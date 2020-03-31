use core::{
    cell::{Cell, RefCell},
    marker::PhantomData,
    mem,
    ops::Deref,
    ptr::{self, NonNull},
    slice,
};
use alloc::{
    boxed::Box,
    rc::{Rc, Weak},
    vec::Vec,
};

use crate::slice_alloc::SliceAlloc;
use crate::rc::RcSliceMut;

// TODO: Update this comment...
// Relationship btwn RcSlice, RcSliceData, and DataGuard:
//
// RcSlice          RcSliceData         DataGuard
//
//                 s  t  r  o  n  g
//     |------------------------------------|
//     |      strong              weak      v
//   parent  ------->   parent  ------->  parent
//                     s | ^                ^ s
//                     t | | w              | t
//                     r | | e              | r
//                     o | | a              | o
//                     n | | k              | n
//            strong   g v |      weak      | g
//    child  ------->   child   ------->  child
//     |                                    ^
//     |------------------------------------|
//                 s  t  r  o  n  g
//
// Idea: Each RcSlice holds a strong ref to its RcSliceData. Parent
// RcSliceDatas hold strong refs to their children RcSliceDatas, so that
// dropping a child RcSlice doesn't cause its RcSliceData to get dropped
// if there's still a parent RcSlice around. Each RcSlice also holds a
// strong ref to a DataGuard, which in turn holds an optional strong ref
// to its parent DataGuard. Idea there is an RcSlice can check whether it
// holds the only strong ref to its RcSliceData as a way of checking
// whether that data has any still-living ancestors, and it can check
// whether it holds the only strong ref to its DataGuard as a way of
// checking whether its data has any still-living descendants.

#[derive(Debug)]
pub (in crate::rc) struct RcSliceData<T> {
    ptr: NonNull<T>,
    len: usize,
    // An Option b/c we'll let this be None for length zero sublices. They
    // don't need an underlying allocation.
    alloc: Option<Rc<SliceAlloc<T>>>,
    // Really Cell<Option<NonNull<Self>>> where the pointer is obtained via
    // Rc<Self>::into_raw(). But we need RcSliceData<T> to be covariant
    // in T.
    left_child: Cell<Option<NonNull<()>>>,
    // Ditto left_child on really Cell<Option<NonNull<Self>>>
    right_child: Cell<Option<NonNull<()>>>,
    guard: Rc<GuardTether>,
    phantom_item: PhantomData<T>,
    phantom_child: PhantomData<Self>,
}

/// Signals the presence of child RcSlices, thus allowing us to tell whether
/// it's safe to mutate the parent RcSliceData.
#[derive(Debug)]
struct DataGuard {
    parent: Option<Rc<Self>>,
}

/// Loosely tethers an RcSliceData to a DataGuard so that it's possible to
/// reconstruct a DataGuard from an RcSliceData.
#[derive(Debug)]
struct GuardTether {
    parent: Weak<Self>,
    guard: RefCell<Weak<DataGuard>>,
}

/// A reference counted slice that tracks reference counts per
/// subslice.
#[derive(Debug)]
pub struct RcSlice<T> {
    data: Rc<RcSliceData<T>>,
    data_guard: Rc<DataGuard>,
}

#[derive(Debug)]
pub struct WeakSlice<T> {
    data: Weak<RcSliceData<T>>,
}

impl<T> RcSliceData<T> {
    fn from_boxed_slice(slice: Box<[T]>) -> Self {
        assert_ne!(0, mem::size_of::<T>(), "TODO: Support ZSTs");
        let len = slice.len();
        unsafe {
            // Waiting on stabilization of Box::into_raw_non_null
            let ptr = NonNull::new_unchecked(Box::into_raw(slice) as _);
            let alloc = if len == 0 { None } else { Some(Rc::new(SliceAlloc::new(ptr, len))) };
            Self::from_raw_parts(ptr, len, alloc)
        }
    }

    pub (in crate::rc) unsafe fn from_raw_parts(ptr: NonNull<T>, len: usize, alloc: Option<Rc<SliceAlloc<T>>>) -> Self {
        Self::from_rawer_parts(ptr, len, alloc, GuardTether::new(Weak::new()))
    }

    fn from_rawer_parts(ptr: NonNull<T>, len: usize, alloc: Option<Rc<SliceAlloc<T>>>, guard: GuardTether) -> Self {
        RcSliceData {
            ptr,
            len,
            alloc,
            left_child: Cell::new(None),
            right_child: Cell::new(None),
            guard: Rc::new(guard),
            phantom_item: PhantomData,
            phantom_child: PhantomData,
        }
    }

    fn clone_left(&self) -> Rc<Self> {
        let (ptr, len) = self.left_sub();
        unsafe {
            self.clone_child(&self.left_child, ptr, len)
        }
    }

    fn clone_right(&self) -> Rc<Self> {
        let (ptr, len) = self.right_sub();
        unsafe {
            self.clone_child(&self.right_child, ptr, len)
        }
    }

    unsafe fn clone_child(&self, cell: &Cell<Option<NonNull<()>>>, ptr: NonNull<T>, len: usize) -> Rc<Self> {
        cell.get().map_or_else(
            || {
                let alloc = if len == 0 { None } else { self.alloc.clone() };
                let new = Rc::new(Self::from_rawer_parts(ptr, len, alloc, GuardTether::new(Rc::downgrade(&self.guard))));
                let clone = new.clone();
                cell.set(Some(NonNull::new_unchecked(Rc::into_raw(new) as _)));
                clone
            },
            |ptr| {
                let existing = Rc::from_raw(ptr.as_ptr() as *const Self);
                let clone = existing.clone();
                mem::forget(existing);
                clone
            }
        )
    }

    fn take_left(&mut self) -> Option<Rc<Self>> {
        Self::take_child(&mut self.left_child)
    }

    fn take_right(&mut self) -> Option<Rc<Self>> {
        Self::take_child(&mut self.right_child)
    }

    fn take_child(cell: &mut Cell<Option<NonNull<()>>>) -> Option<Rc<Self>> {
        cell.get_mut().take().map(|ptr| unsafe { Rc::from_raw(ptr.as_ptr() as *const Self) })
    }

    fn left_sub(&self) -> (NonNull<T>, usize) {
        (self.ptr, self.len / 2)
    }

    fn right_sub(&self) -> (NonNull<T>, usize) {
        // TODO: Support ZSTs
        (unsafe { NonNull::new_unchecked(self.ptr.as_ptr().offset((self.len / 2) as isize)) }, self.len - self.len / 2)
    }
}

impl<T> Drop for RcSliceData<T> {
    fn drop(&mut self) {
        // Move the children out to decrement their strong counts and
        // also to figure out what range of items to drop, if any.
        let left = self.take_left();
        let right = self.take_right();
        let (p, len) = match (left, right) {
            (None, None) => (self.ptr, self.len),
            (Some(_), None) => {
                // left child is present. Just drop right subslice
                self.right_sub()
            },
            (None, Some(_)) => {
                // right child is present. Just drop left subslice
                self.left_sub()
            },
            _ => return // Both children are present. Nothing more to do.
        };
        // Use ptr::read to drop the items without freeing the underlying allocation.
        // SliceAlloc handles freeing the underlying allocation.
        for i in 0..len {
            unsafe { ptr::read(p.as_ptr().offset(i as isize)); }
        }
    }
}

impl<T> Deref for RcSliceData<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
}

impl DataGuard {
    fn guard<T>(data: &RcSliceData<T>) -> Rc<Self> {
        Self::from_guard_tether(&data.guard)
    }

    fn from_guard_tether(tether: &GuardTether) -> Rc<Self> {
        let existing_guard = tether.guard.borrow().upgrade();
        existing_guard.unwrap_or_else(|| {
            // No reference to a live existing guard. If our parent is still alive,
            // guard IT and use that returned guard as our parent. Otherwise we have
            // no parent guard.
            let parent_guard = tether.parent.upgrade()
                .map(|parent_tether| Self::from_guard_tether(&parent_tether));
            let guard = Rc::new(DataGuard { parent: parent_guard });
            // Save a weak ref to the new guard in the passed data instance
            *tether.guard.borrow_mut() = Rc::downgrade(&guard);
            guard
        })
    }
}

impl GuardTether {
    fn new(parent: Weak<Self>) -> Self {
        GuardTether { parent, guard: RefCell::new(Weak::new()) }
    }
}

impl<T> RcSlice<T> {
    pub (in crate::rc) fn from_data(data: Rc<RcSliceData<T>>) -> Self {
        let data_guard = DataGuard::guard(&data);
        RcSlice { data, data_guard }
    }

    pub fn from_boxed_slice(slice: Box<[T]>) -> Self {
        Self::from_data(Rc::new(RcSliceData::from_boxed_slice(slice)))
    }

    pub fn from_vec(vec: Vec<T>) -> Self {
        Self::from_boxed_slice(vec.into_boxed_slice())
    }

    pub fn clone_left(this: &Self) -> Self {
        Self::from_data(this.data.clone_left())
    }

    pub fn clone_right(this: &Self) -> Self {
        Self::from_data(this.data.clone_right())
    }

    pub fn split_off_left(this: &mut Self) -> Self {
        let left = Self::clone_left(this);
        let right = Self::clone_right(this);
        *this = right;
        left
    }

    pub fn split_off_right(this: &mut Self) -> Self {
        let left = Self::clone_left(this);
        let right = Self::clone_right(this);
        *this = left;
        right
    }

    pub fn get_mut(this: &mut Self) -> Option<&mut [T]> {
        // We need to check for any RcSlices referencing ancestor or
        // descendant RcSliceDatas, and we need to check for any RcSlices
        // or WeakSlices referencing our own RcSliceData. We DON'T need to
        // check for WeakSlices referencing ancestor or descendant
        // RcSliceDatas: We hold no strong ref to any RcSliceData but our
        // own, so the only way any WeakSlice could still hold an active
        // reference to one of those other RcSliceDatas would be if there
        // was also another RcSlice around. So, to put it all together, we
        // just need to do two checks: Make sure we're the only strong or
        // weak ref to our RcSliceData, which also accomplishes the check
        // on ancestor RcSliceDatas, and make sure we're the only strong
        // ref to our DataGuard, which also accomplishes the check on
        // descendant RcSliceDatas.
        if 1 == Rc::strong_count(&this.data_guard) {
            // Ack! Now the weak refs from child RcSliceDatas are screwing this up.
            Rc::get_mut(&mut this.data).map(|RcSliceData { ptr, len, .. }| unsafe {
                slice::from_raw_parts_mut(ptr.as_ptr(), *len)
            })
        } else {
            None
        }
    }

    pub fn into_mut(this: Self) -> Result<RcSliceMut<T>, Self> {
        // Similar to get_mut. But now we don't care about WeakSlices
        // referencing our own RcSliceData: As long as we're the only strong
        // ref to that RcSliceData, the act of converting that RcSliceData into
        // an RcSliceMut will invalidate those WeakSlices. This is the
        // same reason Rc::try_unwrap only cares about strong refs.
        if 1 == Rc::strong_count(&this.data_guard) {
            let RcSlice { data, data_guard } = this;
            Rc::try_unwrap(data).map_or_else(
                |data| {
                    // Error unwrapping data. Reconstruct our RcSlice
                    Err(RcSlice { data, data_guard })
                },
                |mut data| unsafe {
                    Ok(RcSliceMut::from_raw_parts(data.ptr, data.len, data.alloc.take()))
                }
            )
        } else {
            Err(this)
        }
    }

    pub fn downgrade(this: &Self) -> WeakSlice<T> {
        WeakSlice { data: Rc::downgrade(&this.data) }
    }

    // TODO: make_mut
    // TODO: into_boxed_slice, into_vec
    // TODO: split_into_parts
    // TODO: clone_parts
}

impl<T> Clone for RcSlice<T> {
    fn clone(&self) -> Self {
        RcSlice {
            data: self.data.clone(),
            data_guard: self.data_guard.clone(),
        }
    }
}

impl<T> Deref for RcSlice<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &self.data
    }
}

impl<T> From<Box<[T]>> for RcSlice<T> {
    fn from(slice: Box<[T]>) -> Self {
        Self::from_boxed_slice(slice)
    }
}

impl<T> From<Vec<T>> for RcSlice<T> {
    fn from(vec: Vec<T>) -> Self {
        Self::from_vec(vec)
    }
}

impl<T> WeakSlice<T> {
    /// Constructs a new `WeakSlice<T>`, without allocating any memory.
    /// Calling `upgrade` on the return value always gives `None`.
    pub fn new() -> Self {
        WeakSlice { data: Weak::new() }
    }

    pub fn upgrade(&self) -> Option<RcSlice<T>> {
        self.data.upgrade().map(RcSlice::from_data)
    }
}

impl<T> Clone for WeakSlice<T> {
    fn clone(&self) -> WeakSlice<T> {
        WeakSlice { data: self.data.clone() }
    }
}
