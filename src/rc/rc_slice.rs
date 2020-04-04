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

use crate::{
    internal::slice_model::SliceAlloc,
    rc::RcSliceMut,
};

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
    parent: Weak<Self>,
    guard: RefCell<Weak<DataGuard>>,
    phantom_item: PhantomData<T>,
    phantom_child: PhantomData<Self>,
}

/// Signals the presence of child RcSlices or WeakSlices for the same
/// data subslice. Part of detecting which mutations are possible.
#[derive(Debug)]
struct DataGuard {
    // Not used except in the fact that a child DataGuard keeps its
    // parent DataGuard alive.
    _parent: Option<Rc<Self>>,
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
    // Not used except as part of signaling the presence of WeakSlices to RcSlice::get_mut
    _data_guard: Weak<DataGuard>,
}

impl<T> RcSliceData<T> {
    fn from_boxed_slice(slice: Box<[T]>) -> Self {
        assert_ne!(0, mem::size_of::<T>(), "TODO: Support ZSTs");
        let len = slice.len();
        unsafe {
            // Waiting on stabilization of Box::into_raw_non_null
            let ptr = NonNull::new_unchecked(Box::into_raw(slice) as _);
            let alloc = if len == 0 { None } else { Some(Rc::new(SliceAlloc::new(ptr, len))) };
            Self::from_data_parts(ptr, len, alloc)
        }
    }

    pub (in crate::rc) unsafe fn from_data_parts(ptr: NonNull<T>, len: usize, alloc: Option<Rc<SliceAlloc<T>>>) -> Self {
        Self::with_data_and_parent(ptr, len, alloc, Weak::new())
    }

    fn with_data_and_parent(ptr: NonNull<T>, len: usize, alloc: Option<Rc<SliceAlloc<T>>>, parent: Weak<Self>) -> Self {
        RcSliceData {
            ptr,
            len,
            alloc,
            parent,
            left_child: Cell::new(None),
            right_child: Cell::new(None),
            guard: RefCell::new(Weak::new()),
            phantom_item: PhantomData,
            phantom_child: PhantomData,
        }
    }

    fn clone_left(self: &Rc<Self>) -> Rc<Self> {
        if self.len == 0 {
            self.clone()
        } else {
            let (ptr, len) = self.left_sub();
            unsafe {
                self.clone_child(&self.left_child, ptr, len)
            }
        }
    }

    fn clone_right(self: &Rc<Self>) -> Rc<Self> {
        if self.len <= 1 {
            self.clone()
        } else {
            let (ptr, len) = self.right_sub();
            unsafe {
                self.clone_child(&self.right_child, ptr, len)
            }
        }
    }

    unsafe fn clone_child(self: &Rc<Self>, cell: &Cell<Option<NonNull<()>>>, ptr: NonNull<T>, len: usize) -> Rc<Self> {
        cell.get().map_or_else(
            || {
                let alloc = if len == 0 { None } else { self.alloc.clone() };
                let new = Rc::new(Self::with_data_and_parent(ptr, len, alloc, Rc::downgrade(self)));
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

    /// Convert this RcSliceData into an RcSliceMut. Unsafe b/c calling code
    /// must ensure that there are no strong refs to any other RcSliceData
    /// overlapping this one.
    unsafe fn into_mut(mut self) -> RcSliceMut<T> {
        let slice_mut = RcSliceMut::from_raw_parts(self.ptr, self.len, self.alloc.take());
        // We don't want to drop the items in this subslice when self gets dropped,
        // b/c we've transferred their ownership to slice_mut. But we DO wanna drop
        // things like our strong refs to our child datas, ref cells with the weak
        // refs to our data guards, etc, to avoid leaking all that.
        self.forget_items();
        slice_mut
    }

    fn forget_items(&mut self) {
        // Recursively tell left child to forget its items
        self.take_left().map(|child| Rc::try_unwrap(child).map(|mut child| child.forget_items()));
        // Recursively tell right child to forget its items
        self.take_right().map(|child| Rc::try_unwrap(child).map(|mut child| child.forget_items()));
        // Setting len to 0 turns our Drop impl into a no-op.
        self.len = 0;
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
        let existing_guard = data.guard.borrow().upgrade();
        existing_guard.unwrap_or_else(|| {
            // No reference to a live existing guard. If our parent is still alive,
            // guard IT and use that returned guard as our parent. Otherwise we have
            // no parent guard.
            let parent_guard = data.parent.upgrade()
                .map(|parent_data| Self::guard(&parent_data));
            let guard = Rc::new(DataGuard { _parent: parent_guard });
            // Save a weak ref to the new guard in the passed data instance
            *data.guard.borrow_mut() = Rc::downgrade(&guard);
            guard
        })
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
        // was also another RcSlice around.
        let safe_to_mut =
            // We're the only strong ref to our data_guard. Checks that
            // there are no child RcSlices.
            1 == Rc::strong_count(&this.data_guard) &&
            // We're the only strong ref to our data. Checks that there
            // are no parent RcSlices.
            1 == Rc::strong_count(&this.data) &&
            // Our data holds the only weak ref to our data guard. Checks
            // that there are no WeakSlices pointing to our same data.
            1 == Rc::weak_count(&this.data_guard);
        if safe_to_mut {
            unsafe { Some(slice::from_raw_parts_mut((*this.data).ptr.as_ptr(), (*this.data).len)) }
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
                |data| unsafe { Ok(data.into_mut()) }
            )
        } else {
            Err(this)
        }
    }

    pub fn downgrade(this: &Self) -> WeakSlice<T> {
        WeakSlice { data: Rc::downgrade(&this.data), _data_guard: Rc::downgrade(&this.data_guard) }
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

impl<T> From<RcSliceMut<T>> for RcSlice<T> {
    fn from(slice_mut: RcSliceMut<T>) -> Self {
        RcSliceMut::into_immut(slice_mut)
    }
}

impl<T> WeakSlice<T> {
    /// Constructs a new `WeakSlice<T>`, without allocating any memory.
    /// Calling `upgrade` on the return value always gives `None`.
    pub fn new() -> Self {
        WeakSlice { data: Weak::new(), _data_guard: Weak::new() }
    }

    pub fn upgrade(&self) -> Option<RcSlice<T>> {
        self.data.upgrade().map(RcSlice::from_data)
    }
}

impl<T> Clone for WeakSlice<T> {
    fn clone(&self) -> WeakSlice<T> {
        WeakSlice { data: self.data.clone(), _data_guard: self._data_guard.clone() }
    }
}
