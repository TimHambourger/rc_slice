use core::{
    cell::Cell,
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

// Relationship btwn RcSlice, RcSliceData, and RcSliceMutGuard:
//
// RcSlice          RcSliceData       RcSliceMutGuard
//
//                s  t  r  o  n  g
//     |-----------------------------------|
//     |      strong                       v
//   parent  ------->  parent <---|      parent
//                      | s       |        ^ s
//                      | t       |w       | t
//                      | r       |e       | r
//                      | o       |a       | o
//                      | n       |k       | n
//            strong    v g       |        | g
//    child  ------->  child      |----- child
//     |                                   ^
//     |-----------------------------------|
//                s  t  r  o  n  g
//
// Idea: Each RcSlice holds a strong ref to its RcSliceData. Parent
// RcSliceDatas hold strong refs to their children RcSliceDatas, so that
// dropping a child RcSlice doesn't cause its RcSliceData to get dropped
// if there's still a parent RcSlice around. Each RcSlice also holds an
// optional strong ref to an RcSliceMutGuards, which in turn holds a weak
// ref to the parent RcSliceData and an optional strong ref to its parent
// RcSliceMutGuard. Idea there is you can't get an &mut RcSliceData if
// there are weak refs around, so existence of the child RcSlice
// prevents improperly obtaining an &mut [T] from the parent RcSlice.

#[derive(Debug)]
struct RcSliceData<T> {
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
    phantom_item: PhantomData<T>,
    phantom_child: PhantomData<Self>,
}

#[derive(Debug)]
struct RcSliceMutGuard<T> {
    parent_data: Weak<RcSliceData<T>>,
    parent: Option<Rc<Self>>,
}

#[derive(Debug)]
pub struct RcSlice<T> {
    data: Rc<RcSliceData<T>>,
    mut_guard: Option<Rc<RcSliceMutGuard<T>>>,
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

    unsafe fn from_raw_parts(ptr: NonNull<T>, len: usize, alloc: Option<Rc<SliceAlloc<T>>>) -> Self {
        RcSliceData {
            ptr,
            len,
            alloc,
            left_child: Cell::new(None),
            right_child: Cell::new(None),
            phantom_item: PhantomData,
            phantom_child: PhantomData
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
                let new = Rc::new(Self::from_raw_parts(ptr, len, alloc));
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

impl<T> RcSliceMutGuard<T> {
    fn new(parent_slice: &RcSlice<T>) -> Self {
        RcSliceMutGuard {
            parent_data: Rc::downgrade(&parent_slice.data),
            parent: parent_slice.mut_guard.clone(),
        }
    }
}

impl<T> RcSlice<T> {
    pub fn from_boxed_slice(slice: Box<[T]>) -> Self {
        let data = Rc::new(RcSliceData::from_boxed_slice(slice));
        RcSlice { data, mut_guard: None }
    }

    pub fn from_vec(vec: Vec<T>) -> Self {
        Self::from_boxed_slice(vec.into_boxed_slice())
    }

    pub fn clone_left(this: &Self) -> Self {
        let data = this.data.clone_left();
        let mut_guard = Some(Rc::new(RcSliceMutGuard::new(&this)));
        RcSlice { data, mut_guard }
    }

    pub fn clone_right(this: &Self) -> Self {
        let data = this.data.clone_right();
        let mut_guard = Some(Rc::new(RcSliceMutGuard::new(&this)));
        RcSlice { data, mut_guard }
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
        // Our system of strong and weak references guarantees that if we
        // can get a mutable reference into our data, then there are no
        // outstanding references to any slices overlapping this one.
        // (Our binary tree structure guarantees that the only kinds of
        // overlaps are "is contained in" and "contains".) So if we can
        // get a mutable reference into our data, then it's safe to call
        // slice::from_raw_parts_mut. See the longish comment at the top
        // of this file for more.
        match Rc::get_mut(&mut this.data) {
            Some(RcSliceData { ptr, len, ..}) => Some(unsafe { slice::from_raw_parts_mut(ptr.as_ptr(), *len) }),
            None => None
        }
    }

    // TODO: make_mut
    // TODO: into_mut
    // TODO: into_boxed_slice, into_vec
    // TODO: downgrade
    // TODO: split_into_parts
    // TODO: clone_parts
}

impl<T> Clone for RcSlice<T> {
    fn clone(&self) -> Self {
        RcSlice {
            data: self.data.clone(),
            mut_guard: self.mut_guard.clone(),
        }
    }
}

impl<T> Deref for RcSlice<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &*self.data
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
