use core::{
    cell::Cell,
    marker::PhantomData,
    mem,
    ops::Deref,
    ptr::NonNull,
    slice,
};
use alloc::{
    boxed::Box,
    rc::{Rc, Weak},
    vec::Vec,
};

// Relationship btwn RcSlice, RcSliceData, and RcSliceMutGuard:
//
// RcSlice          RcSliceData       RcSliceMutGuard
//
//                s  t  r  o  n  g
//     |-----------------------------------|
//     |      strong             weak      v
//   parent  ------->  parent  <-------  parent
//                      | s                ^ s
//                      | t                | t
//                      | r                | r
//                      | o                | o
//                      | n                | n
//            strong    v g      weak      | g
//    child  ------->  child   <-------  child
//     |                                   ^
//     |-----------------------------------|
//                s  t  r  o  n  g
//
// Idea: Each RcSlice holds a strong ref to its RcSliceData. Parent
// RcSliceDatas hold strong refs to their children RcSliceDatas, so that
// dropping a child RcSlice doesn't cause its RcSliceData to get dropped
// if there's still a parent RcSlice around. Each RcSlice also holds a
// strong ref to an RcSliceMutGuard, which in turn holds a weak ref to
// the RcSliceData and (optionally) a strong ref to its parent
// RcSliceMutGuard. Idea there is you can't get an &mut RcSliceData if
// there are weak refs around, so existence of the child RcSlice
// prevents improperly obtaining an &mut [T] from the parent RcSlice.

#[derive(Debug)]
struct RcSliceData<T> {
    ptr: NonNull<T>,
    len: usize,
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
    parent: Option<Rc<Self>>,
    data: Weak<RcSliceData<T>>,
}

#[derive(Debug, Clone)]
pub struct RcSlice<T> {
    data: Rc<RcSliceData<T>>,
    mut_guard: Rc<RcSliceMutGuard<T>>,
}

impl<T> RcSliceData<T> {
    fn from_boxed_slice(slice: Box<[T]>) -> Self {
        assert_ne!(0, mem::size_of::<T>(), "TODO: Support ZSTs");
        let len = slice.len();
        // Waiting on stabilization of Box::into_raw_non_null
        let ptr = unsafe { NonNull::new_unchecked(Box::into_raw(slice) as _) };
        RcSliceData {
            ptr,
            len,
            left_child: Cell::new(None),
            right_child: Cell::new(None),
            phantom_item: PhantomData,
            phantom_child: PhantomData
        }
    }

    // TODO: add_left_child, add_right_child

    fn get_left_child(&self) -> Option<&Self> {
        Self::get_child(&self.left_child)
    }

    fn get_right_child(&self) -> Option<&Self> {
        Self::get_child(&self.right_child)
    }

    fn get_child(cell: &Cell<Option<NonNull<()>>>) -> Option<&Self> {
        cell.get().map(|ptr| unsafe { &*(ptr.as_ptr() as *const Self) })
    }

    fn take_left_child(&mut self) -> Option<Rc<Self>> {
        Self::take_child(&mut self.left_child)
    }

    fn take_right_child(&mut self) -> Option<Rc<Self>> {
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
        (unsafe { NonNull::new_unchecked(self.ptr.as_ptr().offset((self.len / 2 + 1) as isize)) }, self.len - self.len / 2)
    }
}

impl<T> Drop for RcSliceData<T> {
    fn drop(&mut self) {
        // Move the children out to decrement their strong counts and
        // also to figure out what range of data to free, if any.
        let left_child = self.take_left_child();
        let right_child = self.take_right_child();
        let (ptr, len) = match (left_child, right_child) {
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
        let _ = unsafe { Vec::from_raw_parts(ptr.as_ptr() as _, len, len) };
    }
}

impl<T> Deref for RcSliceData<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
}

impl<T> RcSlice<T> {
    pub fn from_boxed_slice(slice: Box<[T]>) -> Self {
        let data = Rc::new(RcSliceData::from_boxed_slice(slice));
        let mut_guard = Rc::new(RcSliceMutGuard { parent: None, data: Rc::downgrade(&data) });
        RcSlice {
            data,
            mut_guard
        }
    }

    pub fn from_vec(vec: Vec<T>) -> Self {
        Self::from_boxed_slice(vec.into_boxed_slice())
    }

    // TODO: into_boxed_slice, into_vec

    // TODO: clone_left, clone_right, split_off_left, split_off_right

    // TODO: get_mut, make_mut
}

impl<T> Deref for RcSlice<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &**self.data
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
