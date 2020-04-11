use core::{
    borrow::{Borrow, BorrowMut},
    convert::TryFrom,
    hash::{Hash, Hasher},
    mem,
    cmp::Ordering,
    iter::{FromIterator, FusedIterator},
    ops::{Deref, DerefMut},
    ptr::NonNull,
};
use alloc::{
    boxed::Box,
    rc::Rc,
    vec::Vec,
};

use crate::{
    internal::slice_model::{SliceAlloc, SliceItems, IntoIter as SliceItemsIter},
    rc::rc_slice::{RcSlice, RcSliceData},
};

/// A unique reference to a subslice of a reference counted slice.
#[derive(Debug)]
pub struct RcSliceMut<T> {
    items: SliceItems<T>,
    // An Option b/c we'll let this be None for length zero sublices. They
    // don't need an underlying allocation.
    alloc: Option<Rc<SliceAlloc<T>>>,
}

#[derive(Debug)]
pub struct IntoIter<T> {
    iter: SliceItemsIter<T>,
    alloc: Option<Rc<SliceAlloc<T>>>,
}

impl<T> RcSliceMut<T> {
    pub fn from_boxed_slice(slice: Box<[T]>) -> Self {
        assert_ne!(0, mem::size_of::<T>(), "TODO: Support ZSTs");
        let len = slice.len();
        unsafe {
            // Waiting on stabilization of Box::into_raw_non_null
            let ptr = NonNull::new_unchecked(Box::into_raw(slice) as _);
            let alloc = if len == 0 { None } else { Some(Rc::new(SliceAlloc::new(ptr, len))) };
            Self::from_raw_parts(ptr, len, alloc)
        }
    }

    pub fn from_vec(vec: Vec<T>) -> Self {
        Self::from_boxed_slice(vec.into_boxed_slice())
    }

    pub(in crate::rc) unsafe fn from_raw_parts(ptr: NonNull<T>, len: usize, alloc: Option<Rc<SliceAlloc<T>>>) -> Self {
        RcSliceMut { items: SliceItems::new(ptr, len), alloc }
    }

    pub fn split_off_left(this: &mut Self) -> Self {
        let new_items = this.items.split_off_left();
        RcSliceMut { items: new_items, alloc: this.alloc.clone() }
    }

    pub fn split_off_right(this: &mut Self) -> Self {
        let new_items = this.items.split_off_right();
        RcSliceMut { items: new_items, alloc: this.alloc.clone() }
    }

    pub fn into_immut(this: Self) -> RcSlice<T> {
        let RcSliceMut { items, mut alloc } = this;
        let (ptr, len) = SliceItems::into_raw_parts(items);
        let data = unsafe { Rc::new(RcSliceData::from_data_parts(ptr, len, alloc.take())) };
        RcSlice::from_data(data)
    }

    // TODO: split_into_parts
}

impl<T> Deref for RcSliceMut<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &self.items
    }
}

impl<T> DerefMut for RcSliceMut<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        &mut self.items
    }
}

impl<T> From<Box<[T]>> for RcSliceMut<T> {
    fn from(slice: Box<[T]>) -> Self {
        Self::from_boxed_slice(slice)
    }
}

impl<T> From<Vec<T>> for RcSliceMut<T> {
    fn from(vec: Vec<T>) -> Self {
        Self::from_vec(vec)
    }
}

impl<T> TryFrom<RcSlice<T>> for RcSliceMut<T> {
    type Error = RcSlice<T>;

    fn try_from(slice: RcSlice<T>) -> Result<Self, RcSlice<T>> {
        RcSlice::into_mut(slice)
    }
}

impl<T: Clone> Clone for RcSliceMut<T> {
    /// Clone an `RcSliceMut` by allocating a new vector and cloning items
    /// into it. Unlike the `clone` impl for `RcSlice`, this does NOT add
    /// a reference to the original underlying slice but instead constructs
    /// a new slice.
    fn clone(&self) -> Self {
        self.iter().cloned().collect()
    }
}

impl<T> IntoIterator for RcSliceMut<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    #[inline]
    fn into_iter(self) -> IntoIter<T> {
        let RcSliceMut { items, alloc } = self;
        IntoIter { iter: items.into_iter(), alloc }
    }
}

borrow_as_slice!(RcSliceMut);
borrow_mut_as_slice!(RcSliceMut);
compare_as_slice!(RcSliceMut);
hash_as_slice!(RcSliceMut);
from_iter_via_vec!(RcSliceMut);

impl<T> ExactSizeIterator for IntoIter<T> {
    #[inline]
    fn len(&self) -> usize { self.iter.len() }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        let item = self.iter.next();
        // Don't need to hold onto SliceAlloc if length is going to zero
        if self.len() == 0 { self.alloc.take(); }
        item
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        let item = self.iter.next_back();
        // Don't need to hold onto SliceAlloc if length is going to zero
        if self.len() == 0 { self.alloc.take(); }
        item
    }
}

impl<T> FusedIterator for IntoIter<T> { }
