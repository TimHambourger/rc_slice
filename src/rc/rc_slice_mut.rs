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
    internal::slice_model::{SliceAlloc, SliceItems, SliceItemsIter},
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
pub struct RcSliceMutIter<T> {
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

    // NOTE: We limit our splitting API to just split_off_left and split_off_right
    // instead of arbitrary split points for maximum convertability btwn RcSliceMut
    // and RcSlice. If RcSliceMut allowed arbitrary split points, we could introduce
    // unsoundness via a series of calls like
    //   - Split an RcSliceMut at a point other than the midpoint.
    //   - Convert each resulting sub-RcSliceMut into an RcSlice via
    //     RcSliceMut::into_immut.
    //   - Clone each resulting RcSlice.
    //   - Join the cloned RcSlices via RcSlice::unsplit (not yet implemented).
    //   - Split the joined RcSlice via RcSlice::split_off_left.
    // Now you've got RcSlices that overlap each other w/o one being a child of
    // the other, which our RcSlice internals don't currently support.
    // Of course, there are other API restrictions we could make to fix the above
    // (e.g. restrict RcSlice::unsplit to slices that could have resulted from a
    // split at a midpoint). But restricting RcSliceMut to splits at midpoints
    // seems like the most intuitive option so long as RcSlice has the same
    // restriction.

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
    // TODO: unsplit
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
    type IntoIter = RcSliceMutIter<T>;

    #[inline]
    fn into_iter(self) -> RcSliceMutIter<T> {
        let RcSliceMut { items, alloc } = self;
        RcSliceMutIter { iter: items.into_iter(), alloc }
    }
}

borrow_as_slice!(RcSliceMut);
borrow_mut_as_slice!(RcSliceMut);
compare_as_slice!(RcSliceMut);
hash_as_slice!(RcSliceMut);
from_iter_via_vec!(RcSliceMut);

impl<T> RcSliceMutIter<T> {
    pub fn as_slice(&self) -> &[T] {
        self.iter.as_slice()
    }

    pub fn as_slice_mut(&mut self) -> &mut [T] {
        self.iter.as_slice_mut()
    }

    // NOTE: Unlike RcSliceMut, we DO support splits at arbitrary points for
    // RcSliceMutIter. That's b/c we have no plans for allowing conversions from
    // an RcSliceMutIter back to an RcSliceMut or RcSlice. Since you can remove
    // items from an RcSliceMutIter one at a time, such conversions would already
    // be unsound for the reasons given above.

    pub fn split_off_from(&mut self, at: usize) -> Self {
        let split_iter = self.iter.split_off_from(at);
        let alloc = if self.len() == 0 {
            self.alloc.take()
        } else if split_iter.len() > 0 {
            self.alloc.clone()
        } else {
            None
        };
        RcSliceMutIter { iter: split_iter, alloc }
    }

    pub fn split_off_to(&mut self, at: usize) -> Self {
        let split_iter = self.iter.split_off_to(at);
        let alloc = if self.len() == 0 {
            self.alloc.take()
        } else if split_iter.len() > 0 {
            self.alloc.clone()
        } else {
            None
        };
        RcSliceMutIter { iter: split_iter, alloc }
    }
}

impl<T> ExactSizeIterator for RcSliceMutIter<T> {
    #[inline]
    fn len(&self) -> usize { self.iter.len() }
}

impl<T> Iterator for RcSliceMutIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        let item = self.iter.next();
        // Don't need to hold onto SliceAlloc if length is going to zero
        if self.len() == 0 { self.alloc.take(); }
        item
    }
}

impl<T> DoubleEndedIterator for RcSliceMutIter<T> {
    fn next_back(&mut self) -> Option<T> {
        let item = self.iter.next_back();
        // Don't need to hold onto SliceAlloc if length is going to zero
        if self.len() == 0 { self.alloc.take(); }
        item
    }
}

impl<T> FusedIterator for RcSliceMutIter<T> { }
