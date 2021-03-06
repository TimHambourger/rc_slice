use core::{
    convert::TryFrom,
    iter::FusedIterator,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};
use alloc::{
    boxed::Box,
    sync::Arc,
    vec::Vec,
};
use crate::{
    internal::slice_model::{
        self,
        SliceAlloc,
        SliceItems,
        SliceItemsIter,
        SliceItemsParts,
    },
    arc::arc_slice::{ArcSlice, ArcSliceData},
};

pub struct ArcSliceMut<T> {
    // Ditto RcSliceMut re this field ordering being significant for drop ordering
    items: SliceItems<T>,
    // An Option b/c we'll let this be None for length zero sublices. They
    // don't need an underlying allocation.
    alloc: Option<Arc<SliceAlloc<T>>>,
}

pub struct ArcSliceMutIter<T> {
    // Ditto RcSliceMut re this field ordering being significant for drop ordering
    iter: SliceItemsIter<T>,
    alloc: Option<Arc<SliceAlloc<T>>>,
}

pub struct ArcSliceMutParts<T> {
    // Ditto RcSliceMut re this field ordering being significant for drop ordering
    iter: SliceItemsParts<T>,
    alloc: Option<Arc<SliceAlloc<T>>>,
}

impl<T> ArcSliceMut<T> {
    pub fn from_boxed_slice(slice: Box<[T]>) -> Self {
        let (items, alloc) = unsafe { slice_model::split_alloc_from_items(slice) };
        Self { items, alloc: alloc.map(Arc::new) }
    }

    pub fn from_vec(vec: Vec<T>) -> Self {
        Self::from_boxed_slice(vec.into_boxed_slice())
    }

    pub(in crate::arc) unsafe fn from_raw_parts(ptr: NonNull<T>, len: usize, alloc: Option<Arc<SliceAlloc<T>>>) -> Self {
        Self { items: SliceItems::new(ptr, len), alloc }
    }

    // NOTE: We limit our splitting API to just split_off_left and split_off_right
    // for the same reasons that we limit RcSliceMut to just split_off_left and
    // split_off_right. See comment in rc_slic_mut.rs for more.

    pub fn split_off_left(this: &mut Self) -> Self {
        let new_items = this.items.split_off_left();
        let alloc = if new_items.len() > 0 { this.alloc.clone() } else { None };
        Self { items: new_items, alloc }
    }

    pub fn split_off_right(this: &mut Self) -> Self {
        let new_items = this.items.split_off_right();
        let alloc = if new_items.len() > 0 { this.alloc.clone() } else { None };
        Self { items: new_items, alloc }
    }

    pub fn split_into_parts(this: Self, num_parts: usize) -> ArcSliceMutParts<T> {
        let ArcSliceMut { items, alloc } = this;
        let iter = items.split_into_parts(num_parts);
        ArcSliceMutParts { iter, alloc }
    }

    pub fn into_immut(this: Self) -> ArcSlice<T> {
        let ArcSliceMut { items, mut alloc } = this;
        let (ptr, len) = SliceItems::into_raw_parts(items);
        let data = unsafe { Arc::new(ArcSliceData::from_data_parts(ptr, len, alloc.take())) };
        ArcSlice::from_data(data)
    }

    // TODO: unsplit
}


impl<T> Deref for ArcSliceMut<T> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &[T] { &self.items }
}

impl<T> DerefMut for ArcSliceMut<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] { &mut self.items }
}

impl<T> From<Box<[T]>> for ArcSliceMut<T> {
    fn from(slice: Box<[T]>) -> Self {
        Self::from_boxed_slice(slice)
    }
}

impl<T> From<Vec<T>> for ArcSliceMut<T> {
    fn from(vec: Vec<T>) -> Self {
        Self::from_vec(vec)
    }
}

impl<T> TryFrom<ArcSlice<T>> for ArcSliceMut<T> {
    type Error = ArcSlice<T>;

    fn try_from(slice: ArcSlice<T>) -> Result<Self, ArcSlice<T>> {
        ArcSlice::into_mut(slice)
    }
}

impl<T: Clone> Clone for ArcSliceMut<T> {
    /// Clone an `ArcSliceMut` by allocating a new vector and cloning items
    /// into it. Unlike the `clone` impl for `ArcSlice`, this does NOT add
    /// a reference to the original underlying slice but instead constructs
    /// a new slice.
    fn clone(&self) -> Self {
        self.iter().cloned().collect()
    }
}

impl<T> IntoIterator for ArcSliceMut<T> {
    type Item = T;
    type IntoIter = ArcSliceMutIter<T>;

    #[inline]
    fn into_iter(self) -> ArcSliceMutIter<T> {
        let ArcSliceMut { items, alloc } = self;
        ArcSliceMutIter { iter: items.into_iter(), alloc }
    }
}

borrow_as_slice!(ArcSliceMut);
borrow_mut_as_slice!(ArcSliceMut);
debug_as_slice!(ArcSliceMut);
compare_as_slice!(ArcSliceMut);
hash_as_slice!(ArcSliceMut);
from_iter_via_vec!(ArcSliceMut);

impl<T> ArcSliceMutIter<T> {
    #[inline]
    pub fn as_slice(&self) -> &[T] { self.iter.as_slice() }
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] { self.iter.as_mut_slice() }

    // NOTE: As w/ RcSliceMutIter, we DO allow arbitrary splits for ArcSliceMutIter.
    // See comment in rc_slice_mut.rs for more.

    pub fn split_off_from(&mut self, at: usize) -> Self {
        let split_iter = self.iter.split_off_from(at);
        let alloc = if self.len() == 0 {
            self.alloc.take()
        } else if split_iter.len() > 0 {
            self.alloc.clone()
        } else {
            None
        };
        Self { iter: split_iter, alloc }
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
        Self { iter: split_iter, alloc }
    }
}

impl<T> ExactSizeIterator for ArcSliceMutIter<T> {
    #[inline]
    fn len(&self) -> usize { self.iter.len() }
}

impl<T> Iterator for ArcSliceMutIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        let item = self.iter.next();
        // Don't need to hold onto SliceAlloc if length is going to zero
        if self.len() == 0 { self.alloc.take(); }
        item
    }

    exact_size_hint!();
    exact_count!();
}

impl<T> DoubleEndedIterator for ArcSliceMutIter<T> {
    fn next_back(&mut self) -> Option<T> {
        let item = self.iter.next_back();
        // Don't need to hold onto SliceAlloc if length is going to zero
        if self.len() == 0 { self.alloc.take(); }
        item
    }
}

impl<T> FusedIterator for ArcSliceMutIter<T> { }

debug_as_items_iter!(ArcSliceMutIter);

impl<T> ArcSliceMutParts<T> {
    #[inline]
    pub fn as_slice(&self) -> &[T] { self.iter.as_slice() }
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] { self.iter.as_mut_slice() }
}

impl<T> ExactSizeIterator for ArcSliceMutParts<T> {
    #[inline]
    fn len(&self) -> usize { self.iter.len() }
}

impl<T> Iterator for ArcSliceMutParts<T> {
    type Item = ArcSliceMut<T>;

    fn next(&mut self) -> Option<ArcSliceMut<T>> {
        self.iter.next().map(|items| {
            let alloc = if self.as_slice().len() == 0 {
                self.alloc.take()
            } else if items.len() > 0 {
                self.alloc.clone()
            } else {
                None
            };
            ArcSliceMut { items, alloc }
        })
    }

    exact_size_hint!();
    exact_count!();
}

impl<T> DoubleEndedIterator for ArcSliceMutParts<T> {
    fn next_back(&mut self) -> Option<ArcSliceMut<T>> {
        self.iter.next_back().map(|items| {
            let alloc = if self.as_slice().len() == 0 {
                self.alloc.take()
            } else if items.len() > 0 {
                self.alloc.clone()
            } else {
                None
            };
            ArcSliceMut { items, alloc }
        })
    }
}

impl<T> FusedIterator for ArcSliceMutParts<T> { }

debug_as_parts_iter!(ArcSliceMutParts);
