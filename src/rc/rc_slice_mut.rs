use core::{
    convert::TryFrom,
    mem,
    ops::{Deref, DerefMut},
    ptr::NonNull,
};
use alloc::{
    boxed::Box,
    rc::Rc,
    vec::Vec,
};

use crate::{
    internal::slice_model::{SliceAlloc, SliceItems},
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
