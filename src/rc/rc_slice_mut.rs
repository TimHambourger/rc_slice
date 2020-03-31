use core::{
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
    slice,
};
use alloc::{
    boxed::Box,
    rc::{Rc, Weak},
    vec::Vec,
};

use crate::{
    rc::rc_slice::{RcSlice, RcSliceData},
    slice_alloc::SliceAlloc
};

/// A unique reference to a subslice of a reference counted slice.
#[derive(Debug)]
pub struct RcSliceMut<T> {
    ptr: NonNull<T>,
    len: usize,
    // An Option b/c we'll let this be None for length zero sublices. They
    // don't need an underlying allocation.
    alloc: Option<Rc<SliceAlloc<T>>>,
    phantom: PhantomData<T>,
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
        RcSliceMut { ptr, len, alloc, phantom: PhantomData }
    }

    pub fn into_immut(mut this: Self) -> RcSlice<T> {
        let data = unsafe { Rc::new(RcSliceData::from_raw_parts(this.ptr, this.len, this.alloc.take(), Weak::new())) };
        RcSlice::from_data(data)
    }

    // TODO: split_off_left
    // TODO: split_off_right
    // TODO: split_into_parts
}

impl<T> Drop for RcSliceMut<T> {
    fn drop(&mut self) {
        // Use ptr::read to drop the items without freeing the underlying allocation.
        // SliceAlloc handles freeing the underlying allocation.
        for i in 0..self.len {
            unsafe { ptr::read(self.ptr.as_ptr().offset(i as isize)); }
        }
    }
}

impl<T> Deref for RcSliceMut<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
}

impl<T> DerefMut for RcSliceMut<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
    }
}
