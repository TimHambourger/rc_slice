use core::{
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
    slice,
};

/// A struct that uniquely owns the items in some subslice of an underlying
/// slice but does not own the allocation for the underlying slice.
#[derive(Debug)]
pub struct SliceItems<T> {
    ptr: NonNull<T>,
    len: usize,
    phantom: PhantomData<T>,
}

impl<T> SliceItems<T> {
    /// Construct a new `SliceItems` instance.
    /// Unsafe for several reasons:
    /// - Calling code must guarantee that `ptr` points to the start of an
    /// allocated object of length `len` (in units of T).
    /// - Calling code MUST take ownership of the allocation for the
    /// underlying slice.
    /// - Calling code MUST guarantee that this struct uniquely owns the
    /// items in the indicated subslice.
    pub unsafe fn new(ptr: NonNull<T>, len: usize) -> Self {
        assert_ne!(0, mem::size_of::<T>(), "TODO: Support ZSTs");
        SliceItems { ptr, len, phantom: PhantomData }
    }

    pub fn into_raw_parts(this: Self) -> (NonNull<T>, usize) {
        let ptr = this.ptr;
        let len = this.len;
        mem::forget(this);
        (ptr, len)
    }

    pub fn split_off_left(&mut self) -> Self {
        let ptr = self.ptr;
        let left_len = self.left_len();
        self.ptr = self.mid();
        self.len = self.right_len();
        unsafe { Self::new(ptr, left_len) }
    }

    pub fn split_off_right(&mut self) -> Self {
        let mid = self.mid();
        let right_len = self.right_len();
        self.len = self.left_len();
        unsafe { Self::new(mid, right_len) }
    }

    fn left_len(&self) -> usize {
        self.len / 2
    }

    fn right_len(&self) -> usize {
        self.len - self.len / 2
    }

    fn mid(&self) -> NonNull<T> {
        // TODO: Support ZSTs
        unsafe { NonNull::new_unchecked(self.ptr.as_ptr().offset((self.len / 2) as isize)) }
    }

    // TODO: split_into_parts
}

impl<T> Drop for SliceItems<T> {
    fn drop(&mut self) {
        // Use ptr::read to drop the items without freeing the underlying allocation.
        // SliceAlloc handles freeing the underlying allocation.
        for i in 0..self.len {
            unsafe { ptr::read(self.ptr.as_ptr().offset(i as isize)); }
        }
    }
}

impl<T> Deref for SliceItems<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
}

impl<T> DerefMut for SliceItems<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
    }
}
