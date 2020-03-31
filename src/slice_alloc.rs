use core::ptr::NonNull;
use alloc::vec::Vec;

/// A struct that owns the underlying allocation for a slice but owns
/// none of the items in the slice.
#[derive(Debug)]
pub struct SliceAlloc<T> {
    ptr: NonNull<T>,
    len: usize,
}

impl<T> SliceAlloc<T> {
    /// Construct a new `SliceAlloc` instance.
    /// Unsafe for several reasons:
    /// - Calling code must guarantee that `ptr` points to the start of an
    /// allocated object of length `len` (in units of T).
    /// - Calling code MUST take ownership of the items in the indicated
    /// slice and handle dropping those items as needed.
    /// - Calling code MUST NOT attempt to free the underlying allocation
    /// on its own. SliceAlloc takes that responsibility.
    pub unsafe fn new(ptr: NonNull<T>, len: usize) -> Self {
        SliceAlloc { ptr, len }
    }
}

impl<T> Drop for SliceAlloc<T> {
    /// Drop this SliceAlloc. This frees the underlying allocation but
    /// does not drop any instances of T.
    fn drop(&mut self) {
        unsafe { Vec::from_raw_parts(self.ptr.as_ptr(), 0, self.len); }
    }
}