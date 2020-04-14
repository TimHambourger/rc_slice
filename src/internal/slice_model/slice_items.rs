use core::{
    iter::FusedIterator,
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

#[derive(Debug)]
pub struct SliceItemsIter<T> {
    start: NonNull<T>,
    end: NonNull<T>,
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
        self.len >> 1
    }

    fn right_len(&self) -> usize {
        self.len - (self.len >> 1)
    }

    fn mid(&self) -> NonNull<T> {
        // TODO: Support ZSTs
        unsafe { NonNull::new_unchecked(self.ptr.as_ptr().offset((self.len >> 1) as isize)) }
    }

    // TODO: split_into_parts
}

impl<T> Drop for SliceItems<T> {
    fn drop(&mut self) {
        // Use [T]'s drop impl to drop the items without freeing the underlying allocation.
        // SliceAlloc handles freeing the underlying allocation.
        // The idea of using drop_in_place was taken straight from the drop impl for Vec<T>.
        // See https://doc.rust-lang.org/src/alloc/vec.rs.html
        unsafe { ptr::drop_in_place(&mut **self) }
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

impl<T> IntoIterator for SliceItems<T> {
    type Item = T;
    type IntoIter = SliceItemsIter<T>;

    #[inline]
    fn into_iter(self) -> SliceItemsIter<T> { SliceItemsIter::new(self) }
}

impl<T> SliceItemsIter<T> {
    fn new(slice_items: SliceItems<T>) -> Self {
        // TODO: support ZSTs
        let start = slice_items.ptr;
        let end = unsafe { NonNull::new_unchecked(start.as_ptr().offset(slice_items.len as isize)) };
        mem::forget(slice_items);
        SliceItemsIter { start, end, phantom: PhantomData }
    }

    pub fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.start.as_ptr(), self.len()) }
    }

    pub fn as_slice_mut(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.start.as_ptr(), self.len()) }
    }

    pub fn split_off_from(&mut self, at: usize) -> Self {
        assert!(at <= self.len(), "{} <= {}", at, self.len());
        let split_pt = unsafe { NonNull::new_unchecked(self.start.as_ptr().offset(at as isize)) };
        let split = SliceItemsIter { start: split_pt, end: self.end, phantom: PhantomData };
        self.end = split_pt;
        split
    }

    pub fn split_off_to(&mut self, at: usize) -> Self {
        assert!(at <= self.len(), "{} <= {}", at, self.len());
        let split_pt = unsafe { NonNull::new_unchecked(self.start.as_ptr().offset(at as isize)) };
        let split = SliceItemsIter { start: self.start, end: split_pt, phantom: PhantomData };
        self.start = split_pt;
        split
    }
}

impl<T> ExactSizeIterator for SliceItemsIter<T> {
    #[inline]
    fn len(&self) -> usize {
        // TODO: support ZSTs
        (self.end.as_ptr() as usize - self.start.as_ptr() as usize) / mem::size_of::<T>()
    }
}

impl<T> Iterator for SliceItemsIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.len() > 0 {
            unsafe {
                let read = ptr::read(self.start.as_ptr());
                self.start = NonNull::new_unchecked(self.start.as_ptr().offset(1));
                Some(read)
            }
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<T> DoubleEndedIterator for SliceItemsIter<T> {
    fn next_back(&mut self) -> Option<T> {
        if self.len() > 0 {
            unsafe {
                self.end = NonNull::new_unchecked(self.end.as_ptr().offset(-1));
                Some(ptr::read(self.end.as_ptr()))
            }
        } else {
            None
        }
    }
}

impl<T> FusedIterator for SliceItemsIter<T> { }

impl<T> Drop for SliceItemsIter<T> {
    fn drop(&mut self) {
        // As for SliceItems, use [T]'s drop impl
        unsafe { ptr::drop_in_place(slice::from_raw_parts_mut(self.start.as_ptr(), self.len())) }
    }
}
