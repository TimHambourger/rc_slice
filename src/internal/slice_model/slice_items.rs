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

#[derive(Debug)]
pub struct SliceItemsParts<T> {
    orig_ptr: NonNull<T>,
    orig_len: usize,
    num_parts: usize,
    num_yielded_front: usize,
    num_yielded_back: usize,
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
        Self { ptr, len, phantom: PhantomData }
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

    pub fn split_into_parts(self, num_parts: usize) -> SliceItemsParts<T> {
        SliceItemsParts::new(self, num_parts)
    }
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

// For concurrency purposes, SliceItems<T> acts like Vec<T> or Box<[T]>.
unsafe impl<T: Send> Send for SliceItems<T> { }
unsafe impl<T: Sync> Sync for SliceItems<T> { }

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
        Self { start, end, phantom: PhantomData }
    }

    pub fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.start.as_ptr(), self.len()) }
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.start.as_ptr(), self.len()) }
    }

    pub fn split_off_from(&mut self, at: usize) -> Self {
        assert!(at <= self.len(), "at <= self.len(): {} <= {}", at, self.len());
        let split_pt = unsafe { NonNull::new_unchecked(self.start.as_ptr().offset(at as isize)) };
        let split = Self { start: split_pt, end: self.end, phantom: PhantomData };
        self.end = split_pt;
        split
    }

    pub fn split_off_to(&mut self, at: usize) -> Self {
        assert!(at <= self.len(), "at <= self.len(): {} <= {}", at, self.len());
        let split_pt = unsafe { NonNull::new_unchecked(self.start.as_ptr().offset(at as isize)) };
        let split = Self { start: self.start, end: split_pt, phantom: PhantomData };
        self.start = split_pt;
        split
    }
}

// SliceItemsIter<T> acts like SliceItems<T> for concurrency purposes (or
// maybe a better comparison is vec's IntoIter).
unsafe impl<T: Send> Send for SliceItemsIter<T> { }
unsafe impl<T: Sync> Sync for SliceItemsIter<T> { }

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

    exact_size_hint!();
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
        unsafe { ptr::drop_in_place(self.as_mut_slice()); }
    }
}

impl<T> SliceItemsParts<T> {
    fn new(slice_items: SliceItems<T>, num_parts: usize) -> Self {
        assert_ne!(0, num_parts, "num_parts > 0");
        let mut n = num_parts;
        while n & 1 == 0 { n >>= 1; }
        assert_eq!(1, n, "num_parts {} is a power of 2", num_parts);
        let orig_ptr = slice_items.ptr;
        let orig_len = slice_items.len;
        mem::forget(slice_items);
        Self {
            orig_ptr,
            orig_len,
            num_parts,
            num_yielded_front: 0,
            num_yielded_back: 0,
            phantom: PhantomData,
        }
    }

    pub fn as_slice(&self) -> &[T] {
        let (data, len) = self.as_raw_slice_parts();
        unsafe { slice::from_raw_parts(data, len) }
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        let (data, len) = self.as_raw_slice_parts();
        unsafe { slice::from_raw_parts_mut(data, len) }
    }

    fn as_raw_slice_parts(&self) -> (*mut T, usize) {
        if self.len() > 0 {
            // TODO: Support ZSTs
            let mut start = self.orig_ptr.as_ptr();
            let mut end = unsafe { start.offset(self.orig_len as isize) };

            // Refine start based on num_yielded_front
            let mut len = self.orig_len;
            let mut mask = self.num_parts >> 1;
            while mask > 0 {
                if self.num_yielded_front & mask == 0 {
                    len = len >> 1;
                } else {
                    start = unsafe { start.offset((len >> 1) as isize) };
                    len = len - (len >> 1);
                }
                mask >>= 1;
            }

            // Refine end based on num_yielded_back
            len = self.orig_len;
            mask = self.num_parts >> 1;
            while mask > 0 {
                if self.num_yielded_back & mask == 0 {
                    len = len - (len >> 1);
                } else {
                    end = unsafe { end.offset(-((len - (len >> 1)) as isize)) };
                    len = len >> 1;
                }
                mask >>= 1;
            }

            let len = (end as usize - start as usize) / mem::size_of::<T>();
            (start, len)
        } else {
            (NonNull::dangling().as_ptr(), 0)
        }
    }
}

// SliceItemsParts<T> acts like SliceItems<T> for concurrency purposes (or
// maybe a better comparison is vec's IntoIter).
unsafe impl<T: Send> Send for SliceItemsParts<T> { }
unsafe impl<T: Sync> Sync for SliceItemsParts<T> { }

impl<T> ExactSizeIterator for SliceItemsParts<T> {
    #[inline]
    fn len(&self) -> usize {
        self.num_parts - self.num_yielded_front - self.num_yielded_back
    }
}

impl<T> Iterator for SliceItemsParts<T> {
    type Item = SliceItems<T>;

    fn next(&mut self) -> Option<SliceItems<T>> {
        if 0 == self.len() {
            None
        } else {
            let mut ptr = self.orig_ptr.as_ptr();
            let mut len = self.orig_len;
            let mut mask = self.num_parts >> 1;
            while mask > 0 {
                if self.num_yielded_front & mask == 0 {
                    len = len >> 1;
                } else {
                    // TODO: Support ZSTs
                    ptr = unsafe { ptr.offset((len >> 1) as isize) };
                    len = len - (len >> 1);
                }
                mask >>= 1;
            }
            let ptr = unsafe { NonNull::new_unchecked(ptr) };
            self.num_yielded_front += 1;
            Some(SliceItems { ptr, len, phantom: PhantomData })
        }
    }

    exact_size_hint!();
}

impl<T> DoubleEndedIterator for SliceItemsParts<T> {
    fn next_back(&mut self) -> Option<SliceItems<T>> {
        // The exact mirror image of next(...).
        if 0 == self.len() {
            None
        } else {
            let mut ptr = self.orig_ptr.as_ptr();
            let mut len = self.orig_len;
            let mut mask = self.num_parts >> 1;
            while mask > 0 {
                // Note that the two branches of this conditional are reversed compared to next(...).
                if self.num_yielded_back & mask == 0 {
                    // TODO: Support ZSTs
                    ptr = unsafe { ptr.offset((len >> 1) as isize) };
                    len = len - (len >> 1);
                } else {
                    len = len >> 1;
                }
                mask >>= 1;
            }
            let ptr = unsafe { NonNull::new_unchecked(ptr) };
            self.num_yielded_back += 1;
            Some(SliceItems { ptr, len, phantom: PhantomData })
        }
    }
}

impl<T> FusedIterator for SliceItemsParts<T> { }

impl<T> Drop for SliceItemsParts<T> {
    fn drop(&mut self) {
        unsafe { ptr::drop_in_place(self.as_mut_slice()); }
    }
}
