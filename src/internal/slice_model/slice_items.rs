use core::{
    iter::FusedIterator,
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
    slice,
};
use zst_utils::PtrOrIdxRange;

/// A struct that uniquely owns the items in some subslice of an underlying
/// slice but does not own the allocation for the underlying slice.
pub struct SliceItems<T> {
    ptr: NonNull<T>,
    len: usize,
    phantom: PhantomData<T>,
}

pub struct SliceItemsIter<T> {
    range: PtrOrIdxRange<T>,
    phantom: PhantomData<T>,
}

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
        if mem::size_of::<T>() == 0 {
            self.ptr
        } else {
            unsafe { NonNull::new_unchecked(self.ptr.as_ptr().add(self.len >> 1)) }
        }
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
        let range = unsafe { PtrOrIdxRange::with_ptr_and_len(slice_items.ptr, slice_items.len) };
        mem::forget(slice_items);
        Self { range, phantom: PhantomData }
    }

    pub fn as_slice(&self) -> &[T] {
        unsafe { self.range.as_slice() }
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        unsafe { self.range.as_mut_slice() }
    }

    pub fn split_off_from(&mut self, at: usize) -> Self {
        assert!(at <= self.len(), "at <= self.len(): {} <= {}", at, self.len());
        let split_pt = unsafe { self.range.start.add(at) };
        let split = Self {
            range: PtrOrIdxRange { start: split_pt, end: self.range.end },
            phantom: PhantomData,
        };
        self.range.end = split_pt;
        split
    }

    pub fn split_off_to(&mut self, at: usize) -> Self {
        assert!(at <= self.len(), "at <= self.len(): {} <= {}", at, self.len());
        let split_pt = unsafe { self.range.start.add(at) };
        let split = Self {
            range: PtrOrIdxRange { start: self.range.start, end: split_pt },
            phantom: PhantomData,
        };
        self.range.start = split_pt;
        split
    }
}

// SliceItemsIter<T> acts like SliceItems<T> for concurrency purposes (or
// maybe a better comparison is vec's IntoIter).
unsafe impl<T: Send> Send for SliceItemsIter<T> { }
unsafe impl<T: Sync> Sync for SliceItemsIter<T> { }

impl<T> ExactSizeIterator for SliceItemsIter<T> {
    #[inline]
    fn len(&self) -> usize { self.range.len() }
}

impl<T> Iterator for SliceItemsIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.len() > 0 {
            unsafe {
                let read = self.range.start.read();
                self.range.start = self.range.start.add(1);
                Some(read)
            }
        } else {
            None
        }
    }

    exact_size_hint!();
    exact_count!();
}

impl<T> DoubleEndedIterator for SliceItemsIter<T> {
    fn next_back(&mut self) -> Option<T> {
        if self.len() > 0 {
            unsafe {
                self.range.end = self.range.end.sub(1);
                Some(self.range.end.read())
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
        unsafe { slice::from_raw_parts_mut(data as _, len) }
    }

    fn as_raw_slice_parts(&self) -> (*const T, usize) {
        if self.len() > 0 {
            let mut range = unsafe { PtrOrIdxRange::with_ptr_and_len(self.orig_ptr, self.orig_len) };

            // Refine start based on num_yielded_front
            let mut len = self.orig_len;
            let mut mask = self.num_parts >> 1;
            while mask > 0 {
                if self.num_yielded_front & mask == 0 {
                    len = len >> 1;
                } else {
                    range.start = unsafe { range.start.add(len >> 1) };
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
                    range.end = unsafe { range.end.sub(len - (len >> 1)) };
                    len = len >> 1;
                }
                mask >>= 1;
            }

            let len = range.len();
            (range.start.as_ptr(), len)
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
                    ptr = if mem::size_of::<T>() == 0 {
                        ptr
                    } else {
                        unsafe { ptr.add(len >> 1) }
                    };
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
    exact_count!();
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
                    ptr = if mem::size_of::<T>() == 0 {
                        ptr
                    } else {
                        unsafe { ptr.add(len >> 1) }
                    };
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

mod zst_utils {
    // NOTE: The whole approach used here is adapted from vec's IntoIter,
    // minus use of the internal arith_offset function for pointers to
    // ZSTs. See https://doc.rust-lang.org/std/vec/struct.IntoIter.html
    // and follow link from there to src.

    use core::{
        mem,
        ptr::{self, NonNull},
        slice,
    };

    /// A value that represents either a) a valid, properly aligned,
    /// non-null pointer to a type of size > 0, or b) a usize index into
    /// a slice of ZSTs.
    #[derive(Debug)]
    pub struct PtrOrIdx<T>(*const T);

    /// A subslice of some initial slice delimited either by start and end
    /// pointers (for types of size > 0) or by start and end indices (for
    /// ZSTs).
    #[derive(Debug)]
    pub struct PtrOrIdxRange<T> {
        pub start: PtrOrIdx<T>,
        pub end: PtrOrIdx<T>,
    }

    impl<T> PtrOrIdx<T> {
        #[inline]
        pub fn as_ptr(self) -> *const T {
            if mem::size_of::<T>() == 0 {
                NonNull::dangling().as_ptr()
            } else {
                self.0
            }
        }

        #[inline]
        pub fn as_mut_ptr(self) -> *mut T {
            self.as_ptr() as _
        }

        #[inline]
        pub unsafe fn read(self) -> T {
            if mem::size_of::<T>() == 0 {
                mem::zeroed()
            } else {
                ptr::read(self.0)
            }
        }

        #[inline]
        pub unsafe fn add(self, count: usize) -> Self {
            if mem::size_of::<T>() == 0 {
                Self((self.0 as usize + count) as _)
            } else {
                Self(self.0.add(count))
            }
        }

        #[inline]
        pub unsafe fn sub(self, count: usize) -> Self {
            if mem::size_of::<T>() == 0 {
                Self((self.0 as usize - count) as _)
            } else {
                Self(self.0.sub(count))
            }
        }
    }

    impl<T> Copy for PtrOrIdx<T> { }
    impl<T> Clone for PtrOrIdx<T> {
        #[inline]
        fn clone(&self) -> Self { *self }
    }

    impl<T> PtrOrIdxRange<T> {
        /// Construct a `PtrOrIdxRange` comprising the entire slice indicated
        /// by the given start pointer and length.
        /// Safety: Unsafe b/c in the case that mem::size_of::<T>() > 0, calling
        /// code must guarantee that `ptr` is a valid, properly aligned pointer
        /// to a slice of T's of length at least `len`. This guarantee is unneeded
        /// if T is a ZST.
        #[inline]
        pub unsafe fn with_ptr_and_len(ptr: NonNull<T>, len: usize) -> Self {
            if mem::size_of::<T>() == 0 {
                Self { start: PtrOrIdx(0 as _), end: PtrOrIdx(len as _) }
            } else {
                let ptr = ptr.as_ptr();
                // Safety: As long as calling code adheres to the safety guarantees
                // in the comment above, the pointer `add` below is safe for the same
                // reasons it's safe in the impl of, say, [T]'s as_ptr_range.
                // See https://doc.rust-lang.org/std/primitive.slice.html#method.as_ptr_range
                // and follow link from there to src.
                Self { start: PtrOrIdx(ptr), end: PtrOrIdx(ptr.add(len)) }
            }
        }

        #[inline]
        pub fn len(self) -> usize {
            if mem::size_of::<T>() == 0 {
                self.end.0 as usize - self.start.0 as usize
            } else {
                (self.end.0 as usize - self.start.0 as usize) / mem::size_of::<T>()
            }
        }

        #[inline]
        pub unsafe fn as_slice<'a>(self) -> &'a [T] {
            slice::from_raw_parts(self.start.as_ptr(), self.len())
        }

        #[inline]
        pub unsafe fn as_mut_slice<'a>(self) -> &'a mut [T] {
            slice::from_raw_parts_mut(self.start.as_mut_ptr(), self.len())
        }
    }

    impl<T> Copy for PtrOrIdxRange<T> { }
    impl<T> Clone for PtrOrIdxRange<T> {
        #[inline]
        fn clone(&self) -> Self { *self }
    }
}

#[cfg(test)]
mod test {
    use crate::internal::slice_model::{self, SliceAlloc};
    use super::SliceItems;

    // Like slice_model::split_alloc_from_items but returns the tuple elements
    // in the opposite order so that items will be dropped before alloc when
    // destructuring the return value. This accounts for a quirk in Rust's drop
    // order, which is that dropping of tuple elements (and struct fields and
    // many other things) is FIFO, but dropping of local variables is LIFO.
    // See https://github.com/rust-lang/rfcs/blob/master/text/1857-stabilize-drop-order.md
    unsafe fn alloc_and_items_for_destructuring<T>(slice: Box<[T]>) -> (Option<SliceAlloc<T>>, SliceItems<T>) {
        let (items, alloc) = slice_model::split_alloc_from_items(slice);
        (alloc, items)
    }

    #[test]
    fn split_off_left() {
        let v = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let (_alloc, mut items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let left = items.split_off_left();
        assert_eq!(["a"], left[..]);
        assert_eq!(["b", "c"], items[..]);
    }

    #[test]
    fn split_off_right() {
        let v = vec!["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string()];
        let (_alloc, mut items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let right = items.split_off_right();
        assert_eq!(["a", "b"], items[..]);
        assert_eq!(["c", "d"], right[..]);
    }

    #[test]
    fn split_off_left_zst() {
        let v = vec![(); 6];
        let (_alloc, mut items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let left = items.split_off_left();
        assert_eq!(3, left.len());
        assert_eq!(3, items.len());
    }

    #[test]
    fn split_off_right_zst() {
        let v = vec![(); 5];
        let (_alloc, mut items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let right = items.split_off_right();
        assert_eq!(2, items.len());
        assert_eq!(3, right.len());
    }

    #[test]
    fn deref_and_deref_mut() {
        let v = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let (_alloc, mut items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        assert_eq!("b", items[1]);
        items[1] = "x".to_string();
        assert_eq!("x", items[1]);
    }

    #[test]
    fn deref_and_deref_mut_zst() {
        let v = vec![(); 5];
        let (_alloc, mut items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        assert_eq!(5, items.len());
        // Mutating a ZST is fundamentally pointless, but we should still be able to do it
        items[1] = ();
        assert_eq!(5, items.len());
    }

    #[test]
    fn slice_items_iter_basic() {
        let v = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut iter = items.into_iter();
        assert_eq!("a", iter.next().unwrap());
        assert_eq!("b", iter.next().unwrap());
        assert_eq!("c", iter.next().unwrap());
        assert!(iter.next().is_none());
    }

    #[test]
    fn slice_items_iter_double_ended() {
        let v = vec!["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string()];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut iter = items.into_iter();
        assert_eq!("a", iter.next().unwrap());
        assert_eq!("d", iter.next_back().unwrap());
        assert_eq!("b", iter.next().unwrap());
        assert_eq!("c", iter.next_back().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());
    }

    #[test]
    fn slice_items_iter_zst() {
        let v = vec![(); 5];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut iter = items.into_iter();
        assert_eq!(5, iter.len());
        iter.next().unwrap();
        assert_eq!(4, iter.len());
        iter.next_back().unwrap();
        assert_eq!(3, iter.len());
        iter.next_back().unwrap();
        assert_eq!(2, iter.len());
        iter.next().unwrap();
        assert_eq!(1, iter.len());
        iter.next().unwrap();
        assert_eq!(0, iter.len());
        assert!(iter.next_back().is_none());
        assert!(iter.next().is_none());
    }

    #[test]
    fn slice_items_iter_as_slice() {
        let v = vec!["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string()];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut iter = items.into_iter();
        assert_eq!(["a", "b", "c", "d"], iter.as_slice());
        iter.next();
        assert_eq!(["b", "c", "d"], iter.as_slice());
        iter.next_back();
        assert_eq!(["b", "c"], iter.as_slice());
        iter.next_back();
        assert_eq!(["b"], iter.as_slice());
        iter.next_back();
        assert_eq!(0, iter.as_slice().len());
    }

    #[test]
    fn slice_items_iter_as_mut_slice() {
        let v = vec!["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string()];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut iter = items.into_iter();
        iter.as_mut_slice()[0] = "x".to_string();
        assert_eq!(["x", "b", "c", "d"], iter.as_slice());
        assert_eq!("x", iter.next().unwrap());
        iter.as_mut_slice()[2] = "y".to_string();
        assert_eq!(["b", "c", "y"], iter.as_slice());
        assert_eq!("y", iter.next_back().unwrap());
        iter.as_mut_slice()[1] = "z".to_string();
        assert_eq!(["b", "z"], iter.as_slice());
        assert_eq!("b", iter.next().unwrap());
        assert_eq!("z", iter.next().unwrap());
    }

    #[test]
    fn slice_items_iter_as_mut_slice_zst() {
        let v = vec![(); 5];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut iter = items.into_iter();
        assert_eq!(5, iter.as_slice().len());
        iter.next().unwrap();
        assert_eq!(4, iter.as_slice().len());
        iter.next_back().unwrap();
        assert_eq!(3, iter.as_slice().len());
        // Again, mutating a ZST is fundamentally pointless, but still should be able to
        iter.as_mut_slice()[2] = ();
        assert_eq!(3, iter.as_slice().len());
        assert_eq!(3, iter.as_mut_slice().len());
    }

    #[test]
    fn slice_items_iter_split_off_from() {
        let v = vec!["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string()];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut iter = items.into_iter();
        // Test a trivial split first: split off last 0 items
        let mut split = iter.split_off_from(4);
        assert_eq!(0, split.len());
        assert!(split.next().is_none());
        // Split off last item
        let mut split = iter.split_off_from(3);
        assert_eq!(1, split.len());
        assert_eq!("d", split.next().unwrap());
        assert!(split.next().is_none());
        // Assert current contents of iterator
        assert_eq!(["a", "b", "c"], iter.as_slice());
        assert_eq!("c", iter.next_back().unwrap());
        // Split off last 2 items, i.e. whole remaining iterator
        let mut split = iter.split_off_from(0);
        assert_eq!(0, iter.len());
        assert!(iter.next().is_none());
        assert_eq!(["a", "b"], split.as_slice());
        assert_eq!("b", split.next_back().unwrap());
        assert_eq!("a", split.next_back().unwrap());
    }

    #[test]
    fn slice_items_iter_split_off_to() {
        let v = vec!["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string()];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut iter = items.into_iter();
        // Test a trivial split first: split off first 0 items
        let mut split = iter.split_off_to(0);
        assert_eq!(0, split.len());
        assert!(split.next().is_none());
        // Split off first item
        let mut split = iter.split_off_to(1);
        assert_eq!(1, split.len());
        assert_eq!("a", split.next().unwrap());
        assert!(split.next().is_none());
        // Assert current contents of iterator
        assert_eq!(["b", "c", "d"], iter.as_slice());
        assert_eq!("b", iter.next().unwrap());
        // Split off first 2 items, i.e. whole remaining iterator
        let mut split = iter.split_off_to(2);
        assert_eq!(0, iter.len());
        assert!(iter.next().is_none());
        assert_eq!(["c", "d"], split.as_slice());
        assert_eq!("c", split.next().unwrap());
        assert_eq!("d", split.next().unwrap());
    }

    #[test]
    #[should_panic(expected = "at <=")]
    fn slice_items_iter_split_off_from_out_of_bounds() {
        let v = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut iter = items.into_iter();
        iter.split_off_from(4);
    }

    #[test]
    #[should_panic(expected = "at <=")]
    fn slice_items_iter_split_off_to_out_of_bounds() {
        let v = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut iter = items.into_iter();
        iter.split_off_to(4);
    }

    #[test]
    fn slice_items_split_off_from_zst() {
        let v = vec![(); 5];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut iter = items.into_iter();
        // Test a trivial split first: split off last 0 items
        let mut split = iter.split_off_from(5);
        assert_eq!(0, split.len());
        assert_eq!(0, split.as_slice().len());
        assert!(split.next().is_none());
        // Split off last 2 items
        let mut split = iter.split_off_from(3);
        assert_eq!(2, split.len());
        assert_eq!(2, split.as_slice().len());
        split.next().unwrap();
        assert_eq!(1, split.len());
        assert_eq!(1, split.as_slice().len());
        split.next_back().unwrap();
        assert_eq!(0, split.len());
        assert_eq!(0, split.as_slice().len());
        assert!(split.next().is_none());
        // Assert current contents of iterator
        assert_eq!(3, iter.as_slice().len());
        // Split off last 3 items, i.e. whole remaining iterator
        let mut split = iter.split_off_from(0);
        assert_eq!(0, iter.len());
        assert!(iter.next().is_none());
        assert_eq!(3, split.len());
        assert_eq!(3, split.as_slice().len());
        split.next_back().unwrap();
        assert_eq!(2, split.len());
        assert_eq!(2, split.as_slice().len());
        split.next().unwrap();
        assert_eq!(1, split.len());
        assert_eq!(1, split.as_slice().len());
    }

    #[test]
    fn slice_items_split_off_to_zst() {
        let v = vec![(); 5];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut iter = items.into_iter();
        // Test a trivial split first: split off first 0 items
        let mut split = iter.split_off_to(0);
        assert_eq!(0, split.len());
        assert_eq!(0, split.as_slice().len());
        assert!(split.next().is_none());
        // Split off first 2 items
        let mut split = iter.split_off_to(2);
        assert_eq!(2, split.len());
        assert_eq!(2, split.as_slice().len());
        split.next_back().unwrap();
        assert_eq!(1, split.len());
        assert_eq!(1, split.as_slice().len());
        split.next().unwrap();
        assert_eq!(0, split.len());
        assert_eq!(0, split.as_slice().len());
        assert!(split.next_back().is_none());
        // Assert current contentx of iterator
        assert_eq!(3, iter.as_slice().len());
        // Split off first 3 items, i.e. whole remaining iterator
        let mut split = iter.split_off_to(3);
        assert_eq!(0, iter.len());
        assert!(iter.next_back().is_none());
        assert_eq!(3, split.len());
        assert_eq!(3, split.as_slice().len());
        split.next().unwrap();
        assert_eq!(2, split.len());
        assert_eq!(2, split.as_slice().len());
        split.next_back().unwrap();
        assert_eq!(1, split.len());
        assert_eq!(1, split.as_slice().len());
    }

    #[test]
    fn slice_items_parts_basic() {
        let v = vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "d".to_string(),
            "e".to_string(),
            "f".to_string(),
            "g".to_string(),
            "h".to_string(),
        ];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut parts = items.split_into_parts(8);
        assert_eq!(["a"], parts.next().unwrap()[..]);
        assert_eq!(["b"], parts.next().unwrap()[..]);
        assert_eq!(["c"], parts.next().unwrap()[..]);
        assert_eq!(["d"], parts.next().unwrap()[..]);
        assert_eq!(["e"], parts.next().unwrap()[..]);
        assert_eq!(["f"], parts.next().unwrap()[..]);
        assert_eq!(["g"], parts.next().unwrap()[..]);
        assert_eq!(["h"], parts.next().unwrap()[..]);
        assert!(parts.next().is_none());
    }

    #[test]
    fn slice_items_parts_double_ended() {
        let v = vec!["a".to_string(), "b".to_string(), "c".to_string(), "d".to_string()];

        // All possible "walks" (sequences of next/next_back calls) for a split
        // into 4 parts, excluding the walk consisting purely of next calls,
        // since we have other tests that focus just on forward iteration.
        // 2 ^ 4 - 1 = 15 different walks.

        // Walk #1: next, next, next, next_back
        {
            let v = v.clone();
            let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
            let mut parts = items.split_into_parts(4);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert_eq!(["b"], parts.next().unwrap()[..]);
            assert_eq!(["c"], parts.next().unwrap()[..]);
            assert_eq!(["d"], parts.next_back().unwrap()[..]);
            assert!(parts.next().is_none());
            assert!(parts.next_back().is_none());
        }

        // Walk #2: next, next, next_back, next
        {
            let v = v.clone();
            let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
            let mut parts = items.split_into_parts(4);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert_eq!(["b"], parts.next().unwrap()[..]);
            assert_eq!(["d"], parts.next_back().unwrap()[..]);
            assert_eq!(["c"], parts.next().unwrap()[..]);
            assert!(parts.next().is_none());
            assert!(parts.next_back().is_none());
        }

        // Walk #3: next, next, next_back, next_back
        {
            let v = v.clone();
            let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
            let mut parts = items.split_into_parts(4);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert_eq!(["b"], parts.next().unwrap()[..]);
            assert_eq!(["d"], parts.next_back().unwrap()[..]);
            assert_eq!(["c"], parts.next_back().unwrap()[..]);
            assert!(parts.next().is_none());
            assert!(parts.next_back().is_none());
        }

        // Walk #4: next, next_back, next, next
        {
            let v = v.clone();
            let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
            let mut parts = items.split_into_parts(4);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert_eq!(["d"], parts.next_back().unwrap()[..]);
            assert_eq!(["b"], parts.next().unwrap()[..]);
            assert_eq!(["c"], parts.next().unwrap()[..]);
            assert!(parts.next().is_none());
            assert!(parts.next_back().is_none());
        }

        // Walk #5: next, next_back, next, next_back
        {
            let v = v.clone();
            let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
            let mut parts = items.split_into_parts(4);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert_eq!(["d"], parts.next_back().unwrap()[..]);
            assert_eq!(["b"], parts.next().unwrap()[..]);
            assert_eq!(["c"], parts.next_back().unwrap()[..]);
            assert!(parts.next().is_none());
            assert!(parts.next_back().is_none());
        }

        // Walk #6: next, next_back, next_back, next
        {
            let v = v.clone();
            let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
            let mut parts = items.split_into_parts(4);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert_eq!(["d"], parts.next_back().unwrap()[..]);
            assert_eq!(["c"], parts.next_back().unwrap()[..]);
            assert_eq!(["b"], parts.next().unwrap()[..]);
            assert!(parts.next().is_none());
            assert!(parts.next_back().is_none());
        }

        // Walk #7: next, next_back, next_back, next_back
        {
            let v = v.clone();
            let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
            let mut parts = items.split_into_parts(4);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert_eq!(["d"], parts.next_back().unwrap()[..]);
            assert_eq!(["c"], parts.next_back().unwrap()[..]);
            assert_eq!(["b"], parts.next_back().unwrap()[..]);
            assert!(parts.next().is_none());
            assert!(parts.next_back().is_none());
        }

        // Walk #8: next_back, next, next, next
        {
            let v = v.clone();
            let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
            let mut parts = items.split_into_parts(4);
            assert_eq!(["d"], parts.next_back().unwrap()[..]);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert_eq!(["b"], parts.next().unwrap()[..]);
            assert_eq!(["c"], parts.next().unwrap()[..]);
            assert!(parts.next().is_none());
            assert!(parts.next_back().is_none());
        }

        // Walk #9: next_back, next, next, next_back
        {
            let v = v.clone();
            let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
            let mut parts = items.split_into_parts(4);
            assert_eq!(["d"], parts.next_back().unwrap()[..]);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert_eq!(["b"], parts.next().unwrap()[..]);
            assert_eq!(["c"], parts.next_back().unwrap()[..]);
            assert!(parts.next().is_none());
            assert!(parts.next_back().is_none());
        }

        // Walk #10: next_back, next, next_back, next
        {
            let v = v.clone();
            let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
            let mut parts = items.split_into_parts(4);
            assert_eq!(["d"], parts.next_back().unwrap()[..]);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert_eq!(["c"], parts.next_back().unwrap()[..]);
            assert_eq!(["b"], parts.next().unwrap()[..]);
            assert!(parts.next().is_none());
            assert!(parts.next_back().is_none());
        }

        // Walk #11: next_back, next, next_back, next_back
        {
            let v = v.clone();
            let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
            let mut parts = items.split_into_parts(4);
            assert_eq!(["d"], parts.next_back().unwrap()[..]);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert_eq!(["c"], parts.next_back().unwrap()[..]);
            assert_eq!(["b"], parts.next_back().unwrap()[..]);
            assert!(parts.next().is_none());
            assert!(parts.next_back().is_none());
        }

        // Walk #12: next_back, next_back, next, next
        {
            let v = v.clone();
            let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
            let mut parts = items.split_into_parts(4);
            assert_eq!(["d"], parts.next_back().unwrap()[..]);
            assert_eq!(["c"], parts.next_back().unwrap()[..]);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert_eq!(["b"], parts.next().unwrap()[..]);
            assert!(parts.next().is_none());
            assert!(parts.next_back().is_none());
        }

        // Walk #13: next_back, next_back, next, next_back
        {
            let v = v.clone();
            let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
            let mut parts = items.split_into_parts(4);
            assert_eq!(["d"], parts.next_back().unwrap()[..]);
            assert_eq!(["c"], parts.next_back().unwrap()[..]);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert_eq!(["b"], parts.next_back().unwrap()[..]);
            assert!(parts.next().is_none());
            assert!(parts.next_back().is_none());
        }

        // Walk #14: next_back, next_back, next_back, next
        {
            let v = v.clone();
            let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
            let mut parts = items.split_into_parts(4);
            assert_eq!(["d"], parts.next_back().unwrap()[..]);
            assert_eq!(["c"], parts.next_back().unwrap()[..]);
            assert_eq!(["b"], parts.next_back().unwrap()[..]);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert!(parts.next().is_none());
            assert!(parts.next_back().is_none());
        }

        // Walk #15: next_back, next_back, next_back, next_back
        {
            let v = v.clone();
            let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
            let mut parts = items.split_into_parts(4);
            assert_eq!(["d"], parts.next_back().unwrap()[..]);
            assert_eq!(["c"], parts.next_back().unwrap()[..]);
            assert_eq!(["b"], parts.next_back().unwrap()[..]);
            assert_eq!(["a"], parts.next_back().unwrap()[..]);
            assert!(parts.next().is_none());
            assert!(parts.next_back().is_none());
        }
    }

    #[test]
    fn slice_items_parts_zst() {
        // Test a random "walk" of next/next_back calls for splitting a
        // slice of ZSTs into 16 parts.
        let v = vec![(); 32];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut parts = items.split_into_parts(16);
        assert_eq!(16, parts.len());
        assert_eq!(2, parts.next().unwrap().len());
        assert_eq!(15, parts.len());
        assert_eq!(2, parts.next().unwrap().len());
        assert_eq!(14, parts.len());
        assert_eq!(2, parts.next_back().unwrap().len());
        assert_eq!(13, parts.len());
        assert_eq!(2, parts.next_back().unwrap().len());
        assert_eq!(12, parts.len());
        assert_eq!(2, parts.next().unwrap().len());
        assert_eq!(11, parts.len());
        assert_eq!(2, parts.next_back().unwrap().len());
        assert_eq!(10, parts.len());
        assert_eq!(2, parts.next().unwrap().len());
        assert_eq!(9, parts.len());
        assert_eq!(2, parts.next_back().unwrap().len());
        assert_eq!(8, parts.len());
        assert_eq!(2, parts.next().unwrap().len());
        assert_eq!(7, parts.len());
        assert_eq!(2, parts.next().unwrap().len());
        assert_eq!(6, parts.len());
        assert_eq!(2, parts.next_back().unwrap().len());
        assert_eq!(5, parts.len());
        assert_eq!(2, parts.next().unwrap().len());
        assert_eq!(4, parts.len());
        assert_eq!(2, parts.next().unwrap().len());
        assert_eq!(3, parts.len());
        assert_eq!(2, parts.next_back().unwrap().len());
        assert_eq!(2, parts.len());
        assert_eq!(2, parts.next_back().unwrap().len());
        assert_eq!(1, parts.len());
        assert_eq!(2, parts.next().unwrap().len());
        assert_eq!(0, parts.len());
        assert!(parts.next().is_none());
        assert!(parts.next_back().is_none());
    }

    #[test]
    #[should_panic(expected = "power of 2")]
    fn split_into_parts_not_power_of_2() {
        let v = vec![0];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        items.split_into_parts(56);
    }

    #[test]
    #[should_panic(expected = "> 0")]
    fn split_into_zero_parts() {
        let v = vec![0];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        items.split_into_parts(0);
    }

    #[test]
    fn slice_items_parts_as_slice() {
        // Also use this as a test of num_parts > 8.
        let mut v = Vec::with_capacity(32);
        for i in 0..32 { v.push(i); }
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut parts = items.split_into_parts(32);
        assert_eq!(32, parts.as_slice().len());
        assert_eq!([0, 1, 2, 3, 4, 5], parts.as_slice()[..6]);
        assert_eq!([26, 27, 28, 29, 30, 31], parts.as_slice()[26..]);
        assert_eq!([0], parts.next().unwrap()[..]);
        assert_eq!(31, parts.as_slice().len());
        assert_eq!([1, 2, 3, 4, 5, 6], parts.as_slice()[..6]);
        assert_eq!([27, 28, 29, 30, 31], parts.as_slice()[26..]);
        assert_eq!([31], parts.next_back().unwrap()[..]);
        assert_eq!(30, parts.as_slice().len());
        assert_eq!([1, 2, 3, 4, 5, 6], parts.as_slice()[..6]);
        assert_eq!([27, 28, 29, 30], parts.as_slice()[26..]);
        assert_eq!([30], parts.next_back().unwrap()[..]);
        assert_eq!(29, parts.as_slice().len());
        assert_eq!([1, 2, 3, 4, 5, 6], parts.as_slice()[..6]);
        assert_eq!([27, 28, 29], parts.as_slice()[26..]);
        assert_eq!([1], parts.next().unwrap()[..]);
        assert_eq!(28, parts.as_slice().len());
        assert_eq!([2, 3, 4, 5, 6, 7], parts.as_slice()[..6]);
        assert_eq!([28, 29], parts.as_slice()[26..]);
        assert_eq!([29], parts.next_back().unwrap()[..]);
        assert_eq!(27, parts.as_slice().len());
        assert_eq!([2, 3, 4, 5, 6, 7], parts.as_slice()[..6]);
        assert_eq!([28], parts.as_slice()[26..]);
        assert_eq!([28], parts.next_back().unwrap()[..]);
        assert_eq!(26, parts.as_slice().len());
        assert_eq!([2, 3, 4, 5, 6, 7], parts.as_slice()[..6]);
        assert_eq!([25, 26, 27], parts.as_slice()[23..]);
        assert_eq!([2], parts.next().unwrap()[..]);
        assert_eq!(25, parts.as_slice().len());
        assert_eq!([3, 4, 5, 6, 7, 8], parts.as_slice()[..6]);
        assert_eq!([26, 27], parts.as_slice()[23..]);
    }

    #[test]
    fn slice_items_parts_len_and_as_slice_len() {
        // Illustrate the relationship btwn .len() and .as_slice().len().
        let v = vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "d".to_string(),
            "e".to_string(),
            "f".to_string(),
            "g".to_string(),
            "h".to_string(),
            "i".to_string(),
        ];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut parts = items.split_into_parts(4);
        assert_eq!(4, parts.len());
        assert_eq!(9, parts.as_slice().len());
        assert_eq!(["a", "b"], parts.next().unwrap()[..]);
        assert_eq!(3, parts.len());
        assert_eq!(7, parts.as_slice().len());
        assert_eq!(["c", "d"], parts.next().unwrap()[..]);
        assert_eq!(2, parts.len());
        assert_eq!(5, parts.as_slice().len());
        assert_eq!(["e", "f"], parts.next().unwrap()[..]);
        assert_eq!(1, parts.len());
        assert_eq!(3, parts.as_slice().len());
        assert_eq!(["g", "h", "i"], parts.next().unwrap()[..]);
        assert_eq!(0, parts.len());
        assert_eq!(0, parts.as_slice().len());
    }

    #[test]
    fn slice_items_parts_len_and_as_slice_len_zst() {
        let v = vec![(); 10];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut parts = items.split_into_parts(4);
        assert_eq!(4, parts.len());
        assert_eq!(10, parts.as_slice().len());
        assert_eq!(2, parts.next().unwrap().len());
        assert_eq!(3, parts.len());
        assert_eq!(8, parts.as_slice().len());
        assert_eq!(3, parts.next().unwrap().len());
        assert_eq!(2, parts.len());
        assert_eq!(5, parts.as_slice().len());
        assert_eq!(2, parts.next().unwrap().len());
        assert_eq!(1, parts.len());
        assert_eq!(3, parts.as_slice().len());
        assert_eq!(3, parts.next().unwrap().len());
        assert_eq!(0, parts.len());
        assert_eq!(0, parts.as_slice().len());
    }

    #[test]
    fn slice_items_parts_as_mut_slice() {
        let v = vec![10, 20, 30, 40, 50];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut parts = items.split_into_parts(2);
        parts.as_mut_slice()[0] = 60;
        assert_eq!([60, 20, 30, 40, 50], parts.as_slice());
        assert_eq!([60, 20], parts.next().unwrap()[..]);
        parts.as_mut_slice()[2] = 70;
        assert_eq!([30, 40, 70], parts.as_slice()[..]);
        assert_eq!([30, 40, 70], parts.next_back().unwrap()[..]);
        assert_eq!(0, parts.len());
    }

    #[test]
    fn slice_items_parts_as_mut_slice_zst() {
        let v = vec![(); 5];
        let (_alloc, items) = unsafe { alloc_and_items_for_destructuring(v.into_boxed_slice()) };
        let mut parts = items.split_into_parts(2);
        assert_eq!(5, parts.as_mut_slice().len());
        // And confirm we can do a pointless update.
        parts.as_mut_slice()[4] = ();
        assert_eq!(5, parts.as_mut_slice().len());
        parts.next().unwrap();
        assert_eq!(3, parts.as_mut_slice().len());
        // And another pointless update.
        parts.as_mut_slice()[2] = ();
        assert_eq!(3, parts.as_mut_slice().len());
    }
}
