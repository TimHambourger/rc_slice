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
pub struct SliceItems<T> {
    ptr: NonNull<T>,
    len: usize,
    phantom: PhantomData<T>,
}

pub struct SliceItemsIter<T> {
    start: NonNull<T>,
    end: NonNull<T>,
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
        let (items, _alloc) = unsafe { slice_model::split_alloc_from_items(v.into_boxed_slice()) };
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
}
