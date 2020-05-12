// Common logic for both RcSliceParts and ArcSliceParts.

use core::{
    iter::FusedIterator,
    mem,
    ops::Deref,
    ptr::NonNull,
    slice,
};
use alloc::collections::VecDeque;

/// A trait for types that can be split into left and right halves.
pub trait BinarySplitOff {
    fn split_off_left(this: &mut Self) -> Self;
    fn split_off_right(this: &mut Self) -> Self;
}

/// An iterator over parts of an initial whole. Parts are obtained by repeatedly
/// splitting off left or right halves.
#[derive(Clone)]
pub struct BinaryPartsIter<S> {
    num_parts: usize,
    num_yielded_front: usize,
    num_yielded_back: usize,
    deque: VecDeque<S>,
}

/// A marker trait that indicates that a type's BinarySplitOff impl acts
/// like splitting a slice. Succintly, this means the type's impls of
/// BinarySplitOff and Deref<Target=[T]> commute with each other. More
/// formally, by implementing `SplitAsSlice<T>` for a type S, you are
/// guaranteeing that the assertions in the following code snippets will
/// never panic:
///
/// #1
/// ```rs
/// let mut s: S;
/// let old_len = (*s).len();
/// let left = BinarySplitOff::split_off_left(&mut s);
/// // Assertion: new lengths sum to old length
/// assert_eq!(old_len, (*left).len() + (*s).len());
/// ```
///
/// #2
/// ```rs
/// let mut s: S;
/// let old_len = (*s).len();
/// let right = BinarySplitOff::split_off_right(&mut s);
/// // Assertion: new lengths sum to old length
/// assert_eq!(old_len, (*s).len() + (*right).len());
/// ```
///
/// Additionally, if `mem::size_of::<T>() > 0`, then you are also
/// guaranteeing that these additional assertions will never panic:
///
/// #3
/// ```rs
/// let mut s: S;
/// let old_ptr = (*s).as_ptr();
/// let left = BinarySplitOff::split_off_left(&mut s);
/// // Assertion: left starts at previous starting pointer
/// assert_eq!(old_ptr, (*left).as_ptr());
/// // Assertion: s now starts at previous starting pointer offset by length of left
/// assert_eq!(unsafe { old_ptr.add((*left).len()) }, (*s).as_ptr());
/// ```
///
/// #4
/// ```rs
/// let mut s: S;
/// let old_ptr = (*s).as_ptr();
/// let right = BinarySplitOff::split_off_right(&mut s);
/// // Assertion: s still starts at previous starting pointer
/// assert_eq!(old_ptr, (*s).as_ptr());
/// // Right starts at previous starting pointer offset by new length of s
/// assert_eq!(unsafe { old_ptr.add((*s).len()) }, (*right).as_ptr());
/// ```
///
/// `SplitAsSlice<T>` is unsafe to implement because BinaryPartsIter<S>::as_slice
/// assumes without proof that the assertions above hold in order to provide a safe
/// interface around unsafe slice operations.
//
// NOTE: Despite the T in SplitAsSlice<T> being a generic param, a given
// type S can in fact implement SplitAsSlice<T> for at most one type T
// since T constrains the associated Target type of S's Deref impl.
// It'd be nice to be able to use an associated type instead of a generic
// type param to express this, something like the commented out declaration
// below, but currently this gives a compiler error
//
//   where clauses on associated types are unstable
//
//   note: for more information, see https://github.com/rust-lang/rust/issues/44265 rustc(E0658)
//
// pub unsafe trait SplitAsSlice: BinarySplitOff + Deref {
//     type Item where Self: Deref<Target=[Item]>;
// }
pub unsafe trait SplitAsSlice<T>: BinarySplitOff + Deref<Target=[T]> { }

impl<S> BinaryPartsIter<S> {
    pub fn new(slice: S, num_parts: usize) -> Self {
        assert_ne!(0, num_parts, "num_parts > 0");
        let mut n = num_parts;
        let mut log: usize = 0;
        while n & 1 == 0 {
            log += 1;
            n >>= 1;
        }
        assert_eq!(1, n, "num_parts {} is a power of 2", num_parts);
        // Ensure our deque has enough capacity to iterate through all subslices
        // w/o growing. It turns out that for num_parts >= 4, the largest the
        // deque can possibly be is after you call next() then next_back() (or
        // next_back() then next(), the state of the deque is the same). This
        // provides exactly that much capacity. See note below for more.
        let cap = if log <= 1 { 1 } else { (log << 1) - 2 };
        let mut deque = VecDeque::with_capacity(cap);
        deque.push_front(slice);
        Self {
            num_parts,
            num_yielded_front: 0,
            num_yielded_back: 0,
            deque,
        }
    }

    /// Reference the remaining items in the iterator as a single slice.
    pub fn as_slice<T>(&self) -> &[T]
    where
        S: SplitAsSlice<T>,
    {
        if 0 == self.len() {
            unsafe { slice::from_raw_parts(NonNull::dangling().as_ptr(), 0) }
        } else if mem::size_of::<T>() == 0 {
            // For ZSTs, we can't use start and end pointers to compute a
            // length, so we instead sum up the lengths of the slices in
            // our deque.
            let len = self.deque.iter().map(|s| s.len()).sum();
            unsafe { slice::from_raw_parts(NonNull::dangling().as_ptr(), len) }
        } else {
            let start = self.deque.front()
                .map(|slice| slice.as_ptr())
                .expect("deque is nonempty when BinaryPartsIter not done iterating");
            let end = self.deque.back()
                .map(|slice| unsafe { slice.as_ptr().add(slice.len()) })
                .expect("deque is nonempty when BinaryPartsIter not done iterating");
            let len = (end as usize - start as usize) / mem::size_of::<T>();
            unsafe { slice::from_raw_parts(start, len) }
        }
    }
}

impl<S: BinarySplitOff> ExactSizeIterator for BinaryPartsIter<S> {
    #[inline]
    fn len(&self) -> usize {
        self.num_parts - self.num_yielded_front - self.num_yielded_back
    }
}

// Explanation of the math behind iterating BinaryPartsIter:
//
// Our basic strategy is to maintain a deque of subslices and to have
// next() and next_back() subdivide the slices at either end of the
// deque just enough to be able to yield the next subslice of the
// appropriate size.
//
// E.g. say num_parts = 8. As initially constructed, the deque contains
// a single BinarySplitOff spanning the entire original slice. To
// fulfill a call to next(), we subdivide as follows:
//
//                 ()        (initial state, one slice that hasn't been subdivided)
//            L          R   (subdivide in 2)
//       LL       LR     R   (subdivide L in 2 again)
//  [LLL]   LLR   LR     R   (subdivide LL in 2 again)
//
// In the last step LLL is in square brackets to show that it doens't
// ever need to get added to the deque since we can yield it immediately.
// The final state of the deque after the first call to next() is thus
//
// LLR  LR  R
//
// As another example, if we then call next_back(), we do the following
// series of subdivisions:
//
//  LLR   LR          R
//  LLR   LR     RL       RR
//  LLR   LR     RL    RRL   [RRR]
//
// Again RRR is in brackets b/c it can be yielded immediately. The final
// state of the deque is
//
// LLR  LR  RL  RRL
//
// The result is that the maximum size of the deque is O(log N) where
// N = num_parts and the cost of one call to next() or next_back() is
// likewise O(log N) in the worst case.
//
// It turns out that next() and next_back() commute w/ each other as far
// as their actions on the deque are concerned. I.e., to determine the
// state of the deque at any point, you only need to know num_parts and
// the number of times next() and next_back() have each been called;
// the order of those calls is irrelevant.
//
// Thus, our implementation of next() basically works as follows:
// In a loop, call split_off_left on the frontmost slice in the deque
// and push the returned slice onto the front of the deque. Do this
// until you've obtained a slice of the appropriate size to be yielded.
// Also, you can skip pushing this last slice onto the front of the
// deque since it can be yielded immediately. next_back() works the
// same way except it calls split_off_right on the backmost slice in
// the deque and pushes the returned slice onto the back.
//
// The real trick w/ both implementations is knowing when to stop looping.
// We COULD try to deduce this from the lengths of the slices involved,
// but that doesn't work when you start getting down to small slices:
// A length 1 slice subdivides as slices of length 0 and 1, so you get
// length 1 slices at multiple depths in the hierarchy. Or we could
// store the depth as metadata in our deque along with the actual slice.
// But that increases memory overhead.
//
// But it turns out we can quickly figure out how many times to loop by
// examining just num_parts, num_yielded_front, and num_yielded_back.
// Some hand waving examples to convince you that the implementations
// below actually work:
//
// For calls to next() when num_parts = 8:
//
// When...
// num_yielded_front = 0           Split ()         Skip if num_yielded_back > 0
//                                 Split L          Skip if num_yielded_back > 4
//                                 Split LL         Skip if num_yielded_back > 6
// num_yielded_front = 2           Split LR         Skip if num_yielded_back > 4
// num_yielded_front = 4           Split R          Skip if num_yielded_back > 0
//                                 Split RL         Skip if num_yielded_back > 2
// num_yielded_front = 6           Split RR         Skip if num_yielded_back > 0
//
// The common formula is: Let n be the largest power of 2 that's a factor of
// the number num_parts - num_yielded_front (which must be positive so long
// as we haven't yielded all subslices yet). Then you can skip the first
// split provided num_yielded_back > num_parts - num_yielded_front - n.
// Or, rearranging, you can skip the first split provided n > len.
// Set n = n / 2. Then you can skip the next split provided n is still >
// len. Repeat until n = 1.

impl<S: BinarySplitOff> Iterator for BinaryPartsIter<S> {
    type Item = S;

    fn next(&mut self) -> Option<S> {
        if 0 == self.len() {
            None
        } else {
            debug_assert_ne!(0, self.deque.len(), "deque is nonempty when BinaryPartsIter not done iterating");
            let initial_cap = self.deque.capacity();
            let mut n = greatest_power_of_2_factor(self.num_parts - self.num_yielded_front);
            let len = self.len();
            while n > len { n >>= 1; }
            let mut item: Option<S> = None;
            while n & 1 == 0 {
                if let Some(item) = item {
                    self.deque.push_front(item);
                }
                item = self.deque.front_mut().map(S::split_off_left);
                n >>= 1;
            }
            debug_assert_eq!(initial_cap, self.deque.capacity(), "deque doesn't need to re-allocate");
            self.num_yielded_front += 1;
            item.or_else(|| self.deque.pop_front())
        }
    }

    exact_size_hint!();
    exact_count!();
}

impl<S: BinarySplitOff> DoubleEndedIterator for BinaryPartsIter<S> {
    fn next_back(&mut self) -> Option<S> {
        // The exact mirror image of next(...).
        if 0 == self.len() {
            None
        } else {
            debug_assert_ne!(0, self.deque.len(), "deque is nonempty when BinaryPartsIter not done iterating");
            let initial_cap = self.deque.capacity();
            let mut n = greatest_power_of_2_factor(self.num_parts - self.num_yielded_back);
            let len = self.len();
            while n > len { n >>= 1; }
            let mut item: Option<S> = None;
            while n & 1 == 0 {
                if let Some(item) = item {
                    self.deque.push_back(item);
                }
                item = self.deque.back_mut().map(S::split_off_right);
                n >>= 1;
            }
            debug_assert_eq!(initial_cap, self.deque.capacity(), "deque doesn't need to re-allocate");
            self.num_yielded_back += 1;
            item.or_else(|| self.deque.pop_back())
        }
    }
}

/// Return the greatest power of 2 that's a factor of the given positive number.
/// Calling code is responsible for ensuring that the given number is positive.
#[inline]
fn greatest_power_of_2_factor(mut n: usize) -> usize {
    // A debug assertion only since this is a private function and our
    // calling code should guarantee this.
    debug_assert_ne!(0, n, "n > 0");
    let mut p = 1;
    while n & 1 == 0 {
        p <<= 1;
        n >>= 1;
    }
    p
}

impl<S: BinarySplitOff> FusedIterator for BinaryPartsIter<S> { }

#[cfg(test)]
mod test {
    use std::string::String;
    use super::*;

    #[derive(Clone, Debug, Default)]
    struct SplitMarker(String);

    impl SplitMarker {
        fn new() -> Self { Self::default() }
    }

    impl PartialEq<SplitMarker> for &str {
        fn eq(&self, other: &SplitMarker) -> bool {
            *self == other.0
        }
    }

    impl BinarySplitOff for SplitMarker {
        fn split_off_left(this: &mut Self) -> Self {
            let left = SplitMarker(format!("{}L", this.0));
            this.0 = format!("{}R", this.0);
            left
        }

        fn split_off_right(this: &mut Self) -> Self {
            let right = SplitMarker(format!("{}R", this.0));
            this.0 = format!("{}L", this.0);
            right
        }
    }

    #[test]
    fn parts_eq_1() {
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 1);
        assert_eq!("", iter.next().unwrap());
        assert!(iter.next().is_none());
    }

    #[test]
    fn parts_eq_2() {
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 2);
        assert_eq!("L", iter.next().unwrap());
        assert_eq!("R", iter.next().unwrap());
        assert!(iter.next().is_none());
    }

    #[test]
    fn parts_eq_4() {
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("LL", iter.next().unwrap());
        assert_eq!("LR", iter.next().unwrap());
        assert_eq!("RL", iter.next().unwrap());
        assert_eq!("RR", iter.next().unwrap());
        assert!(iter.next().is_none());
    }

    #[test]
    fn parts_eq_8() {
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 8);
        assert_eq!("LLL", iter.next().unwrap());
        assert_eq!("LLR", iter.next().unwrap());
        assert_eq!("LRL", iter.next().unwrap());
        assert_eq!("LRR", iter.next().unwrap());
        assert_eq!("RLL", iter.next().unwrap());
        assert_eq!("RLR", iter.next().unwrap());
        assert_eq!("RRL", iter.next().unwrap());
        assert_eq!("RRR", iter.next().unwrap());
        assert!(iter.next().is_none());
    }

    #[test]
    fn iter_front_and_back() {
        // All possible "walks" (sequences of next/next_back calls) for a split
        // into 4 parts, excluding the walk consisting purely of next calls,
        // since we have other tests that focus just on forward iteration.
        // 2 ^ 4 - 1 = 15 different walks.

        // Walk #1: next, next, next, next_back
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("LL", iter.next().unwrap());
        assert_eq!("LR", iter.next().unwrap());
        assert_eq!("RL", iter.next().unwrap());
        assert_eq!("RR", iter.next_back().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // Walk #2: next, next, next_back, next
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("LL", iter.next().unwrap());
        assert_eq!("LR", iter.next().unwrap());
        assert_eq!("RR", iter.next_back().unwrap());
        assert_eq!("RL", iter.next().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // Walk #3: next, next, next_back, next_back
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("LL", iter.next().unwrap());
        assert_eq!("LR", iter.next().unwrap());
        assert_eq!("RR", iter.next_back().unwrap());
        assert_eq!("RL", iter.next_back().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // Walk #4: next, next_back, next, next
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("LL", iter.next().unwrap());
        assert_eq!("RR", iter.next_back().unwrap());
        assert_eq!("LR", iter.next().unwrap());
        assert_eq!("RL", iter.next().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // Walk #5: next, next_back, next, next_back
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("LL", iter.next().unwrap());
        assert_eq!("RR", iter.next_back().unwrap());
        assert_eq!("LR", iter.next().unwrap());
        assert_eq!("RL", iter.next_back().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // Walk #6: next, next_back, next_back, next
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("LL", iter.next().unwrap());
        assert_eq!("RR", iter.next_back().unwrap());
        assert_eq!("RL", iter.next_back().unwrap());
        assert_eq!("LR", iter.next().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // Walk #7: next, next_back, next_back, next_back
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("LL", iter.next().unwrap());
        assert_eq!("RR", iter.next_back().unwrap());
        assert_eq!("RL", iter.next_back().unwrap());
        assert_eq!("LR", iter.next_back().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // Walk #8: next_back, next, next, next
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("RR", iter.next_back().unwrap());
        assert_eq!("LL", iter.next().unwrap());
        assert_eq!("LR", iter.next().unwrap());
        assert_eq!("RL", iter.next().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // Walk #9: next_back, next, next, next_back
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("RR", iter.next_back().unwrap());
        assert_eq!("LL", iter.next().unwrap());
        assert_eq!("LR", iter.next().unwrap());
        assert_eq!("RL", iter.next_back().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // Walk #10: next_back, next, next_back, next
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("RR", iter.next_back().unwrap());
        assert_eq!("LL", iter.next().unwrap());
        assert_eq!("RL", iter.next_back().unwrap());
        assert_eq!("LR", iter.next().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // Walk #11: next_back, next, next_back, next_back
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("RR", iter.next_back().unwrap());
        assert_eq!("LL", iter.next().unwrap());
        assert_eq!("RL", iter.next_back().unwrap());
        assert_eq!("LR", iter.next_back().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // Walk #12: next_back, next_back, next, next
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("RR", iter.next_back().unwrap());
        assert_eq!("RL", iter.next_back().unwrap());
        assert_eq!("LL", iter.next().unwrap());
        assert_eq!("LR", iter.next().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // Walk #13: next_back, next_back, next, next_back
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("RR", iter.next_back().unwrap());
        assert_eq!("RL", iter.next_back().unwrap());
        assert_eq!("LL", iter.next().unwrap());
        assert_eq!("LR", iter.next_back().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // Walk #14: next_back, next_back, next_back, next
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("RR", iter.next_back().unwrap());
        assert_eq!("RL", iter.next_back().unwrap());
        assert_eq!("LR", iter.next_back().unwrap());
        assert_eq!("LL", iter.next().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());

        // Walk #15: next_back, next_back, next_back, next_back
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("RR", iter.next_back().unwrap());
        assert_eq!("RL", iter.next_back().unwrap());
        assert_eq!("LR", iter.next_back().unwrap());
        assert_eq!("LL", iter.next_back().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());
    }

    #[test]
    fn parts_eq_32_front_back_sample() {
        // One particular "walk" of 32 next/next_back calls. Nothing special
        // about this walk vs any other. Just want a test that uses both
        // next and next_back and deals w/ a higher num_parts than our other
        // tests.
        let mut iter = BinaryPartsIter::new(SplitMarker::new(), 32);
        assert_eq!("LLLLL", iter.next().unwrap());
        assert_eq!("LLLLR", iter.next().unwrap());
        assert_eq!("RRRRR", iter.next_back().unwrap());
        assert_eq!("RRRRL", iter.next_back().unwrap());
        assert_eq!("LLLRL", iter.next().unwrap());
        assert_eq!("LLLRR", iter.next().unwrap());
        assert_eq!("RRRLR", iter.next_back().unwrap());
        assert_eq!("LLRLL", iter.next().unwrap());
        assert_eq!("RRRLL", iter.next_back().unwrap());
        assert_eq!("LLRLR", iter.next().unwrap());
        assert_eq!("LLRRL", iter.next().unwrap());
        assert_eq!("LLRRR", iter.next().unwrap());
        assert_eq!("RRLRR", iter.next_back().unwrap());
        assert_eq!("LRLLL", iter.next().unwrap());
        assert_eq!("RRLRL", iter.next_back().unwrap());
        assert_eq!("RRLLR", iter.next_back().unwrap());
        assert_eq!("LRLLR", iter.next().unwrap());
        assert_eq!("RRLLL", iter.next_back().unwrap());
        assert_eq!("LRLRL", iter.next().unwrap());
        assert_eq!("LRLRR", iter.next().unwrap());
        assert_eq!("RLRRR", iter.next_back().unwrap());
        assert_eq!("RLRRL", iter.next_back().unwrap());
        assert_eq!("RLRLR", iter.next_back().unwrap());
        assert_eq!("LRRLL", iter.next().unwrap());
        assert_eq!("LRRLR", iter.next().unwrap());
        assert_eq!("RLRLL", iter.next_back().unwrap());
        assert_eq!("LRRRL", iter.next().unwrap());
        assert_eq!("LRRRR", iter.next().unwrap());
        assert_eq!("RLLRR", iter.next_back().unwrap());
        assert_eq!("RLLLL", iter.next().unwrap());
        assert_eq!("RLLRL", iter.next_back().unwrap());
        assert_eq!("RLLLR", iter.next().unwrap());
        assert!(iter.next().is_none());
        assert!(iter.next_back().is_none());
    }

    #[test]
    #[should_panic(expected = "power of 2")]
    fn parts_not_power_of_2() {
        BinaryPartsIter::new(SplitMarker::new(), 32 * 3 * 7);
    }

    #[test]
    #[should_panic(expected = "> 0")]
    fn parts_eq_0() {
        BinaryPartsIter::new(SplitMarker::new(), 0);
    }

    #[test]
    fn clone() {
        let mut orig = BinaryPartsIter::new(SplitMarker::new(), 4);
        assert_eq!("LL", orig.next().unwrap());
        assert_eq!(3, orig.len());

        let mut clone = orig.clone();
        // Clone iter matches iteration state of original
        assert_eq!(3, clone.len());
        assert_eq!("LR", clone.next().unwrap());
        assert_eq!("RR", clone.next_back().unwrap());
        assert_eq!("RL", clone.next().unwrap());
        assert!(clone.next().is_none());
        assert!(clone.next_back().is_none());

        // And original is still in same state it was
        assert_eq!(3, orig.len());
        assert_eq!("LR", orig.next().unwrap());
        assert_eq!("RR", orig.next_back().unwrap());
        assert_eq!("RL", orig.next().unwrap());
        assert!(orig.next().is_none());
        assert!(orig.next_back().is_none());
    }

    #[derive(Debug, PartialEq)]
    struct SliceWrapper<'a, T>(&'a [T]);

    impl<'a, T> Deref for SliceWrapper<'a, T> {
        type Target = [T];
        fn deref(&self) -> &[T] { self.0 }
    }

    impl<'a, T> BinarySplitOff for SliceWrapper<'a, T> {
        fn split_off_left(this: &mut Self) -> Self {
            let (left, right) = this.0.split_at(this.0.len() / 2);
            *this = SliceWrapper(right);
            SliceWrapper(left)
        }

        fn split_off_right(this: &mut Self) -> Self {
            let (left, right) = this.0.split_at(this.0.len() / 2);
            *this = SliceWrapper(left);
            SliceWrapper(right)
        }
    }

    unsafe impl<'a, T> SplitAsSlice<T> for SliceWrapper<'a, T> { }

    #[test]
    fn as_slice() {
        let slice = SliceWrapper(&[0, 5, 10, 15, 20]);
        let mut parts = BinaryPartsIter::new(slice, 4);
        assert_eq!([0, 5, 10, 15, 20], parts.as_slice());
        assert_eq!(SliceWrapper(&[0]), parts.next().unwrap());
        assert_eq!([5, 10, 15, 20], parts.as_slice());
        assert_eq!(SliceWrapper(&[15, 20]), parts.next_back().unwrap());
        assert_eq!([5, 10], parts.as_slice());
        assert_eq!(SliceWrapper(&[10]), parts.next_back().unwrap());
        assert_eq!([5], parts.as_slice());
        assert_eq!(SliceWrapper(&[5]), parts.next().unwrap());
        assert_eq!(0, parts.len());
        assert_eq!(0, parts.as_slice().len());
    }

    #[test]
    fn as_slice_zst() {
        let slice = SliceWrapper(&[(); 6]);
        let mut parts = BinaryPartsIter::new(slice, 4);
        assert_eq!(6, parts.as_slice().len());
        assert_eq!(2, parts.next_back().unwrap().len());
        assert_eq!(4, parts.as_slice().len());
        assert_eq!(1, parts.next().unwrap().len());
        assert_eq!(3, parts.as_slice().len());
        assert_eq!(2, parts.next().unwrap().len());
        assert_eq!(1, parts.as_slice().len());
        assert_eq!(1, parts.next_back().unwrap().len());
        assert_eq!(0, parts.as_slice().len());
    }
}
