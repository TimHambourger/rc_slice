use core::{
    borrow::Borrow,
    cell::{Cell, RefCell},
    cmp::Ordering,
    hash::{Hash, Hasher},
    iter::{FromIterator, FusedIterator},
    marker::PhantomData,
    mem,
    ops::Deref,
    ptr::{self, NonNull},
    slice,
};
use alloc::{
    boxed::Box,
    collections::VecDeque,
    rc::{Rc, Weak},
    vec::Vec,
};

use crate::{
    internal::slice_model::SliceAlloc,
    rc::RcSliceMut,
};

// Relationship btwn RcSlice, RcSliceData, and DataGuard:
//
// RcSlice          RcSliceData         DataGuard
//
//                 s  t  r  o  n  g
//     |------------------------------------|
//     |      strong              weak      v
//   parent  ------->   parent  ------->  parent
//                     s | ^                ^ s
//                     t | | w              | t
//                     r | | e              | r
//                     o | | a              | o
//                     n | | k              | n
//            strong   g v |      weak      | g
//    child  ------->   child   ------->  child
//     |                                    ^
//     |------------------------------------|
//                 s  t  r  o  n  g
//
// Idea: Each RcSlice holds a strong ref to its RcSliceData. Parent
// RcSliceDatas hold strong refs to their children RcSliceDatas, so that
// dropping a child RcSlice doesn't cause its RcSliceData to get dropped
// if there's still a parent RcSlice around. Each RcSlice also holds a
// strong ref to a DataGuard, which in turn holds an optional strong ref
// to its parent DataGuard. Idea there is an RcSlice can check whether it
// holds the only strong ref to its RcSliceData as a way of checking
// whether that data has any still-living ancestors, and it can check
// whether it holds the only strong ref to its DataGuard as a way of
// checking whether its data has any still-living descendants.

#[derive(Debug)]
pub (in crate::rc) struct RcSliceData<T> {
    ptr: NonNull<T>,
    len: usize,
    // An Option b/c we'll let this be None for length zero sublices. They
    // don't need an underlying allocation.
    alloc: Option<Rc<SliceAlloc<T>>>,
    // Really Cell<Option<NonNull<Self>>> where the pointer is obtained via
    // Rc<Self>::into_raw(). But we need RcSliceData<T> to be covariant
    // in T.
    left_child: Cell<Option<NonNull<()>>>,
    // Ditto left_child on really Cell<Option<NonNull<Self>>>
    right_child: Cell<Option<NonNull<()>>>,
    parent: Weak<Self>,
    guard: RefCell<Weak<DataGuard>>,
    phantom_item: PhantomData<T>,
    phantom_child: PhantomData<Self>,
}

/// Signals the presence of child RcSlices or WeakSlices for the same
/// data subslice. Part of detecting which mutations are possible.
#[derive(Debug)]
struct DataGuard {
    // Not used except in the fact that a child DataGuard keeps its
    // parent DataGuard alive.
    _parent: Option<Rc<Self>>,
}

/// A reference counted slice that tracks reference counts per
/// subslice.
#[derive(Debug)]
pub struct RcSlice<T> {
    data: Rc<RcSliceData<T>>,
    data_guard: Rc<DataGuard>,
}

/// A weak reference to a reference counted slice. Comparable to
/// std::rc::Weak<[T]>
#[derive(Debug)]
pub struct WeakSlice<T> {
    data: Weak<RcSliceData<T>>,
    // Not used except as part of signaling the presence of WeakSlices to RcSlice::get_mut
    _data_guard: Weak<DataGuard>,
}

/// A double-ended iterator over roughly-even subslices of a starting RcSlice.
#[derive(Debug)]
pub struct RcSliceParts<T> {
    num_parts: usize,
    num_yielded_front: usize,
    num_yielded_back: usize,
    deque: VecDeque<RcSlice<T>>,
}

impl<T> RcSliceData<T> {
    fn from_boxed_slice(slice: Box<[T]>) -> Self {
        assert_ne!(0, mem::size_of::<T>(), "TODO: Support ZSTs");
        let len = slice.len();
        unsafe {
            // Waiting on stabilization of Box::into_raw_non_null
            let ptr = NonNull::new_unchecked(Box::into_raw(slice) as _);
            let alloc = if len == 0 { None } else { Some(Rc::new(SliceAlloc::new(ptr, len))) };
            Self::from_data_parts(ptr, len, alloc)
        }
    }

    pub (in crate::rc) unsafe fn from_data_parts(ptr: NonNull<T>, len: usize, alloc: Option<Rc<SliceAlloc<T>>>) -> Self {
        Self::with_data_and_parent(ptr, len, alloc, Weak::new())
    }

    fn with_data_and_parent(ptr: NonNull<T>, len: usize, alloc: Option<Rc<SliceAlloc<T>>>, parent: Weak<Self>) -> Self {
        RcSliceData {
            ptr,
            len,
            alloc,
            parent,
            left_child: Cell::new(None),
            right_child: Cell::new(None),
            guard: RefCell::new(Weak::new()),
            phantom_item: PhantomData,
            phantom_child: PhantomData,
        }
    }

    fn clone_left(self: &Rc<Self>) -> Rc<Self> {
        if self.len == 0 {
            self.clone()
        } else {
            let (ptr, len) = self.left_sub();
            unsafe {
                self.clone_child(&self.left_child, ptr, len)
            }
        }
    }

    fn clone_right(self: &Rc<Self>) -> Rc<Self> {
        if self.len <= 1 {
            self.clone()
        } else {
            let (ptr, len) = self.right_sub();
            unsafe {
                self.clone_child(&self.right_child, ptr, len)
            }
        }
    }

    unsafe fn clone_child(self: &Rc<Self>, cell: &Cell<Option<NonNull<()>>>, ptr: NonNull<T>, len: usize) -> Rc<Self> {
        cell.get().map_or_else(
            || {
                let alloc = if len == 0 { None } else { self.alloc.clone() };
                let new = Rc::new(Self::with_data_and_parent(ptr, len, alloc, Rc::downgrade(self)));
                let clone = new.clone();
                cell.set(Some(NonNull::new_unchecked(Rc::into_raw(new) as _)));
                clone
            },
            |ptr| {
                let existing = Rc::from_raw(ptr.as_ptr() as *const Self);
                let clone = existing.clone();
                mem::forget(existing);
                clone
            }
        )
    }

    fn take_left(&mut self) -> Option<Rc<Self>> {
        Self::take_child(&mut self.left_child)
    }

    fn take_right(&mut self) -> Option<Rc<Self>> {
        Self::take_child(&mut self.right_child)
    }

    fn take_child(cell: &mut Cell<Option<NonNull<()>>>) -> Option<Rc<Self>> {
        cell.get_mut().take().map(|ptr| unsafe { Rc::from_raw(ptr.as_ptr() as *const Self) })
    }

    fn left_sub(&self) -> (NonNull<T>, usize) {
        (self.ptr, self.len >> 1)
    }

    fn right_sub(&self) -> (NonNull<T>, usize) {
        // TODO: Support ZSTs
        (unsafe { NonNull::new_unchecked(self.ptr.as_ptr().offset((self.len >> 1) as isize)) }, self.len - (self.len >> 1))
    }

    /// Convert this RcSliceData into an RcSliceMut. Unsafe b/c calling code
    /// must ensure that there are no strong refs to any other RcSliceData
    /// overlapping this one.
    unsafe fn into_mut(mut self) -> RcSliceMut<T> {
        let slice_mut = RcSliceMut::from_raw_parts(self.ptr, self.len, self.alloc.take());
        // We don't want to drop the items in this subslice when self gets dropped,
        // b/c we've transferred their ownership to slice_mut. But we DO wanna drop
        // things like our strong refs to our child datas, ref cells with the weak
        // refs to our data guards, etc, to avoid leaking all that.
        self.forget_items();
        slice_mut
    }

    fn forget_items(&mut self) {
        // Recursively tell left child to forget its items
        self.take_left().map(|child| Rc::try_unwrap(child).map(|mut child| child.forget_items()));
        // Recursively tell right child to forget its items
        self.take_right().map(|child| Rc::try_unwrap(child).map(|mut child| child.forget_items()));
        // Setting len to 0 turns our Drop impl into a no-op.
        self.len = 0;
    }
}

impl<T> Drop for RcSliceData<T> {
    fn drop(&mut self) {
        // Move the children out to decrement their strong counts and
        // also to figure out what range of items to drop, if any.
        let left = self.take_left();
        let right = self.take_right();
        let (p, len) = match (left, right) {
            (None, None) => (self.ptr, self.len),
            (Some(_), None) => {
                // left child is present. Just drop right subslice
                self.right_sub()
            },
            (None, Some(_)) => {
                // right child is present. Just drop left subslice
                self.left_sub()
            },
            _ => return // Both children are present. Nothing more to do.
        };
        // Use [T]'s drop impl to drop the items without freeing the underlying allocation.
        // SliceAlloc handles freeing the underlying allocation.
        // The idea of using drop_in_place was taken straight from the drop impl for Vec<T>.
        // See https://doc.rust-lang.org/src/alloc/vec.rs.html
        unsafe { ptr::drop_in_place(slice::from_raw_parts_mut(p.as_ptr(), len)); }
    }
}

impl<T> Deref for RcSliceData<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
}

impl DataGuard {
    fn guard<T>(data: &RcSliceData<T>) -> Rc<Self> {
        let existing_guard = data.guard.borrow().upgrade();
        existing_guard.unwrap_or_else(|| {
            // No reference to a live existing guard. If our parent is still alive,
            // guard IT and use that returned guard as our parent. Otherwise we have
            // no parent guard.
            let parent_guard = data.parent.upgrade()
                .map(|parent_data| Self::guard(&parent_data));
            let guard = Rc::new(DataGuard { _parent: parent_guard });
            // Save a weak ref to the new guard in the passed data instance
            *data.guard.borrow_mut() = Rc::downgrade(&guard);
            guard
        })
    }
}

impl<T> RcSlice<T> {
    pub (in crate::rc) fn from_data(data: Rc<RcSliceData<T>>) -> Self {
        let data_guard = DataGuard::guard(&data);
        RcSlice { data, data_guard }
    }

    pub fn from_boxed_slice(slice: Box<[T]>) -> Self {
        Self::from_data(Rc::new(RcSliceData::from_boxed_slice(slice)))
    }

    pub fn from_vec(vec: Vec<T>) -> Self {
        Self::from_boxed_slice(vec.into_boxed_slice())
    }

    pub fn clone_left(this: &Self) -> Self {
        Self::from_data(this.data.clone_left())
    }

    pub fn clone_right(this: &Self) -> Self {
        Self::from_data(this.data.clone_right())
    }

    pub fn split_off_left(this: &mut Self) -> Self {
        let left = Self::clone_left(this);
        let right = Self::clone_right(this);
        *this = right;
        left
    }

    pub fn split_off_right(this: &mut Self) -> Self {
        let left = Self::clone_left(this);
        let right = Self::clone_right(this);
        *this = left;
        right
    }

    pub fn split_into_parts(this: Self, num_parts: usize) -> RcSliceParts<T> {
        RcSliceParts::new(this, num_parts)
    }

    pub fn get_mut(this: &mut Self) -> Option<&mut [T]> {
        // We need to check for any RcSlices referencing ancestor or
        // descendant RcSliceDatas, and we need to check for any RcSlices
        // or WeakSlices referencing our own RcSliceData. We DON'T need to
        // check for WeakSlices referencing ancestor or descendant
        // RcSliceDatas: We hold no strong ref to any RcSliceData but our
        // own, so the only way any WeakSlice could still hold an active
        // reference to one of those other RcSliceDatas would be if there
        // was also another RcSlice around.
        let safe_to_mut =
            // We're the only strong ref to our data_guard. Checks that
            // there are no child RcSlices.
            1 == Rc::strong_count(&this.data_guard) &&
            // We're the only strong ref to our data. Checks that there
            // are no parent RcSlices.
            1 == Rc::strong_count(&this.data) &&
            // Our data holds the only weak ref to our data guard. Checks
            // that there are no WeakSlices pointing to our same data.
            1 == Rc::weak_count(&this.data_guard);
        if safe_to_mut {
            unsafe { Some(slice::from_raw_parts_mut((*this.data).ptr.as_ptr(), (*this.data).len)) }
        } else {
            None
        }
    }

    pub fn into_mut(this: Self) -> Result<RcSliceMut<T>, Self> {
        // Similar to get_mut. But now we don't care about WeakSlices
        // referencing our own RcSliceData: As long as we're the only strong
        // ref to that RcSliceData, the act of converting that RcSliceData into
        // an RcSliceMut will invalidate those WeakSlices. This is the
        // same reason Rc::try_unwrap only cares about strong refs.
        if 1 == Rc::strong_count(&this.data_guard) {
            let RcSlice { data, data_guard } = this;
            Rc::try_unwrap(data).map_or_else(
                |data| {
                    // Error unwrapping data. Reconstruct our RcSlice
                    Err(RcSlice { data, data_guard })
                },
                |data| unsafe { Ok(data.into_mut()) }
            )
        } else {
            Err(this)
        }
    }

    pub fn downgrade(this: &Self) -> WeakSlice<T> {
        WeakSlice { data: Rc::downgrade(&this.data), _data_guard: Rc::downgrade(&this.data_guard) }
    }

    // TODO: unsplit
    // TODO: make_mut
    // TODO: into_boxed_slice, into_vec
}

impl<T> Clone for RcSlice<T> {
    fn clone(&self) -> Self {
        RcSlice {
            data: self.data.clone(),
            data_guard: self.data_guard.clone(),
        }
    }
}

impl<T> Deref for RcSlice<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &self.data
    }
}

impl<T> From<Box<[T]>> for RcSlice<T> {
    fn from(slice: Box<[T]>) -> Self {
        Self::from_boxed_slice(slice)
    }
}

impl<T> From<Vec<T>> for RcSlice<T> {
    fn from(vec: Vec<T>) -> Self {
        Self::from_vec(vec)
    }
}

impl<T> From<RcSliceMut<T>> for RcSlice<T> {
    fn from(slice_mut: RcSliceMut<T>) -> Self {
        RcSliceMut::into_immut(slice_mut)
    }
}

borrow_as_slice!(RcSlice);
compare_as_slice!(RcSlice);
hash_as_slice!(RcSlice);
from_iter_via_vec!(RcSlice);

impl<T> WeakSlice<T> {
    /// Constructs a new `WeakSlice<T>`, without allocating any memory.
    /// Calling `upgrade` on the return value always gives `None`.
    pub fn new() -> Self {
        WeakSlice { data: Weak::new(), _data_guard: Weak::new() }
    }

    pub fn upgrade(&self) -> Option<RcSlice<T>> {
        // TODO: This upgrade strategy has a few limitations we might wanna relax:
        // For one, to upgrade a WeakSlice, you need there to be a strong ref to the
        // referenced slice or some ancestor of it. E.g., it'd be cool if the
        // following worked, but currently it won't:
        //
        //  let slice = RcSlice::from_vec(some_vec);
        //  let left = RcSlice::clone_left(&slice);
        //  let right = RcSlice::clone_right(&slice);
        //  let weak = RcSlice::downgrade(&slice);
        //  drop(slice); // Drop the original RcSlice
        //  let upgraded = weak.upgrade(); // Will be None, unfortunately
        //
        // In the last line, it feels like we SHOULD be able to upgrade `weak`
        // since `left` and `right` together keep alive the full original slice,
        // albeit as two RcSlices instead of one. But currently that won't work.
        //
        // Similarly, once we implement RcSlice::unsplit, we won't be able
        // to upgrade `weak` even if we were to join `left` and `right` back
        // into a single RcSlice spanning the entire original slice.
        self.data.upgrade().map(RcSlice::from_data)
    }
}

impl<T> Clone for WeakSlice<T> {
    fn clone(&self) -> WeakSlice<T> {
        WeakSlice { data: self.data.clone(), _data_guard: self._data_guard.clone() }
    }
}

impl<T> RcSliceParts<T> {
    fn new(slice: RcSlice<T>, num_parts: usize) -> Self {
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
        RcSliceParts {
            num_parts,
            num_yielded_front: 0,
            num_yielded_back: 0,
            deque,
        }
    }

    /// Reference the remaining items in the iterator as a single slice.
    pub fn as_slice(&self) -> &[T] {
        if 0 == self.len() {
            unsafe { slice::from_raw_parts(NonNull::dangling().as_ptr(), 0) }
        } else {
            // TODO: Support ZSTs
            let start = self.deque.front()
                .map(|slice| slice.as_ptr())
                .expect("deque is nonempty when RcSliceParts not done iterating");
            let end = self.deque.back()
                .map(|slice| unsafe { slice.as_ptr().offset(slice.len() as isize) })
                .expect("deque is nonempty when RcSliceParts not done iterating");
            let len = (end as usize - start as usize) / mem::size_of::<T>();
            unsafe { slice::from_raw_parts(start, len) }
        }
    }
}

impl<T> ExactSizeIterator for RcSliceParts<T> {
    #[inline]
    fn len(&self) -> usize {
        self.num_parts - self.num_yielded_front - self.num_yielded_back
    }
}

// Explanation of the math behind iterating RcSliceParts:
//
// Our basic strategy is to maintain a deque of subslices and to have
// next() and next_back() subdivide the slices at either end of the
// deque just enough to be able to yield the next subslice of the
// appropriate size.
//
// E.g. say num_parts = 8. As initially constructed, the deque contains
// a single RcSlice spanning the entire original slice. To fulfill a
// call to next(), we subdivide as follows:
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
// In a loop, call RcSlice::split_off_left on the frontmost slice in the
// deque and push the returned slice onto the front of the deque. Do this
// until you've obtained a slice of the appropriate size to be yielded.
// Also, you can skip pushing this last slice onto the front of the
// deque since it can be yielded immediately. next_back() works the
// same way except it calls RcSlice::split_off_right on the backmost
// slice in the deque and pushes the returned slice onto the back.
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

impl<T> Iterator for RcSliceParts<T> {
    type Item = RcSlice<T>;

    fn next(&mut self) -> Option<RcSlice<T>> {
        if 0 == self.len() {
            None
        } else {
            debug_assert_ne!(0, self.deque.len(), "deque is nonempty when RcSliceParts not done iterating");
            let initial_cap = self.deque.capacity();
            let mut n = greatest_power_of_2_factor(self.num_parts - self.num_yielded_front);
            let len = self.len();
            while n > len { n >>= 1; }
            let mut item: Option<RcSlice<T>> = None;
            while n & 1 == 0 {
                if let Some(item) = item {
                    self.deque.push_front(item);
                }
                item = self.deque.front_mut().map(RcSlice::split_off_left);
                n >>= 1;
            }
            debug_assert_eq!(initial_cap, self.deque.capacity(), "deque doesn't need to re-allocate");
            self.num_yielded_front += 1;
            item.or_else(|| self.deque.pop_front())
        }
    }

    exact_size_hint!();
}

impl<T> DoubleEndedIterator for RcSliceParts<T> {
    fn next_back(&mut self) -> Option<RcSlice<T>> {
        // The exact mirror image of next(...).
        if 0 == self.len() {
            None
        } else {
            debug_assert_ne!(0, self.deque.len(), "deque is nonempty when RcSliceParts not done iterating");
            let initial_cap = self.deque.capacity();
            let mut n = greatest_power_of_2_factor(self.num_parts - self.num_yielded_back);
            let len = self.len();
            while n > len { n >>= 1; }
            let mut item: Option<RcSlice<T>> = None;
            while n & 1 == 0 {
                if let Some(item) = item {
                    self.deque.push_back(item);
                }
                item = self.deque.back_mut().map(RcSlice::split_off_right);
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

impl<T> FusedIterator for RcSliceParts<T> { }

impl<T> Clone for RcSliceParts<T> {
    fn clone(&self) -> Self {
        RcSliceParts {
            num_parts: self.num_parts,
            num_yielded_front: self.num_yielded_front,
            num_yielded_back: self.num_yielded_back,
            deque: self.deque.clone(),
        }
    }
}
