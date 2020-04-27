use core::{
    iter::FusedIterator,
    marker::PhantomData,
    mem,
    ops::Deref,
    ptr::{self, NonNull},
    slice,
    sync::atomic::{AtomicPtr, Ordering},
};
use alloc::{
    boxed::Box,
    sync::{Arc, Weak},
    vec::Vec,
};
use crate::{
    internal::{
        bin_parts_iter::{BinaryPartsIter, BinarySplitOff, SplitAsSlice},
        gate::Gate,
        slice_model::SliceAlloc,
    },
    arc::ArcSliceMut,
};

// Relationships btwn ArcSlice, ArcSliceData, and DataGuard mirror those
// from crate::rc.

#[derive(Debug)]
pub (in crate::arc) struct ArcSliceData<T> {
    ptr: NonNull<T>,
    len: usize,
    // An Option b/c we'll let this be None for length zero subslices. They
    // don't need an underlying allocation.
    alloc: Option<Arc<SliceAlloc<T>>>,
    // Really AtomicPtr<Self> where the pointer is obtained via
    // Arc<Self>::into_raw(). But we need ArcSliceData<T> to be convariant
    // in T.
    left_child: AtomicPtr<()>,
    // Ditto left_child on really AtomicPtr<Self>
    right_child: AtomicPtr<()>,
    parent: Weak<Self>,
    // Obtained via Box<Weak<DataGuard>>::into_raw(). Could instead do this
    // as an AtomicPtr<DataGuard> obtained via Weak<DataGuard>::into_raw(),
    // but avoiding using of unstable Weak::into_raw.
    guard: AtomicPtr<Weak<DataGuard>>,
    phantom_item: PhantomData<T>,
    phantom_child: PhantomData<Self>,
}

/// Signals the presence of child ArcSlices or WeakSlices for the same
/// data subslice. Part of detecting which mutations are possible.
#[derive(Debug)]
struct DataGuard {
    // Not used except in the fact that a child DataGuard keeps its parent
    // DataGuard alive.
    _parent: Option<Arc<Self>>,
    // A Gate controlling whether clone_left and clone_right are allowed
    clone_child_gate: Gate,
    // A Gate controlling whether downgrade is allowed
    downgrade_gate: Gate,
}

/// An atomically reference counted slice that tracks reference counts
/// per subslice.
#[derive(Debug)]
pub struct ArcSlice<T> {
    data: Arc<ArcSliceData<T>>,
    data_guard: Arc<DataGuard>,
}

/// A weak reference to an atomically reference counted slice. Comparable
/// to std::sync::Weak<[T]>.
#[derive(Debug)]
pub struct WeakSlice<T> {
    data: Weak<ArcSliceData<T>>,
    // Not used except as part of signaling the presence of WeakSlices to ArcSlice:;get_mut
    _data_guard: Weak<DataGuard>,
}

/// A double-ended iterator over roughly-even subslices of a starting ArcSlice.
#[derive(Debug)]
pub struct ArcSliceParts<T> {
    iter: BinaryPartsIter<ArcSlice<T>>,
}

impl<T> ArcSliceData<T> {
    fn from_boxed_slice(slice: Box<[T]>) -> Self {
        assert_ne!(0, mem::size_of::<T>(), "TODO: Support ZSTs");
        let len = slice.len();
        unsafe {
            // Waiting on stabilization of Box::into_raw_non_null
            let ptr = NonNull::new_unchecked(Box::into_raw(slice) as _);
            let alloc = if len == 0 { None } else { Some(Arc::new(SliceAlloc::new(ptr, len))) };
            Self::from_data_parts(ptr, len, alloc)
        }
    }

    pub (in crate::arc) unsafe fn from_data_parts(ptr: NonNull<T>, len: usize, alloc: Option<Arc<SliceAlloc<T>>>) -> Self {
        Self::with_data_and_parent(ptr, len, alloc, Weak::new())
    }

    fn with_data_and_parent(ptr: NonNull<T>, len: usize, alloc: Option<Arc<SliceAlloc<T>>>, parent: Weak<Self>) -> Self {
        let guard = AtomicPtr::new(Box::into_raw(Box::new(Weak::new())) as _);
        Self {
            ptr,
            len,
            alloc,
            parent,
            left_child: AtomicPtr::default(),
            right_child: AtomicPtr::default(),
            guard,
            phantom_item: PhantomData,
            phantom_child: PhantomData,
        }
    }

    fn clone_left(self: &Arc<Self>) -> Arc<Self> {
        if self.len == 0 {
            self.clone()
        } else {
            let (ptr, len) = self.left_sub();
            unsafe {
                self.clone_child(&self.left_child, ptr, len)
            }
        }
    }

    fn clone_right(self: &Arc<Self>) -> Arc<Self> {
        if self.len <= 1 {
            self.clone()
        } else {
            let (ptr, len) = self.right_sub();
            unsafe {
                self.clone_child(&self.right_child, ptr, len)
            }
        }
    }

    unsafe fn clone_child(self: &Arc<Self>, child: &AtomicPtr<()>, ptr: NonNull<T>, len: usize) -> Arc<Self> {
        let cur_child = child.load(Ordering::Acquire);
        if cur_child.is_null() {
            // Observed the child ptr as being null. Try to construct a new child and
            // swap into place.
            let alloc = if len == 0 { None } else { self.alloc.clone() };
            let new_child = Arc::new(Self::with_data_and_parent(ptr, len, alloc, Arc::downgrade(self)));
            let clone = new_child.clone();
            let new_child = Arc::into_raw(new_child);
            let prev_child = child.compare_and_swap(ptr::null_mut(), new_child as _, Ordering::AcqRel);
            if prev_child.is_null() {
                // Swapping new child in succeeded. Return clone of new child.
                clone
            } else {
                // Uh oh! Failed to swap in new child. We must've just lost a race
                // to clone this child. prev_child is the child that just won the race.
                let prev_child = Arc::from_raw(prev_child as *const Self);
                let clone = prev_child.clone();
                mem::forget(prev_child);
                // Reconstitute our new_child in order to drop it
                Arc::from_raw(new_child);
                clone
            }
        } else {
            // Observed the child ptr as being non-null. Just clone the underlying Arc.
            let cur_child = Arc::from_raw(cur_child as *const Self);
            let clone = cur_child.clone();
            mem::forget(cur_child);
            clone
        }
    }

    fn take_left(&mut self) -> Option<Arc<Self>> {
        Self::take_child(&mut self.left_child)
    }

    fn take_right(&mut self) -> Option<Arc<Self>> {
        Self::take_child(&mut self.right_child)
    }

    fn take_child(child: &mut AtomicPtr<()>) -> Option<Arc<Self>> {
        let child = child.swap(ptr::null_mut(), Ordering::AcqRel);
        if child.is_null() {
            None
        } else {
            unsafe { Some(Arc::from_raw(child as *const Self)) }
        }
    }

    fn left_sub(&self) -> (NonNull<T>, usize) {
        (self.ptr, self.len >> 1)
    }

    fn right_sub(&self) -> (NonNull<T>, usize) {
        // TODO: Support ZSTs
        (unsafe { NonNull::new_unchecked(self.ptr.as_ptr().offset((self.len >> 1) as isize)) }, self.len - (self.len >> 1))
    }

    /// Convert this ArcSliceData into an ArcSliceMut. Unsafe b/c calling
    /// code must ensure that there are no strong refs to any other ArcSliceData
    /// overlapping this one.
    unsafe fn into_mut(mut self) -> ArcSliceMut<T> {
        let slice_mut = ArcSliceMut::from_raw_parts(self.ptr, self.len, self.alloc.take());
        // We don't want to drop the items in this subslice when self gets dropped,
        // b/c we've transferred their ownership to slice_mut. But we DO wanna drop
        // things like our strong refs to our child datas, ref cells with the weak
        // refs to our data guards, etc, to avoid leaking all that.
        self.forget_items();
        slice_mut
    }

    fn forget_items(&mut self) {
        // Recursively tell left child to forget its items
        self.take_left().map(|child| Arc::try_unwrap(child).map(|mut child| child.forget_items()));
        // Recursively tell right child to forget its items
        self.take_right().map(|child| Arc::try_unwrap(child).map(|mut child| child.forget_items()));
        // Setting len to 0 turns our Drop impl into a no-op.
        self.len = 0;
    }
}

impl<T> Drop for ArcSliceData<T> {
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

impl<T> Deref for ArcSliceData<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
}

impl DataGuard {
    fn guard<T>(data: &ArcSliceData<T>) -> Arc<Self> {
        let mut existing_guard_ptr = data.guard.load(Ordering::Acquire);
        // We guarantee that ArcSliceData.guard is always a valid pointer
        let mut existing_guard = unsafe { (*existing_guard_ptr).upgrade() };
        while existing_guard.is_none() {
            // No reference to a live existing guard. We'll try constructing
            // a new guard as we do for RcSliceData and then atomically
            // swapping the new guard into place.
            let parent_guard = data.parent.upgrade()
                .map(|parent_data| Self::guard(&parent_data));
            let guard = Arc::new(Self {
                _parent: parent_guard,
                clone_child_gate: Gate::new(),
                downgrade_gate: Gate::new(),
            });
            let guard_ptr = Box::into_raw(Box::new(Arc::downgrade(&guard)));
            let prev_guard_ptr = data.guard.compare_and_swap(existing_guard_ptr, guard_ptr, Ordering::AcqRel);
            if prev_guard_ptr == existing_guard_ptr {
                // Swap succeeded. Set existing_guard to the guard we just
                // successfully created to exit the loop.
                existing_guard = Some(guard);
            } else {
                // Uh oh! Swap failed. We must've just lost a race to guard this
                // slice data. Reconstitue our guard_ptr to drop it, then keep
                // looping until we manage to observe a live existing guard.
                unsafe { Box::from_raw(guard_ptr); }
                existing_guard_ptr = prev_guard_ptr;
                existing_guard = unsafe { (*existing_guard_ptr).upgrade() };
            }
        }
        existing_guard.unwrap_or_else(|| unreachable!())
    }
}

impl<T> ArcSlice<T> {
    pub (in crate::arc) fn from_data(data: Arc<ArcSliceData<T>>) -> Self {
        let data_guard = DataGuard::guard(&data);
        Self { data, data_guard }
    }

    pub fn from_boxed_slice(slice: Box<[T]>) -> Self {
        Self::from_data(Arc::new(ArcSliceData::from_boxed_slice(slice)))
    }

    pub fn from_vec(vec: Vec<T>) -> Self {
        Self::from_boxed_slice(vec.into_boxed_slice())
    }

    pub fn clone_left(this: &Self) -> Self {
        this.clone_child_gate().wait_till_open();
        Self::from_data(this.data.clone_left())
    }

    pub fn clone_right(this: &Self) -> Self {
        this.clone_child_gate().wait_till_open();
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

    pub fn split_into_parts(this: Self, num_parts: usize) -> ArcSliceParts<T> {
        ArcSliceParts::new(this, num_parts)
    }

    pub fn get_mut(this: &mut Self) -> Option<&mut [T]> {
        // We do the same basic checks as RcSlice::get_mut, but we also have to
        // avoid race conditions while doing so. We solve this w/ short-lived locks.
        // TODO: Ack! Descendant WeakSlices create unsoundness here for the same
        // reason they do w/ RcSlice::get_mut. Refactor!

        // Check for no weak refs first.
        this.downgrade_gate().try_close().and_then(|_downgrade_latch|
            if 1 == Arc::weak_count(&this.data_guard) {
                this.clone_child_gate().try_close().and_then(|_clone_child_latch|
                    if 1 == Arc::strong_count(&this.data_guard) {
                        if 1 == Arc::strong_count(&this.data) {
                            // Safe to mutate
                            unsafe { Some(slice::from_raw_parts_mut((*this.data).ptr.as_ptr(), (*this.data).len)) }
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                )
            } else {
                None
            }
        )
    }

    pub fn into_mut(this: Self) -> Result<ArcSliceMut<T>, Self> {
        // We do the same basic checks as RcSlice::into_mut, but as w/
        // get_mut above, we need to do locking to avoid race conditions.

        let ArcSlice { data, data_guard } = this;
        let slice_mut = match (*data_guard).clone_child_gate.try_close() {
            Some(_clone_child_latch) => {
                if 1 == Arc::strong_count(&data_guard) {
                    Arc::try_unwrap(data).map(|data| unsafe { data.into_mut() })
                } else {
                    Err(data)
                }
            },
            None => Err(data)
        };
        slice_mut.map_err(|data| ArcSlice { data, data_guard })
    }

    pub fn downgrade(this: &Self) -> WeakSlice<T> {
        this.downgrade_gate().wait_till_open();
        WeakSlice { data: Arc::downgrade(&this.data), _data_guard: Arc::downgrade(&this.data_guard) }
    }

    // TODO: unsplit
    // TODO: make_mut
    // TODO: into_boxed_slice, into_vec

    fn clone_child_gate(&self) -> &Gate {
        &(*self.data_guard).clone_child_gate
    }

    fn downgrade_gate(&self) -> &Gate {
        &(*self.data_guard).downgrade_gate
    }
}

impl<T> Clone for ArcSlice<T> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            data_guard: self.data_guard.clone(),
        }
    }
}

impl<T> Deref for ArcSlice<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &self.data
    }
}

impl<T> From<Box<[T]>> for ArcSlice<T> {
    fn from(slice: Box<[T]>) -> Self {
        Self::from_boxed_slice(slice)
    }
}

impl<T> From<Vec<T>> for ArcSlice<T> {
    fn from(vec: Vec<T>) -> Self {
        Self::from_vec(vec)
    }
}

impl<T> From<ArcSliceMut<T>> for ArcSlice<T> {
    fn from(slice_mut: ArcSliceMut<T>) -> Self {
        ArcSliceMut::into_immut(slice_mut)
    }
}

borrow_as_slice!(ArcSlice);
compare_as_slice!(ArcSlice);
hash_as_slice!(ArcSlice);
from_iter_via_vec!(ArcSlice);

impl<T> WeakSlice<T> {
    /// Constructs a new `WeakSlice<T>`, without allocating any memory.
    /// Calling `upgrade` on the return value always gives `None`.
    pub fn new() -> Self {
        Self { data: Weak::new(), _data_guard: Weak::new() }
    }

    pub fn upgrade(&self) -> Option<ArcSlice<T>> {
        // TODO: This suffers from the same limitations as
        // crate::rc::WeakSlice::upgrade does.
        self.data.upgrade().map(ArcSlice::from_data)
    }
}

impl<T> Clone for WeakSlice<T> {
    fn clone(&self) -> Self {
        Self { data: self.data.clone(), _data_guard: self._data_guard.clone() }
    }
}

impl<T> BinarySplitOff for ArcSlice<T> {
    #[inline]
    fn split_off_left(this: &mut Self) -> Self { ArcSlice::split_off_left(this) }
    #[inline]
    fn split_off_right(this: &mut Self) -> Self { ArcSlice::split_off_right(this) }
}

unsafe impl<T> SplitAsSlice<T> for ArcSlice<T> { }

impl<T> ArcSliceParts<T> {
    #[inline]
    fn new(slice: ArcSlice<T>, num_parts: usize) -> Self {
        Self { iter: BinaryPartsIter::new(slice, num_parts) }
    }

    /// Reference the remaining items in the iterator as a single slice.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self.iter.as_slice()
    }
}

impl<T> ExactSizeIterator for ArcSliceParts<T> {
    #[inline]
    fn len(&self) -> usize { self.iter.len() }
}

impl<T> Iterator for ArcSliceParts<T> {
    type Item = ArcSlice<T>;

    #[inline]
    fn next(&mut self) -> Option<ArcSlice<T>> { self.iter.next() }
    exact_size_hint!();
}

impl<T> DoubleEndedIterator for ArcSliceParts<T> {
    #[inline]
    fn next_back(&mut self) -> Option<ArcSlice<T>> { self.iter.next_back() }
}

impl<T> FusedIterator for ArcSliceParts<T> { }

impl<T> Clone for ArcSliceParts<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self { iter: self.iter.clone() }
    }
}
