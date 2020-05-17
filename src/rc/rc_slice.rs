use core::{
    cell::{Cell, UnsafeCell},
    iter::FusedIterator,
    marker::PhantomData,
    mem,
    ops::Deref,
    ptr::{self, NonNull},
    slice,
};
use alloc::{
    boxed::Box,
    rc::{Rc, Weak},
    vec::Vec,
};
use crate::{
    internal::{
        bin_parts_iter::{BinaryPartsIter, BinarySplitOff, SplitAsSlice},
        slice_model::SliceAlloc,
    },
    rc::RcSliceMut,
};

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
    phantom_item: PhantomData<T>,
    phantom_child: PhantomData<Self>,
}

/// Signals the presence of child RcSlices for the same data subslice.
struct IntoMutGuard {
    // Not used except implicitly in the fact that this IntoMutGuard
    // keeps its ancestors alive.
    _parent: Option<Rc<Self>>,
    left_child: UnsafeCell<Weak<Self>>,
    right_child: UnsafeCell<Weak<Self>>,
    // IntoMutGuard holds a strong ref to a GetMutGuard b/c any ref that
    // prevents into_mut also prevents get_mut.
    get_mut_guard: Rc<GetMutGuard>,
}

enum GetMutGuardChildType {
    Left,
    Right,
}

struct GetMutGuardParentage {
    parent: Rc<GetMutGuard>,
    // Is this GetMutGuard a left child or right child of its parent?
    child_type: GetMutGuardChildType,
}

struct GetMutGuard {
    parentage: Option<GetMutGuardParentage>,
    left_child: UnsafeCell<Weak<Self>>,
    right_child: UnsafeCell<Weak<Self>>,
    into_mut_guard: UnsafeCell<Weak<IntoMutGuard>>,
}

/// A reference counted slice that tracks reference counts per
/// subslice.
pub struct RcSlice<T> {
    data: Rc<RcSliceData<T>>,
    // Presence of a strong ref to a subslice prevents calling into_mut
    // on any ancestor subslice.
    into_mut_guard: Rc<IntoMutGuard>,
}

/// A weak reference to a reference counted slice. Comparable to
/// std::rc::Weak<[T]>.
pub struct WeakSlice<T> {
    data: Weak<RcSliceData<T>>,
    // Presence of a weak ref to a subslice prevents calling get_mut
    // (but not into_mut) on any ancestor subslice.
    get_mut_guard: Rc<GetMutGuard>,
}

/// A double-ended iterator over roughly-even subslices of a starting RcSlice.
pub struct RcSliceParts<T> {
    iter: BinaryPartsIter<RcSlice<T>>,
}

impl<T> RcSliceData<T> {
    fn from_boxed_slice(slice: Box<[T]>) -> Self {
        let len = slice.len();
        unsafe {
            // Waiting on stabilization of Box::into_raw_non_null
            let ptr = NonNull::new_unchecked(Box::into_raw(slice) as _);
            let alloc = if len == 0 { None } else { Some(Rc::new(SliceAlloc::new(ptr, len))) };
            Self::from_data_parts(ptr, len, alloc)
        }
    }

    pub (in crate::rc) unsafe fn from_data_parts(ptr: NonNull<T>, len: usize, alloc: Option<Rc<SliceAlloc<T>>>) -> Self {
        Self {
            ptr,
            len,
            alloc,
            left_child: Cell::new(None),
            right_child: Cell::new(None),
            phantom_item: PhantomData,
            phantom_child: PhantomData,
        }
    }

    fn clone_left(self: &Rc<Self>) -> Rc<Self> {
        let (ptr, len) = self.left_sub();
        unsafe {
            self.clone_child(&self.left_child, ptr, len)
        }
    }

    fn clone_right(self: &Rc<Self>) -> Rc<Self> {
        let (ptr, len) = self.right_sub();
        unsafe {
            self.clone_child(&self.right_child, ptr, len)
        }
    }

    unsafe fn clone_child(self: &Rc<Self>, child: &Cell<Option<NonNull<()>>>, ptr: NonNull<T>, len: usize) -> Rc<Self> {
        child.get().map_or_else(
            || {
                let alloc = if len == 0 { None } else { self.alloc.clone() };
                let new = Rc::new(Self::from_data_parts(ptr, len, alloc));
                let clone = new.clone();
                child.set(Some(NonNull::new_unchecked(Rc::into_raw(new) as _)));
                clone
            },
            |child| {
                let existing = Rc::from_raw(child.as_ptr() as *const Self);
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

    fn take_child(child: &mut Cell<Option<NonNull<()>>>) -> Option<Rc<Self>> {
        child.get_mut().take().map(|child| unsafe { Rc::from_raw(child.as_ptr() as *const Self) })
    }

    fn left_sub(&self) -> (NonNull<T>, usize) {
        (self.ptr, self.len >> 1)
    }

    fn right_sub(&self) -> (NonNull<T>, usize) {
        let ptr = if mem::size_of::<T>() == 0 {
            self.ptr
        } else {
            unsafe { NonNull::new_unchecked(self.ptr.as_ptr().add(self.len >> 1)) }
        };
        (ptr, self.len - (self.len >> 1))
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

macro_rules! into_mut_guard_clone_child_fn {
    ($child_method:ident, $child_field:ident) => {
        fn $child_method(self: &Rc<Self>) -> Rc<Self> {
            let child = unsafe { (*self.$child_field.get()).upgrade() };
            child.unwrap_or_else(|| {
                let get_mut_guard_child = self.get_mut_guard.$child_method();
                let child = Rc::new(Self {
                    _parent: Some(self.clone()),
                    left_child: UnsafeCell::new(Weak::new()),
                    right_child: UnsafeCell::new(Weak::new()),
                    get_mut_guard: get_mut_guard_child,
                });
                unsafe {
                    *child.get_mut_guard.into_mut_guard.get() = Rc::downgrade(&child);
                    *self.$child_field.get() = Rc::downgrade(&child);
                }
                child
            })
        }
    };
}

impl IntoMutGuard {
    fn new() -> Rc<Self> {
        let get_mut_guard = Rc::new(GetMutGuard {
            parentage: None,
            left_child: UnsafeCell::new(Weak::new()),
            right_child: UnsafeCell::new(Weak::new()),
            into_mut_guard: UnsafeCell::new(Weak::new()),
        });
        let into_mut_guard = Rc::new(Self {
            _parent: None,
            left_child: UnsafeCell::new(Weak::new()),
            right_child: UnsafeCell::new(Weak::new()),
            get_mut_guard,
        });
        unsafe { *into_mut_guard.get_mut_guard.into_mut_guard.get() = Rc::downgrade(&into_mut_guard) };
        into_mut_guard
    }

    into_mut_guard_clone_child_fn!(clone_left, left_child);
    into_mut_guard_clone_child_fn!(clone_right, right_child);
}

macro_rules! get_mut_guard_clone_child_fn {
    ($child_method:ident, $child_field:ident, $child_type:ident) => {
        fn $child_method(self: &Rc<Self>) -> Rc<Self> {
            let child = unsafe { (*self.$child_field.get()).upgrade() };
            child.unwrap_or_else(|| {
                let child = Rc::new(Self {
                    parentage: Some(GetMutGuardParentage { parent: self.clone(), child_type: GetMutGuardChildType::$child_type }),
                    left_child: UnsafeCell::new(Weak::new()),
                    right_child: UnsafeCell::new(Weak::new()),
                    into_mut_guard: UnsafeCell::new(Weak::new()),
                });
                unsafe { *self.$child_field.get() = Rc::downgrade(&child) };
                child
            })
        }
    };
}

impl GetMutGuard {
    fn new() -> Self {
        Self {
            parentage: None,
            left_child: UnsafeCell::new(Weak::new()),
            right_child: UnsafeCell::new(Weak::new()),
            into_mut_guard: UnsafeCell::new(Weak::new()),
        }
    }

    fn ensure_into_mut_guard(self: &Rc<Self>) -> Rc<IntoMutGuard> {
        let existing_guard = unsafe { (*self.into_mut_guard.get()).upgrade() };
        existing_guard.unwrap_or_else(|| match &self.parentage {
            Some(GetMutGuardParentage { parent, child_type }) => {
                let parent_into_mut_guard = parent.ensure_into_mut_guard();
                // Calling clone_left/clone_right on the parent IntoMutGuard also
                // ensures that the correct references are established btwn this
                // GetMutGuard and the new child IntoMutGuard.
                match child_type {
                    GetMutGuardChildType::Left => parent_into_mut_guard.clone_left(),
                    GetMutGuardChildType::Right => parent_into_mut_guard.clone_right(),
                }
            },
            None => {
                let guard = Rc::new(IntoMutGuard {
                    _parent: None,
                    left_child: UnsafeCell::new(Weak::new()),
                    right_child: UnsafeCell::new(Weak::new()),
                    get_mut_guard: self.clone(),
                });
                unsafe {
                    *self.into_mut_guard.get() = Rc::downgrade(&guard);
                }
                guard
            }
        })
    }

    get_mut_guard_clone_child_fn!(clone_left, left_child, Left);
    get_mut_guard_clone_child_fn!(clone_right, right_child, Right);
}

impl<T> RcSlice<T> {
    pub (in crate::rc) fn from_unique_data(data: Rc<RcSliceData<T>>) -> Self {
        Self { data, into_mut_guard: IntoMutGuard::new() }
    }

    pub fn from_boxed_slice(slice: Box<[T]>) -> Self {
        Self::from_unique_data(Rc::new(RcSliceData::from_boxed_slice(slice)))
    }

    pub fn from_vec(vec: Vec<T>) -> Self {
        Self::from_boxed_slice(vec.into_boxed_slice())
    }

    pub fn clone_left(this: &Self) -> Self {
        if this.data.len == 0 {
            this.clone()
        } else {
            let child_data = this.data.clone_left();
            let child_guard = this.into_mut_guard.clone_left();
            Self { data: child_data, into_mut_guard: child_guard }
        }
    }

    pub fn clone_right(this: &Self) -> Self {
        if this.data.len <= 1 {
            this.clone()
        } else {
            let child_data = this.data.clone_right();
            let child_guard = this.into_mut_guard.clone_right();
            Self { data: child_data, into_mut_guard: child_guard }
        }
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
        // We need to check for any RcSlices referencing ancestor
        // RcSliceDatas, and we need to check for any RcSlices
        // or WeakSlices referencing our own RcSliceData or any of its
        // descendants. We DON'T need to check for WeakSlices referencing
        // ancestor RcSliceDatas: RcSliceData strong refs go from parent to
        // child, so the only way any WeakSlice could still hold an active
        // reference to an ancestor RcSliceData would be if there was an
        // ancestor RcSlice around.
        let safe_to_mut =
            // We're the only strong ref to our data
            1 == Rc::strong_count(&this.data) &&
            // Our into_mut_guard holds the only strong ref to its get_mut_guard
            1 == Rc::strong_count(&this.into_mut_guard.get_mut_guard);
        if safe_to_mut {
            unsafe { Some(slice::from_raw_parts_mut((*this.data).ptr.as_ptr(), (*this.data).len)) }
        } else {
            None
        }
    }

    pub fn into_mut(this: Self) -> Result<RcSliceMut<T>, Self> {
        // Similar to get_mut. But now we don't care about WeakSlices at all:
        // As long as we're the only strong ref to our RcSliceData or any
        // RcSliceData overlapping it, the act of converting that RcSliceData
        // into an RcSliceMut will invalidate any overlapping WeakSlices. This
        // is the same reason Rc::try_unwrap only cares about strong refs.
        if 1 == Rc::strong_count(&this.into_mut_guard) {
            let RcSlice { data, into_mut_guard } = this;
            Rc::try_unwrap(data)
                .map(|data| unsafe { data.into_mut() })
                .map_err(|data| RcSlice { data, into_mut_guard })
        } else {
            Err(this)
        }
    }

    pub fn downgrade(this: &Self) -> WeakSlice<T> {
        WeakSlice { data: Rc::downgrade(&this.data), get_mut_guard: this.into_mut_guard.get_mut_guard.clone() }
    }

    // TODO: unsplit
    // TODO: make_mut
    // TODO: into_boxed_slice, into_vec
}

impl<T> Clone for RcSlice<T> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            into_mut_guard: self.into_mut_guard.clone(),
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
debug_as_slice!(RcSlice);
hash_as_slice!(RcSlice);
from_iter_via_vec!(RcSlice);

impl<T> WeakSlice<T> {
    /// Constructs a new `WeakSlice<T>` such that calling `upgrade` on the
    /// return value always gives `None`.
    pub fn new() -> Self {
        Self { data: Weak::new(), get_mut_guard: Rc::new(GetMutGuard::new()) }
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
        self.data.upgrade().map(|data| RcSlice {
            data,
            into_mut_guard: self.get_mut_guard.ensure_into_mut_guard()
        })
    }
}

impl<T> Clone for WeakSlice<T> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            get_mut_guard: self.get_mut_guard.clone()
        }
    }
}

impl<T> BinarySplitOff for RcSlice<T> {
    #[inline]
    fn split_off_left(this: &mut Self) -> Self { RcSlice::split_off_left(this) }
    #[inline]
    fn split_off_right(this: &mut Self) -> Self { RcSlice::split_off_right(this) }
}

unsafe impl<T> SplitAsSlice<T> for RcSlice<T> { }

impl<T> RcSliceParts<T> {
    #[inline]
    fn new(slice: RcSlice<T>, num_parts: usize) -> Self {
        Self { iter: BinaryPartsIter::new(slice, num_parts) }
    }

    /// Reference the remaining items in the iterator as a single slice.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self.iter.as_slice()
    }
}

impl<T> ExactSizeIterator for RcSliceParts<T> {
    #[inline]
    fn len(&self) -> usize { self.iter.len() }
}

impl<T> Iterator for RcSliceParts<T> {
    type Item = RcSlice<T>;

    #[inline]
    fn next(&mut self) -> Option<RcSlice<T>> { self.iter.next() }
    exact_size_hint!();
    exact_count!();
}

impl<T> DoubleEndedIterator for RcSliceParts<T> {
    #[inline]
    fn next_back(&mut self) -> Option<RcSlice<T>> { self.iter.next_back() }
}

impl<T> FusedIterator for RcSliceParts<T> { }

impl<T> Clone for RcSliceParts<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self { iter: self.iter.clone() }
    }
}

debug_as_parts_iter!(RcSliceParts);
