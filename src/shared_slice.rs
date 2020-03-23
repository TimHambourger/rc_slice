use core::{isize, mem, ptr};
use core::sync::atomic::{self, AtomicBool, AtomicPtr, AtomicUsize, Ordering};

use alloc::boxed::Box;

// Blatantly borrowing the finer points from std's Arc impl. From std:
//
/// A soft limit on the amount of references that may be made to an `Arc`.
///
/// Going above this limit will abort your program (although not
/// necessarily) at _exactly_ `MAX_REFCOUNT + 1` references.
const MAX_REFCOUNT: usize = (isize::MAX) as usize;

#[derive(Debug)]
pub struct SharedSlice<T> {
    start: *const T,
    end: *const T,
    ref_cnt: AtomicUsize,
    parent: AtomicPtr<SharedSlice<T>>,
    left_child: AtomicPtr<SharedSlice<T>>,
    right_child: AtomicPtr<SharedSlice<T>>,
    drop_started: AtomicBool,
}

impl<T> SharedSlice<T> {
    /// Unsafe b/c start and end must be non-null and aligned,
    /// start must be <= end, and none of the slice between start
    /// inclusive and end exclusive can have been freed already.
    pub unsafe fn new(start: *const T, end: *const T) -> Self {
        Self::new_with_parent(start, end, ptr::null_mut())
    }

    unsafe fn new_with_parent(start: *const T, end: *const T, parent: *mut Self) -> Self {
        assert_ne!(0, mem::size_of::<T>(), "TODO: Support ZSTs");
        SharedSlice {
            start,
            end,
            ref_cnt: AtomicUsize::new(1),
            parent: AtomicPtr::new(parent),
            left_child: AtomicPtr::new(ptr::null_mut()),
            right_child: AtomicPtr::new(ptr::null_mut()),
            drop_started: AtomicBool::new(false)
        }
    }

    pub fn inc_ref(&self) {
        // Relaxed and comparing old_size w/ MAX_REFCOUNT taken from std::Arc::clone.
        let old_size = self.ref_cnt.fetch_add(1, Ordering::Relaxed);
        assert!(old_size <= MAX_REFCOUNT, "References exceeded max refcount");
    }

    pub unsafe fn add_left_child(&self, end: *const T) -> *const Self {
        self.add_child(&self.left_child, self.start, end)
    }

    pub unsafe fn add_right_child(&self, start: *const T) -> *const Self {
        self.add_child(&self.right_child, start, self.end)
    }

    unsafe fn add_child(&self, child_ptr: &AtomicPtr<Self>, child_start: *const T, child_end: *const T) -> *const Self {
        let mut old_child = child_ptr.load(Ordering::Acquire);
        if old_child.is_null() {
            let new_child = Box::new(Self::new_with_parent(child_start, child_end, self as *const _ as _));
            let new_child = Box::into_raw(new_child);
            old_child = child_ptr.compare_and_swap(ptr::null::<Self>() as *mut _, new_child, Ordering::AcqRel);
            if old_child.is_null() {
                new_child
            } else {
                // Oops. Concurrent add_child call. Use old_child instead.
                (*old_child).inc_ref();
                // Drop new_child.
                let _ = Box::from_raw(new_child);
                old_child
            }
        } else {
            (*old_child).inc_ref();
            old_child
        }
    }

    pub fn dec_ref(&self) {
        // Decrement own count
        if self.ref_cnt.fetch_sub(1, Ordering::Acquire) == 1 {
            // Check parrent
            let parent = self.parent.load(Ordering::Acquire);
            if !parent.is_null() {
                
            }
        }
    }
}
