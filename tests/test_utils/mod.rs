// The compiler warns about methods in structs in this module w/o this, I
// think b/c it re-does the dead code analysis per integration test, and
// indeed not all methods are used in every integration test.
#![allow(dead_code)]

use std::{
    cell::RefCell,
    sync::{Arc, RwLock},
};

pub trait AcceptStr {
    fn accept(&self, s: &'static str);
}

#[derive(Debug)]
pub struct DroppedItems(RefCell<Vec<&'static str>>);
#[derive(Clone, Debug)]
pub struct DroppedItemsSync(Arc<RwLock<Vec<&'static str>>>);

impl DroppedItems {
    pub fn new() -> Self {
        Self(RefCell::new(Vec::new()))
    }

    /// Get a cloned vector of all items currently in the collection.
    pub fn get_items(&self) -> Vec<&'static str> {
        self.0.borrow().clone()
    }

    pub fn reset(&self) {
        self.0.borrow_mut().clear();
    }
}

impl DroppedItemsSync {
    pub fn new() -> Self {
        Self(Arc::new(RwLock::new(Vec::new())))
    }

    /// Get a cloned vector of all items currently in the collection.
    pub fn get_items(&self) -> Vec<&'static str> {
        self.0.read().unwrap().clone()
    }

    /// Get a sorted vector of all items currently in the collection.
    /// The collection is cloned before sorting. The underlying
    /// collection is not modified.
    pub fn get_sorted(&self) -> Vec<&'static str> {
        let mut d = self.get_items();
        d.sort_unstable();
        d
    }

    pub fn reset(&self) {
        self.0.write().unwrap().clear();
    }
}

impl AcceptStr for DroppedItems {
    fn accept(&self, s: &'static str) {
        self.0.borrow_mut().push(s);
    }
}

impl AcceptStr for DroppedItemsSync {
    fn accept(&self, s: &'static str) {
        self.0.write().unwrap().push(s);
    }
}

impl <T: AcceptStr> AcceptStr for &T {
    fn accept(&self, s: &'static str) {
        (*self).accept(s);
    }
}

#[derive(Clone, Debug)]
pub struct DropTracker<D: AcceptStr>(pub &'static str, pub D);

impl<D: AcceptStr> Drop for DropTracker<D> {
    fn drop(&mut self) {
        self.1.accept(self.0);
    }
}

// This enables nice assertions on the contents of a [DropTracker<_>]
impl<D: AcceptStr> PartialEq<DropTracker<D>> for &str {
    fn eq(&self, other: &DropTracker<D>) -> bool {
        *self == other.0
    }
}

// Not planning to do many tests as macros since it obscures where any
// assertion failures are. But this one makes a good macro since it's
// just about making sure the test compiles.
macro_rules! is_covariant {
    ($struct:ident) => {
        #[test]
        fn is_covariant() {
            #[allow(unused_variables)]
            fn use_slice<'a>(n: &'a u32, slice: &$struct<&'a u32>) {
            }

            let slice = $struct::from_vec(vec![&0]);
            // Important that x is declared after slice.
            let x = 0;
            // If $struct<T> were invariant in T, then the next line would give an error like
            // error[E0597]: `x` does not live long enough
            //   --> tests/test_rc_slice_mut.rs:35:15
            //    |
            // 35 |     use_slice(&x, &slice)
            //    |               ^^ borrowed value does not live long enough
            // 36 | }
            //    | -
            //    | |
            //    | `x` dropped here while still borrowed
            //    | borrow might be used here, when `slice` is dropped and runs the destructor for type `rc_slice::RcSliceMut<&u32>`
            //    |
            //    = note: values in a scope are dropped in the opposite order they are defined
            use_slice(&x, &slice)
        }
    };
}
