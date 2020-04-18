use std::{
    cell::RefCell,
    sync::{Arc, Mutex},
};

#[derive(Debug)]
#[derive(Clone)]
pub struct DropTracker<'a>(pub &'static str, pub &'a RefCell<Vec<&'static str>>);

impl<'a> Drop for DropTracker<'a> {
    fn drop(&mut self) {
        self.1.borrow_mut().push(self.0);
    }
}

// This enables nice assertions on the contents of a [DropTracker<'_>]
impl<'a> PartialEq<DropTracker<'a>> for &str {
    fn eq(&self, other: &DropTracker<'a>) -> bool {
        *self == other.0
    }
}

#[derive(Debug)]
#[derive(Clone)]
pub struct ThreadSafeDropTracker(pub &'static str, pub Arc<Mutex<Vec<&'static str>>>);

impl Drop for ThreadSafeDropTracker {
    fn drop(&mut self) {
        self.1.lock().unwrap().push(self.0);
    }
}

impl PartialEq<ThreadSafeDropTracker> for &str {
    fn eq(&self, other: &ThreadSafeDropTracker) -> bool {
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
