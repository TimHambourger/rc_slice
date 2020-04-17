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
