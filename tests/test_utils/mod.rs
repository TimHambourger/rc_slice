use std::cell::RefCell;

#[derive(Debug)]
pub struct DropTracker<'a>(pub &'static str, pub &'a RefCell<Vec<&'static str>>);

impl<'a> Drop for DropTracker<'a> {
    fn drop(&mut self) {
        self.1.borrow_mut().push(self.0);
    }
}
