use core::sync::atomic::{AtomicBool, Ordering};

/// A simple syncrhonization primitive.
pub struct Gate {
    is_closed: AtomicBool,
}

pub struct Latch<'a>(&'a Gate);

impl Gate {
    pub fn new() -> Self {
        Self { is_closed: AtomicBool::new(false) }
    }

    pub fn wait_till_open(&self) {
        while self.is_closed.load(Ordering::SeqCst) {}
    }

    pub fn try_close(&self) -> Option<Latch<'_>> {
        if self.is_closed.swap(true, Ordering::SeqCst) {
            None
        } else {
            Some(Latch(self))
        }
    }
}

impl<'a> Drop for Latch<'a> {
    fn drop(&mut self) {
        self.0.is_closed.store(false, Ordering::SeqCst)
    }
}
