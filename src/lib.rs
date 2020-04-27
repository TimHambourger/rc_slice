#![deny(rust_2018_idioms)]

#![no_std]

extern crate alloc;

#[cfg(test)]
#[macro_use]
extern crate std;

#[macro_use]
mod internal;

pub mod arc;
pub mod rc;

// Re-export the core types...
pub use arc::{ArcSlice, ArcSliceMut};
pub use rc::{RcSlice, RcSliceMut};
