#![deny(rust_2018_idioms)]

#![no_std]

extern crate alloc;

#[macro_use]
mod internal;

pub mod rc;

// Re-export the core types...
pub use rc::{RcSlice, RcSliceMut};
