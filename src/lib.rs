// #![deny(warnings, missing_debug_implementations, rust_2018_idioms)]

#![no_std]

extern crate alloc;

mod internal;
pub mod rc;

// Re-export the core types...
pub use rc::{RcSlice, RcSliceMut};
