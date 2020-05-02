#![deny(rust_2018_idioms)]

#![cfg_attr(not(test), no_std)]

extern crate alloc;

#[macro_use]
mod internal;

pub mod arc;
pub mod rc;

// Re-export the core types...
pub use arc::{ArcSlice, ArcSliceMut};
pub use rc::{RcSlice, RcSliceMut};
