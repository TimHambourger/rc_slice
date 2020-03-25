// #![deny(warnings, missing_debug_implementations, rust_2018_idioms)]

#![no_std]

extern crate alloc;

pub mod rc;

pub use rc::RcSlice;
