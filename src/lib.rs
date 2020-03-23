// #![deny(warnings, missing_debug_implementations, rust_2018_idioms)]

#![no_std]

extern crate alloc;

mod shared_slice;

use crate::shared_slice::SharedSlice;

pub struct ArcSlice<T> {
    start: *const T,
    end: *const T,
    shared: *const SharedSlice<T>,
}

impl<T> ArcSlice<T> {

}
