mod rc_slice;
mod rc_slice_mut;

pub use self::rc_slice::{RcSlice, RcSliceParts, WeakSlice};
pub use rc_slice_mut::{RcSliceMut, RcSliceMutIter};
