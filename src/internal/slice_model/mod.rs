use core::{
    mem,
    ptr::NonNull,
};
use alloc::boxed::Box;

mod slice_alloc;
mod slice_items;

pub use slice_alloc::SliceAlloc;
pub use slice_items::{
    SliceItems,
    SliceItemsIter,
    SliceItemsParts,
};

/// Split a boxed slice into an optional SliceAlloc and a SliceItems.
/// The SliceAlloc is optional to represent cases where the input
/// slice requires no allocation (i.e. consumes 0 memory). This function
/// is unsafe because calling code must ensure that whenever a SliceAlloc
/// is returned, then that SliceAlloc strictly outlives the returned
/// SliceItems. Otherwise, any attempt to read or mutate any item in the
/// SliceItems (including any attempt to drop any of the items) will result
/// in a read-after-free.
// NOTE: Ordering of elements in the returned tuple is so alloc will correctly
// get dropped after items if you do no destructuring of the return value.
// See https://github.com/rust-lang/rfcs/blob/master/text/1857-stabilize-drop-order.md
pub unsafe fn split_alloc_from_items<T>(slice: Box<[T]>) -> (SliceItems<T>, Option<SliceAlloc<T>>) {
    let len = slice.len();
    // Waiting on stabilization of Box::into_raw_non_null
    let ptr = NonNull::new_unchecked(Box::into_raw(slice) as _);
    let alloc = if len == 0 || mem::size_of::<T>() == 0 {
        None
    } else {
        Some(SliceAlloc::new(ptr, len))
    };
    let items = SliceItems::new(ptr, len);
    (items, alloc)
}

#[cfg(test)]
mod test {
    #[test]
    fn split_alloc_from_items_correct_usage() {
        let v = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        // Hold onto both alloc and items
        let (_items0, _alloc) = unsafe { super::split_alloc_from_items(v.into_boxed_slice()) };
        // Move items to a new variable to ensure that it gets dropped before alloc.
        let _items = _items0;
        // Doing another allocation here is just fine, unlike in the incorrect
        // usage example below.
        let _just_fine = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        // Implicitly drop items
        // Implicitly drop alloc
    }

    // THIS TEST CRASHES THE PROCESS! Keeping it here to document that
    // misuse of split_alloc_from_items does indeed lead to memory
    // unsafety.
    #[test]
    #[ignore = "This test crashes the process!"]
    fn split_alloc_from_items_crashy_usage() {
        let v = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        // Immediately drop alloc but hold onto items
        let (_items, _) = unsafe { super::split_alloc_from_items(v.into_boxed_slice()) };
        // Doing another allocation here seems to be needed to expose the
        // issue, at least on my old (mid-2012!) Mackbook Pro.
        let _uh_oh = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        // Implicitly drop items... But ack! We already dropped alloc above.
        // For me this gives
        //   rc_slice-23fd62d2e8f777d9(44234,0x700008f8b000) malloc: *** error for object 0x7ffa48e006e0: pointer being freed was not allocated
        //   *** set a breakpoint in malloc_error_break to debug
    }
}
