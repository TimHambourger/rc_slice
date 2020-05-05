extern crate rc_slice;

#[macro_use]
mod test_utils;

use std::{
    thread,
};
use rc_slice::ArcSlice;
use test_utils::{DroppedItemsSync, DropTracker};

is_covariant!(ArcSlice);

#[test]
fn drops_data_across_threads() {
    let dropped = DroppedItemsSync::new();
    let slice = ArcSlice::from_vec(vec![
        DropTracker("a", dropped.clone()),
        DropTracker("b", dropped.clone()),
        DropTracker("c", dropped.clone()),
    ]);
    let handle = thread::spawn(move || {
        assert_eq!(["a", "b", "c"], slice[..]);
    });
    handle.join().unwrap();
    assert_eq!(["a", "b", "c"], dropped.get_items()[..]);
}

#[test]
fn drops_only_when_no_strong_refs() {
    let dropped = DroppedItemsSync::new();
    let slice = ArcSlice::from_vec(vec![
        DropTracker("a", dropped.clone()),
        DropTracker("b", dropped.clone()),
        DropTracker("c", dropped.clone()),
    ]);
    let clone = slice.clone();
    let handle = thread::spawn(move || {
        assert_eq!(["a", "b", "c"], clone[..]);
        drop(clone); // To be very explicit that clone has been moved and dropped
    });
    handle.join().unwrap();
    assert_eq!(0, dropped.get_items().len());
    drop(slice);
    assert_eq!(["a", "b", "c"], dropped.get_items()[..]);
}

#[test]
fn drops_when_children_dropped() {
    let dropped = DroppedItemsSync::new();
    let dropped2 = dropped.clone();
    let mut slice = ArcSlice::from_vec(vec![
        DropTracker("a", dropped.clone()),
        DropTracker("b", dropped.clone()),
        DropTracker("c", dropped.clone()),
    ]);
    let left = ArcSlice::split_off_left(&mut slice);
    let handle = thread::spawn(move || {
        assert_eq!(["a"], left[..]);
        drop(left);
        assert!(dropped2.get_items().contains(&"a"));
    });
    handle.join().unwrap();
    assert_eq!(["a"], dropped.get_items()[..]);
    drop(slice);
    assert_eq!(["a", "b", "c"], dropped.get_items()[..]);
}

#[test]
fn parallel_split_into_parts_drop_at_end() {
    let dropped = DroppedItemsSync::new();
    let slice = ArcSlice::from_vec(vec![
        DropTracker("a", dropped.clone()),
        DropTracker("b", dropped.clone()),
        DropTracker("c", dropped.clone()),
        DropTracker("d", dropped.clone()),
        DropTracker("e", dropped.clone()),
        DropTracker("f", dropped.clone()),
        DropTracker("g", dropped.clone()),
        DropTracker("h", dropped.clone()),
    ]);
    let mut handles = Vec::new();
    for _ in 0..4 {
        let slice_clone = slice.clone();
        handles.push(thread::spawn(move || {
            let mut parts = ArcSlice::split_into_parts(slice_clone, 8);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert_eq!(["b"], parts.next().unwrap()[..]);
            assert_eq!(["c"], parts.next().unwrap()[..]);
            assert_eq!(["d"], parts.next().unwrap()[..]);
            assert_eq!(["e"], parts.next().unwrap()[..]);
            assert_eq!(["f"], parts.next().unwrap()[..]);
            assert_eq!(["g"], parts.next().unwrap()[..]);
            assert_eq!(["h"], parts.next().unwrap()[..]);
        }));
    }
    for handle in handles {
        handle.join().unwrap();
    }
    // Shouldn't have dropped anything yet b/c we've held onto the original
    // strong ref to slice this whole time.
    assert_eq!(0, dropped.get_items().len());
    drop(slice);
    // Now we've dropped
    assert_eq!(["a", "b", "c", "d", "e", "f", "g", "h"], dropped.get_items()[..]);
}

#[test]
fn parallel_split_into_parts_parallel_drop() {
    let dropped = DroppedItemsSync::new();
    let slice = ArcSlice::from_vec(vec![
        DropTracker("a", dropped.clone()),
        DropTracker("b", dropped.clone()),
        DropTracker("c", dropped.clone()),
        DropTracker("d", dropped.clone()),
        DropTracker("e", dropped.clone()),
        DropTracker("f", dropped.clone()),
        DropTracker("g", dropped.clone()),
        DropTracker("h", dropped.clone()),
    ]);
    let mut handles = Vec::new();
    for _ in 0..4 {
        let slice_clone = slice.clone();
        handles.push(thread::spawn(move || {
            let mut parts = ArcSlice::split_into_parts(slice_clone, 8);
            assert_eq!(["a"], parts.next().unwrap()[..]);
            assert_eq!(["b"], parts.next().unwrap()[..]);
            assert_eq!(["c"], parts.next().unwrap()[..]);
            assert_eq!(["d"], parts.next().unwrap()[..]);
            assert_eq!(["e"], parts.next().unwrap()[..]);
            assert_eq!(["f"], parts.next().unwrap()[..]);
            assert_eq!(["g"], parts.next().unwrap()[..]);
            assert_eq!(["h"], parts.next().unwrap()[..]);
        }));
    }
    // Drop our original strong ref to this slice early, before we've joined
    // all our spawned threads.
    drop(slice);
    for handle in handles {
        handle.join().unwrap();
    }
    // Now by the time all threads have completed, everything should be dropped.
    // Exact drop order is nondeterministic b/c of the parallelism above.
    assert_eq!(["a", "b", "c", "d", "e", "f", "g", "h"], dropped.get_sorted()[..]);
}
