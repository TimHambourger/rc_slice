extern crate rc_slice;

#[macro_use]
mod test_utils;

use std::{
    collections::hash_map::HashMap,
};

use rc_slice::RcSliceMut;
use test_utils::{DroppedItems, DropTracker};

is_covariant!(RcSliceMut);

#[test]
fn drops_its_data() {
    let dropped = DroppedItems::new();
    RcSliceMut::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    assert_eq!(["a", "b", "c"], dropped.get_items()[..]);
}

#[test]
fn derefs_to_slice() {
    let slice_mut = RcSliceMut::from_vec(vec![0, 1, 2, 3]);
    assert_eq!([0, 1, 2, 3], slice_mut[..]);
}

#[test]
fn split_off_left_derefs_to_subslice() {
    let mut slice_mut = RcSliceMut::from_vec(vec![0, 1, 2, 3, 4]);
    let left = RcSliceMut::split_off_left(&mut slice_mut);
    assert_eq!([0, 1], left[..]);
    assert_eq!([2, 3, 4], slice_mut[..]);
}

#[test]
fn split_off_right_derefs_to_subslice() {
    let mut slice_mut = RcSliceMut::from_vec(vec![0, 1, 2, 3]);
    let right = RcSliceMut::split_off_right(&mut slice_mut);
    assert_eq!([0, 1], slice_mut[..]);
    assert_eq!([2, 3], right[..]);
}

#[test]
fn split_off_left_on_length_one_slice() {
    let mut slice_mut = RcSliceMut::from_vec(vec![0]);
    let left = RcSliceMut::split_off_left(&mut slice_mut);
    assert_eq!(0, left.len());
    assert_eq!([0], slice_mut[..]);
}

#[test]
fn split_off_right_on_length_one_slice() {
    let mut slice_mut = RcSliceMut::from_vec(vec![0]);
    let right = RcSliceMut::split_off_right(&mut slice_mut);
    assert_eq!(0, slice_mut.len());
    assert_eq!([0], right[..]);
}

#[test]
fn split_off_left_on_length_zero_slice() {
    let mut slice_mut = RcSliceMut::from_vec(Vec::<u32>::new());
    let left = RcSliceMut::split_off_left(&mut slice_mut);
    assert_eq!(0, left.len());
    assert_eq!(0, slice_mut.len());
}

#[test]
fn split_off_right_on_length_zero_slice() {
    let mut slice_mut = RcSliceMut::from_vec(Vec::<u32>::new());
    let right = RcSliceMut::split_off_right(&mut slice_mut);
    assert_eq!(0, slice_mut.len());
    assert_eq!(0, right.len());
}

#[test]
fn into_immut_doesnt_drop() {
    let dropped = DroppedItems::new();
    let slice_mut = RcSliceMut::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    assert_eq!(0, dropped.get_items().len());
    let slice = RcSliceMut::into_immut(slice_mut);
    // Not dropped yet
    assert_eq!(0, dropped.get_items().len());
    drop(slice);
    // Now items are dropped
    assert_eq!(["a", "b", "c"], dropped.get_items()[..]);
}

#[test]
fn eq_compares_as_slice() {
    let mut slice = RcSliceMut::from_vec(vec![0, 1, 2, 3, 0, 1, 2, 3]);
    let left = RcSliceMut::split_off_left(&mut slice);
    assert_eq!(left, slice);
    slice[0] = 5;
    assert_ne!(left, slice);
}

#[test]
fn ord_compares_as_slice() {
    let mut slice = RcSliceMut::from_vec(vec![0, 2, 1, 1]);
    let left = RcSliceMut::split_off_left(&mut slice);
    assert!(left < slice);
    slice[0] = 0;
    assert!(slice < left);
}

#[test]
fn hash_hashes_as_slice() {
    let mut map = HashMap::new();
    let mut slice = RcSliceMut::from_vec(vec![0, 2, 1, 5, 0, 2, 1, 5]);
    let left = RcSliceMut::split_off_left(&mut slice);
    map.insert(slice, String::from("the slice"));
    assert_eq!("the slice", map.get(&left).unwrap());
    assert_eq!("the slice", map.get(&[0, 2, 1, 5] as &[_]).unwrap());
    assert!(map.get(&[0, 2, 1] as &[_]).is_none());
}

#[test]
fn debug_debugs_as_slice() {
    let slice = RcSliceMut::from_vec(vec![0, 1, 2, 3, 4, 5, 6, 7]);
    assert_eq!(format!("{:?}", &[0, 1, 2, 3, 4, 5, 6, 7]), format!("{:?}", slice));
}

#[test]
fn can_collect() {
    let a = [0, 1, 2, 3, 4];
    let slice: RcSliceMut<_> = a.iter().copied().collect();
    assert_eq!(a, slice[..]);
}

#[test]
fn can_clone() {
    let dropped = DroppedItems::new();
    let original = RcSliceMut::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    let mut clone = original.clone();
    clone[0] = DropTracker("d", &dropped);
    // We dropped the "a" DropTracker from swapping out the clone's first item
    assert_eq!(["a"], dropped.get_items()[..]);
    // Clone is updated
    assert_eq!(["d", "b", "c"], clone[..]);
    // Original is unaffected
    assert_eq!(["a", "b", "c"], original[..]);
    dropped.reset();
    drop(original);
    // Dropped the original's items
    assert_eq!(["a", "b", "c"], dropped.get_items()[..]);
    dropped.reset();
    drop(clone);
    // And dropped the clone's items
    assert_eq!(["d", "b", "c"], dropped.get_items()[..]);
}

#[test]
fn into_iter() {
    // A single test of many methods of RcSliceMutIter. Finer-grained unit
    // tests of the underlying implementation can be found in
    // src/internal/slice_model/slice_items.rs
    let dropped = DroppedItems::new();
    let slice = RcSliceMut::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
        DropTracker("d", &dropped),
        DropTracker("e", &dropped),
        DropTracker("f", &dropped),
        DropTracker("g", &dropped),
        DropTracker("h", &dropped),
    ]);
    let mut iter = slice.into_iter();

    // Just calling into_iter doesn't drop anything
    assert_eq!(0, dropped.get_items().len());

    assert_eq!(8, iter.len());
    assert_eq!(["a", "b", "c", "d", "e", "f", "g", "h"], iter.as_slice());

    assert_eq!("a", iter.next().unwrap());
    assert_eq!(["a"], dropped.get_items()[..]);
    assert_eq!(7, iter.len());
    assert_eq!(["b", "c", "d", "e", "f", "g", "h"], iter.as_slice());

    assert_eq!("h", iter.next_back().unwrap());
    assert_eq!(["a", "h"], dropped.get_items()[..]);
    assert_eq!(6, iter.len());
    assert_eq!(["b", "c", "d", "e", "f", "g"], iter.as_slice());

    assert_eq!("g", iter.next_back().unwrap());
    assert_eq!(["a", "h", "g"], dropped.get_items()[..]);
    assert_eq!(5, iter.len());
    assert_eq!(["b", "c", "d", "e", "f"], iter.as_slice());

    // Mutate the iterator as a slice
    iter.as_mut_slice()[0] = DropTracker("x", &dropped);
    assert_eq!(["a", "h", "g", "b"], dropped.get_items()[..]);
    assert_eq!(5, iter.len());
    assert_eq!(["x", "c", "d", "e", "f"], iter.as_slice());

    assert_eq!("x", iter.next().unwrap());
    assert_eq!(["a", "h", "g", "b", "x"], dropped.get_items()[..]);
    assert_eq!(4, iter.len());
    assert_eq!(["c", "d", "e", "f"], iter.as_slice());

    // Split off first 1 item
    let _ = iter.split_off_to(1);
    assert_eq!(["a", "h", "g", "b", "x", "c"], dropped.get_items()[..]);
    assert_eq!(3, iter.len());
    assert_eq!(["d", "e", "f"], iter.as_slice());

    // Split off last 1 item
    let _ = iter.split_off_from(2);
    assert_eq!(["a", "h", "g", "b", "x", "c", "f"], dropped.get_items()[..]);
    assert_eq!(2, iter.len());
    assert_eq!(["d", "e"], iter.as_slice());

    // Drop the iterator early
    drop(iter);
    assert_eq!(["a", "h", "g", "b", "x", "c", "f", "d", "e"], dropped.get_items()[..]);
}

#[test]
fn debug_rc_slice_mut_iter() {
    let slice = RcSliceMut::from_vec(vec![10, 20, 30, 40]);
    let iter = slice.into_iter();
    println!("iter = {:?}", iter);
    assert!(format!("{:?}", iter).contains("RcSliceMutIter"));
}

#[test]
fn split_into_parts() {
    // A single test of many methods of RcSliceMutParts. Finer-grained unit
    // tests of the underlying implementation can be found in
    // src/internal/bin_parts_iter.rs.
    let dropped = DroppedItems::new();
    let slice = RcSliceMut::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
        DropTracker("d", &dropped),
        DropTracker("e", &dropped),
        DropTracker("f", &dropped),
        DropTracker("g", &dropped),
        DropTracker("h", &dropped),
    ]);
    let mut parts = RcSliceMut::split_into_parts(slice, 8);

    assert_eq!(8, parts.len());
    assert_eq!(["a", "b", "c", "d", "e", "f", "g", "h"], parts.as_slice());

    assert_eq!(["a"], parts.next().unwrap()[..]);
    assert_eq!(["a"], dropped.get_items()[..]);
    assert_eq!(7, parts.len());
    assert_eq!(["b", "c", "d", "e", "f", "g", "h"], parts.as_slice());

    assert_eq!(["h"], parts.next_back().unwrap()[..]);
    assert_eq!(["a", "h"], dropped.get_items()[..]);
    assert_eq!(6, parts.len());
    assert_eq!(["b", "c", "d", "e", "f", "g"], parts.as_slice());

    assert_eq!(["g"], parts.next_back().unwrap()[..]);
    assert_eq!(["a", "h", "g"], dropped.get_items()[..]);
    assert_eq!(5, parts.len());
    assert_eq!(["b", "c", "d", "e", "f"], parts.as_slice());

    assert_eq!(["b"], parts.next().unwrap()[..]);
    assert_eq!(["a", "h", "g", "b"], dropped.get_items()[..]);
    assert_eq!(4, parts.len());
    assert_eq!(["c", "d", "e", "f"], parts.as_slice());

    // Mutate as slice
    parts.as_mut_slice()[3] = DropTracker("x", &dropped);
    assert_eq!(["a", "h", "g", "b", "f"], dropped.get_items()[..]);
    assert_eq!(4, parts.len());
    assert_eq!(["c", "d", "e", "x"], parts.as_slice());

    // Drop the iterator early
    drop(parts);
    assert_eq!(["a", "h", "g", "b", "f", "c", "d", "e", "x"], dropped.get_items()[..]);
}

#[test]
fn debug_rc_slice_mut_parts() {
    let slice = RcSliceMut::from_vec(vec![0, 5, 10, 15, 20]);
    let parts = RcSliceMut::split_into_parts(slice, 2);
    println!("parts = {:?}", parts);
    assert!(format!("{:?}", parts).contains("RcSliceMutParts"));
}
