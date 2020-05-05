extern crate rc_slice;

#[macro_use]
mod test_utils;

use std::{
    collections::hash_map::HashMap,
};

use rc_slice::RcSlice;
use test_utils::{DroppedItems, DropTracker};

is_covariant!(RcSlice);

#[test]
fn drops_its_data() {
    let dropped = DroppedItems::new();
    RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    assert_eq!(["a", "b", "c"], dropped.get_items()[..]);
}

#[test]
fn drops_only_when_no_strong_refs() {
    let dropped = DroppedItems::new();
    let slice = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    let clone = slice.clone();
    drop(clone);
    // Still 0 even after clone is dropped
    assert_eq!(0, dropped.get_items().len());
    drop(slice);
    assert_eq!(["a", "b", "c"], dropped.get_items()[..]);
}

#[test]
fn drops_when_children_dropped() {
    let dropped = DroppedItems::new();
    let mut slice = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    RcSlice::split_off_left(&mut slice);
    // We should've dropped the 1 item from the left subslice
    assert_eq!(["a"], dropped.get_items()[..]);
    drop(slice);
    assert_eq!(["a", "b", "c"], dropped.get_items()[..]);
}

#[test]
fn derefs_to_slice() {
    let slice = RcSlice::from_vec(vec![0, 1, 2, 3]);
    assert_eq!([0, 1, 2, 3], slice[..]);
}

#[test]
fn clone_derefs_to_subslice() {
    let slice = RcSlice::from_vec(vec![0, 1, 2, 3, 4]);
    let left = RcSlice::clone_left(&slice);
    let right = RcSlice::clone_right(&slice);
    assert_eq!([0, 1], left[..]);
    assert_eq!([2, 3, 4], right[..]);
}

#[test]
fn clone_tolerates_small_slices() {
    // To make sure our short-circuiting for small slices doesn't break anything
    let slice = RcSlice::from_vec(vec![0]);
    assert_eq!(1, slice.len());
    let left = RcSlice::clone_left(&slice);
    let right = RcSlice::clone_right(&slice);
    assert_eq!(0, left.len());
    assert_eq!(1, right.len());
    let left_left = RcSlice::clone_left(&left);
    assert_eq!(0, left_left.len());
}

#[test]
fn split_into_parts() {
    // A single test of many methods of RcSliceParts. Finer-grained unit
    // tests of the underlying implementation can be found in
    // src/internal/bin_parts_iter.rs.
    let dropped = DroppedItems::new();
    let slice = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
        DropTracker("d", &dropped),
        DropTracker("e", &dropped),
        DropTracker("f", &dropped),
        DropTracker("g", &dropped),
        DropTracker("h", &dropped),
    ]);
    let mut parts = RcSlice::split_into_parts(slice, 8);

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

    // Drop the iterator early
    drop(parts);
    assert_eq!(["a", "h", "g", "b", "c", "d", "e", "f"], dropped.get_items()[..]);
}

#[test]
fn clone_rc_slice_parts() {
    let dropped = DroppedItems::new();
    let slice = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    let mut parts = RcSlice::split_into_parts(slice, 2);
    assert_eq!(["a"], parts.next().unwrap()[..]);
    assert_eq!(["a"], dropped.get_items()[..]);
    assert_eq!(1, parts.len());

    let mut clone = parts.clone();
    // Cloned iterator matches iteration state of original iterator.
    assert_eq!(1, clone.len());
    assert_eq!(["b", "c"], parts.next().unwrap()[..]);
    // We haven't dropped the righthand items yet since we cloned the iterator.
    assert_eq!(["a"], dropped.get_items()[..]);
    assert_eq!(["b", "c"], clone.next().unwrap()[..]);
    // Now we've dropped
    assert_eq!(["a", "b", "c"], dropped.get_items()[..]);
}

#[test]
fn debug_rc_slice_parts() {
    let slice = RcSlice::from_vec(vec![0, 5, 10, 15, 20]);
    let parts = RcSlice::split_into_parts(slice, 2);
    println!("parts = {:?}", parts);
    assert!(format!("{:?}", parts).contains("RcSliceParts"));
}

#[test]
fn get_mut_allows_mutation() {
    let mut slice = RcSlice::from_vec(vec![0, 1, 2, 3]);
    RcSlice::get_mut(&mut slice).unwrap()[0] = 4;
    assert_eq!([4, 1, 2, 3], slice[..]);
}

#[test]
fn get_mut_prevents_unsafe_mutation() {
    let mut slice1 = RcSlice::from_vec(vec![0, 1, 2, 3]);
    let mut slice2 = RcSlice::split_off_right(&mut slice1);
    {
        let mut slice3 = RcSlice::clone_right(&slice2);
        assert_eq!(&mut [0, 1], RcSlice::get_mut(&mut slice1).unwrap());
        assert!(RcSlice::get_mut(&mut slice2).is_none());
        assert!(RcSlice::get_mut(&mut slice3).is_none());
    }
    assert_eq!(&mut [0, 1], RcSlice::get_mut(&mut slice1).unwrap());
    assert_eq!(&mut [2, 3], RcSlice::get_mut(&mut slice2).unwrap());
}

#[test]
fn get_mut_handles_gaps_in_hierarchy() {
    let grandparent = RcSlice::from_vec(vec![0, 1, 2, 3]);
    let mut parent = RcSlice::clone_left(&grandparent);
    let child = RcSlice::clone_left(&parent);
    parent = RcSlice::clone_left(&grandparent);
    drop(grandparent);
    // Newly re-cloned parent still knows that child is present
    assert!(RcSlice::get_mut(&mut parent).is_none());
    drop(child);
    // But w/ no child parent is mutable
    assert_eq!(&mut [0, 1], RcSlice::get_mut(&mut parent).unwrap());
}

#[test]
fn eq_compares_as_slice() {
    let mut slice = RcSlice::from_vec(vec![0, 1, 2, 3, 0, 1, 2, 3]);
    let left = RcSlice::split_off_left(&mut slice);
    assert_eq!(left, slice);
    RcSlice::split_off_right(&mut slice);
    assert_ne!(left, slice);
}

#[test]
fn ord_compares_as_slice() {
    let mut slice = RcSlice::from_vec(vec![0, 2, 1, 1]);
    let mut left = RcSlice::split_off_left(&mut slice);
    assert!(left < slice);
    RcSlice::split_off_left(&mut left);
    assert!(slice < left);
}

#[test]
fn hash_hashes_as_slice() {
    let mut map = HashMap::new();
    let mut slice = RcSlice::from_vec(vec![0, 2, 1, 5, 0, 2, 1, 5]);
    let left = RcSlice::split_off_left(&mut slice);
    map.insert(slice, String::from("the slice"));
    assert_eq!("the slice", map.get(&left).unwrap());
    assert_eq!("the slice", map.get(&[0, 2, 1, 5] as &[_]).unwrap());
    assert!(map.get(&[0, 2, 1] as &[_]).is_none());
}

#[test]
fn debug_debugs_as_slice() {
    let slice = RcSlice::from_vec(vec![0, 1, 2, 3, 4, 5, 6, 7]);
    assert_eq!(format!("{:?}", &[0, 1, 2, 3, 4, 5, 6, 7]), format!("{:?}", slice));
}

#[test]
fn can_collect() {
    let a = [0, 1, 2, 3, 4];
    let slice: RcSlice<_> = a.iter().copied().collect();
    assert_eq!(a, slice[..]);
}

#[test]
fn downgrade_then_upgrade() {
    let slice = RcSlice::from_vec(vec![0, 1, 2, 3]);
    let weak_slice = RcSlice::downgrade(&slice);
    assert_eq!([0, 1, 2, 3], weak_slice.upgrade().unwrap()[..]);
}

#[test]
fn downgrade_lets_slice_get_dropped() {
    let dropped = DroppedItems::new();
    let slice = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    let weak_slice = RcSlice::downgrade(&slice);

    drop(slice);

    assert_eq!(["a", "b", "c"], dropped.get_items()[..]);
    assert!(weak_slice.upgrade().is_none());
}

#[test]
fn downgrade_child_then_upgrade() {
    let dropped = DroppedItems::new();
    let parent = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    let child = RcSlice::clone_right(&parent);
    let weak_child = RcSlice::downgrade(&child);

    drop(child);
    // Nothing dropped b/c parent still alive.
    assert_eq!(0, dropped.get_items().len());
    // And fact that parent is still alive is enough that weak_child
    // should be upgradeable.
    assert!(weak_child.upgrade().is_some());
}

#[test]
fn downgrade_parent_then_upgrade() {
    let dropped = DroppedItems::new();
    let parent = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    let child = RcSlice::clone_right(&parent);
    let weak_parent = RcSlice::downgrade(&parent);

    drop(parent);

    // Dropped left half b/c we dropped the parent
    assert_eq!(["a"], dropped.get_items()[..]);
    // And weak_parent is no longer upgradeable, b/c to upgrade we need
    // to be able to recover the WHOLE subslice.
    assert!(weak_parent.upgrade().is_none());

    // But can still downgrade child then upgrade
    let weak_child = RcSlice::downgrade(&child);
    assert!(weak_child.upgrade().is_some());
}

#[test]
fn downgrade_then_upgrade_with_gaps() {
    let mut grandparent = RcSlice::from_vec(vec![0, 1, 2, 3]);
    let parent = RcSlice::clone_right(&grandparent);
    let child = RcSlice::clone_right(&parent);
    let weak_child = RcSlice::downgrade(&child);
    drop(parent);
    drop(child);
    // Fact that grandparent is still alive is enough that weak_child should
    // be upgradeable.
    let child = weak_child.upgrade().unwrap();
    assert_eq!([3], child[..]);
    // And we should know that presence of child means grandparent isn't
    // mutable.
    assert!(RcSlice::get_mut(&mut grandparent).is_none());
    drop(child);
    // Now grandparent is mutable.
    assert_eq!(&mut [0, 1, 2, 3], RcSlice::get_mut(&mut grandparent).unwrap());
}

#[test]
fn into_mut_allows_mutation() {
    let slice = RcSlice::from_vec(vec![0, 1, 2, 3]);
    let mut slice = RcSlice::into_mut(slice).unwrap();
    slice[0] = 4;
    assert_eq!([4, 1, 2, 3], slice[..]);
}

#[test]
fn into_mut_prevents_unsafe_mutation() {
    let mut slice1 = RcSlice::from_vec(vec![0, 1, 2, 3]);
    let slice2 = RcSlice::split_off_right(&mut slice1);
    let slice3 = RcSlice::clone_right(&slice2);
    assert_eq!([0, 1], RcSlice::into_mut(slice1).unwrap()[..]);
    // Can't convert slice2 into mutable b/c its child slice3 is still alive.
    let slice2 = RcSlice::into_mut(slice2).unwrap_err();
    assert_eq!([2, 3], slice2[..]);
    // Likewise can't convert slice3 into mutable
    let slice3 = RcSlice::into_mut(slice3).unwrap_err();
    assert_eq!([3], slice3[..]);
    drop(slice2);
    // But now can convert slice3
    assert_eq!([3], RcSlice::into_mut(slice3).unwrap()[..]);
}

#[test]
fn into_mut_tolerates_weak_slices() {
    let slice = RcSlice::from_vec(vec![0, 1, 2, 3, 4]);
    let weak_slice = RcSlice::downgrade(&slice);
    // Conversion into mutable is allowed
    let slice = RcSlice::into_mut(slice).unwrap();
    assert_eq!([0, 1, 2, 3, 4], slice[..]);
    // And weak_slice is no longer upgradeable
    assert!(weak_slice.upgrade().is_none());
}

#[test]
fn into_mut_doesnt_drop() {
    let dropped = DroppedItems::new();
    let slice = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    // Create some child slices to exercise the recursive logic in
    // RcSliceData::forget_items.
    RcSlice::clone_left(&RcSlice::clone_right(&slice));
    RcSlice::clone_left(&slice);
    assert_eq!(0, dropped.get_items().len());
    let slice_mut = RcSlice::into_mut(slice).unwrap();
    // Not dropped yet
    assert_eq!(0, dropped.get_items().len());
    drop(slice_mut);
    // Now items are dropped
    assert_eq!(["a", "b", "c"], dropped.get_items()[..]);
}
