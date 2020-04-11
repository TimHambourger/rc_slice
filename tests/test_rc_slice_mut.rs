extern crate rc_slice;

mod test_utils;

use std::{
    cell::RefCell,
    collections::hash_map::HashMap,
};

use rc_slice::RcSliceMut;
use test_utils::DropTracker;

#[test]
fn drops_its_data() {
    let dropped = RefCell::new(Vec::<&str>::new());
    RcSliceMut::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);

    dropped.borrow_mut().sort_unstable();
    assert_eq!(["a", "b", "c"], dropped.borrow()[..]);
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
    let dropped = RefCell::new(Vec::<&str>::new());
    let slice_mut = RcSliceMut::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    assert_eq!(0, dropped.borrow().len());
    let slice = RcSliceMut::into_immut(slice_mut);
    // Not dropped yet
    assert_eq!(0, dropped.borrow().len());
    drop(slice);
    // Now items are dropped
    dropped.borrow_mut().sort_unstable();
    assert_eq!(["a", "b", "c"], dropped.borrow()[..]);
}


#[test]
fn eq_compares_as_slice() {
    let mut slice = RcSliceMut::from_vec(vec![0, 1, 2, 3, 0, 1, 2, 3]);
    let left = RcSliceMut::split_off_left(&mut slice);
    assert_eq!(left, slice);
}

#[test]
fn ord_compares_as_slice() {
    let mut slice = RcSliceMut::from_vec(vec![0, 2, 1, 1]);
    let left = RcSliceMut::split_off_left(&mut slice);
    assert!(left < slice);
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
fn can_collect() {
    let a = [0, 1, 2, 3, 4];
    let slice: RcSliceMut<_> = a.iter().copied().collect();
    assert_eq!(a, slice[..]);
}

#[test]
fn can_clone() {
    let dropped = RefCell::new(Vec::new());
    let original = RcSliceMut::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    let mut clone = original.clone();
    clone[0] = DropTracker("d", &dropped);
    // We dropped the "a" DropTracker from swapping out the clone's first item
    assert_eq!(["a"], dropped.borrow()[..]);
    // Clone is updated
    assert_eq!(["d", "b", "c"], clone[..]);
    // Original is unaffected
    assert_eq!(["a", "b", "c"], original[..]);
    dropped.borrow_mut().clear();
    drop(original);
    dropped.borrow_mut().sort_unstable();
    // Dropped the original's items
    assert_eq!(["a", "b", "c"], dropped.borrow()[..]);
    dropped.borrow_mut().clear();
    drop(clone);
    // And dropped the clone's items
    dropped.borrow_mut().sort_unstable();
    assert_eq!(["b", "c", "d"], dropped.borrow()[..]);
}

#[test]
fn into_iter_basic() {
    let dropped = RefCell::new(Vec::new());
    let slice = RcSliceMut::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
        DropTracker("d", &dropped),
    ]);
    let mut iter = slice.into_iter();
    // Just calling into_iter doesn't drop anything
    assert_eq!(0, dropped.borrow().len());
    assert_eq!("a", iter.next().unwrap());
    assert_eq!(["a"], dropped.borrow()[..]);
    assert_eq!("b", iter.next().unwrap());
    assert_eq!(["a", "b"], dropped.borrow()[..]);
    assert_eq!("c", iter.next().unwrap());
    assert_eq!(["a", "b", "c"], dropped.borrow()[..]);
    assert_eq!("d", iter.next().unwrap());
    assert_eq!(["a", "b", "c", "d"], dropped.borrow()[..]);
    assert!(iter.next().is_none());
}

#[test]
fn into_iter_partial_iteration() {
    let dropped = RefCell::new(Vec::new());
    let slice = RcSliceMut::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
        DropTracker("d", &dropped),
    ]);
    let mut iter = slice.into_iter();
    assert_eq!("a", iter.next().unwrap());
    assert_eq!(["a"], dropped.borrow()[..]);
    assert_eq!("b", iter.next().unwrap());
    assert_eq!(["a", "b"], dropped.borrow()[..]);
    assert_eq!(2, iter.len());
    drop(iter);
    // Dropping the iterator drops the rest of the items
    dropped.borrow_mut().sort_unstable();
    assert_eq!(["a", "b", "c", "d"], dropped.borrow()[..]);
}

#[test]
fn into_iter_double_ended() {
    let dropped = RefCell::new(Vec::new());
    let slice = RcSliceMut::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
        DropTracker("d", &dropped),
    ]);
    let mut iter = slice.into_iter();
    assert_eq!("a", iter.next().unwrap());
    assert_eq!(["a"], dropped.borrow()[..]);
    assert_eq!("d", iter.next_back().unwrap());
    assert_eq!(["a", "d"], dropped.borrow()[..]);
    assert_eq!("b", iter.next().unwrap());
    assert_eq!(["a", "d", "b"], dropped.borrow()[..]);
    assert_eq!("c", iter.next_back().unwrap());
    assert_eq!(["a", "d", "b", "c"], dropped.borrow()[..]);
    assert!(iter.next().is_none());
    assert!(iter.next_back().is_none());
}
