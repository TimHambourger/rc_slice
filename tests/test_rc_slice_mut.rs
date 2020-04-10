extern crate rc_slice;

mod test_utils;

use std::cell::RefCell;

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
fn can_collect() {
    let a = [0, 1, 2, 3, 4];
    let slice: RcSliceMut<_> = a.iter().copied().collect();
    assert_eq!(a, slice[..]);
}
