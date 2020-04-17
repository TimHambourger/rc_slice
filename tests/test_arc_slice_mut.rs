extern crate rc_slice;

mod test_utils;

use std::{
    sync::{Arc, Mutex},
    thread,
};
use rc_slice::ArcSliceMut;
use test_utils::ThreadSafeDropTracker;

#[test]
fn is_covariant() {
    #[allow(unused_variables)]
    fn use_slice<'a>(n: &'a u32, slice: &ArcSliceMut<&'a u32>) {
    }

    let slice = ArcSliceMut::from_vec(vec![&0]);
    // Important that x is declared after slice.
    let x = 0;
    // As for RcSlice and RcSliceMut, this wouldn't compile if ArcSliceMut<T> were invariant in T
    use_slice(&x, &slice);
}

#[test]
fn drops_data_across_threads() {
    let dropped = Arc::new(Mutex::new(Vec::new()));
    let slice = ArcSliceMut::from_vec(vec![
        ThreadSafeDropTracker("a", dropped.clone()),
        ThreadSafeDropTracker("b", dropped.clone()),
        ThreadSafeDropTracker("c", dropped.clone()),
    ]);
    let handle = thread::spawn(move || {
        assert_eq!(["a", "b", "c"], slice[..]);
    });
    handle.join().unwrap();
    let mut dropped = dropped.lock().unwrap();
    dropped.sort_unstable();
    assert_eq!(["a", "b", "c"], dropped[..]);
}

#[test]
fn split_off_left_across_threads() {
    let dropped = Arc::new(Mutex::new(Vec::new()));
    let mut slice = ArcSliceMut::from_vec(vec![
        ThreadSafeDropTracker("a", dropped.clone()),
        ThreadSafeDropTracker("b", dropped.clone()),
        ThreadSafeDropTracker("c", dropped.clone()),
    ]);
    let left = ArcSliceMut::split_off_left(&mut slice);
    let handle = thread::spawn(move || {
        assert_eq!(["a"], left[..]);
    });
    assert_eq!(["b", "c"], slice[..]);
    handle.join().unwrap();
    assert_eq!(["a"], dropped.lock().unwrap()[..]);
    drop(slice);
    let mut d = dropped.lock().unwrap();
    d.sort_unstable();
    assert_eq!(["a", "b", "c"], d[..]);
}

#[test]
fn split_off_right_across_threads() {
    let dropped = Arc::new(Mutex::new(Vec::new()));
    let mut slice = ArcSliceMut::from_vec(vec![
        ThreadSafeDropTracker("a", dropped.clone()),
        ThreadSafeDropTracker("b", dropped.clone()),
        ThreadSafeDropTracker("c", dropped.clone()),
    ]);
    let right = ArcSliceMut::split_off_right(&mut slice);
    let handle = thread::spawn(move || {
        assert_eq!(["b", "c"], right[..]);
    });
    assert_eq!(["a"], slice[..]);
    handle.join().unwrap();
    let mut d = dropped.lock().unwrap();
    d.sort_unstable();
    assert_eq!(["b", "c"], d[..]);
    drop(d);
    drop(slice);
    let mut d = dropped.lock().unwrap();
    d.sort_unstable();
    assert_eq!(["a", "b", "c"], d[..]);
}
