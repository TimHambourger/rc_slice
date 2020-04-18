extern crate rc_slice;

#[macro_use]
mod test_utils;

use std::{
    collections::hash_map::HashMap,
    sync::{Arc, Mutex},
    thread,
};
use rc_slice::ArcSliceMut;
use test_utils::ThreadSafeDropTracker;

is_covariant!(ArcSliceMut);

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


#[test]
fn split_off_left_on_length_one_slice() {
    let mut slice_mut = ArcSliceMut::from_vec(vec![0]);
    let left = ArcSliceMut::split_off_left(&mut slice_mut);
    assert_eq!(0, left.len());
    assert_eq!([0], slice_mut[..]);
}

#[test]
fn split_off_right_on_length_one_slice() {
    let mut slice_mut = ArcSliceMut::from_vec(vec![0]);
    let right = ArcSliceMut::split_off_right(&mut slice_mut);
    assert_eq!(0, slice_mut.len());
    assert_eq!([0], right[..]);
}

#[test]
fn split_off_left_on_length_zero_slice() {
    let mut slice_mut = ArcSliceMut::from_vec(Vec::<u32>::new());
    let left = ArcSliceMut::split_off_left(&mut slice_mut);
    assert_eq!(0, left.len());
    assert_eq!(0, slice_mut.len());
}

#[test]
fn split_off_right_on_length_zero_slice() {
    let mut slice_mut = ArcSliceMut::from_vec(Vec::<u32>::new());
    let right = ArcSliceMut::split_off_right(&mut slice_mut);
    assert_eq!(0, slice_mut.len());
    assert_eq!(0, right.len());
}


#[test]
fn eq_compares_as_slice() {
    let mut slice = ArcSliceMut::from_vec(vec![0, 1, 2, 3, 0, 1, 2, 3]);
    let left = ArcSliceMut::split_off_left(&mut slice);
    assert_eq!(left, slice);
    slice[0] = 5;
    assert_ne!(left, slice);
}

#[test]
fn ord_compares_as_slice() {
    let mut slice = ArcSliceMut::from_vec(vec![0, 2, 1, 1]);
    let left = ArcSliceMut::split_off_left(&mut slice);
    assert!(left < slice);
    slice[0] = 0;
    assert!(slice < left);
}

#[test]
fn hash_hashes_as_slice() {
    let mut map = HashMap::new();
    let mut slice = ArcSliceMut::from_vec(vec![0, 2, 1, 5, 0, 2, 1, 5]);
    let left = ArcSliceMut::split_off_left(&mut slice);
    map.insert(slice, String::from("the slice"));
    assert_eq!("the slice", map.get(&left).unwrap());
    assert_eq!("the slice", map.get(&[0, 2, 1, 5] as &[_]).unwrap());
    assert!(map.get(&[0, 2, 1] as &[_]).is_none());
}

#[test]
fn can_collect() {
    let a = [0, 1, 2, 3, 4];
    let slice: ArcSliceMut<_> = a.iter().copied().collect();
    assert_eq!(a, slice[..]);
}

#[test]
fn into_iter_across_threads() {
    let dropped = Arc::new(Mutex::new(Vec::new()));
    let slice = ArcSliceMut::from_vec(vec![
        ThreadSafeDropTracker("a", dropped.clone()),
        ThreadSafeDropTracker("b", dropped.clone()),
        ThreadSafeDropTracker("c", dropped.clone()),
        ThreadSafeDropTracker("d", dropped.clone()),
        ThreadSafeDropTracker("e", dropped.clone()),
        ThreadSafeDropTracker("f", dropped.clone()),
        ThreadSafeDropTracker("g", dropped.clone()),
        ThreadSafeDropTracker("h", dropped.clone()),
    ]);
    let mut iter1 = slice.into_iter();
    let mut iter2 = iter1.split_off_to(3);
    let mut iter3 = iter1.split_off_from(2);
    let handle1 = thread::spawn(move || {
        assert_eq!(["a", "b", "c"], iter2.as_slice());
        assert_eq!("c", iter2.next_back().unwrap());
        assert_eq!("a", iter2.next().unwrap());
        assert_eq!("b", iter2.next_back().unwrap());
        assert!(iter2.next().is_none());
        assert!(iter2.next_back().is_none());
    });
    let handle2 = thread::spawn(move || {
        assert_eq!(["f", "g", "h"], iter3.as_slice());
        assert_eq!("f", iter3.next().unwrap());
        assert_eq!("g", iter3.next().unwrap());
        assert_eq!("h", iter3.next_back().unwrap());
        assert!(iter3.next_back().is_none());
        assert!(iter3.next().is_none());
    });
    assert_eq!(["d", "e"], iter1.as_slice());
    assert_eq!("d", iter1.next().unwrap());
    assert_eq!("e", iter1.next().unwrap());
    assert!(iter1.next().is_none());
    assert!(iter1.next_back().is_none());
    handle1.join().unwrap();
    handle2.join().unwrap();
    let mut d = dropped.lock().unwrap();
    d.sort_unstable();
    assert_eq!(["a", "b", "c", "d", "e", "f", "g", "h"], d[..]);
}

#[test]
fn arc_slice_mut_iter_as_mut_slice_across_threads() {
    let dropped = Arc::new(Mutex::new(Vec::new()));
    let dropped2 = dropped.clone();
    let mut slice = ArcSliceMut::from_vec(vec![
        ThreadSafeDropTracker("a", dropped.clone()),
        ThreadSafeDropTracker("b", dropped.clone()),
        ThreadSafeDropTracker("c", dropped.clone()),
        ThreadSafeDropTracker("d", dropped.clone()),
    ]);
    let right = ArcSliceMut::split_off_right(&mut slice);
    let mut iter = slice.into_iter();
    let mut right_iter = right.into_iter();
    let handle = thread::spawn(move || {
        assert_eq!(["c", "d"], right_iter.as_slice());
        right_iter.as_mut_slice()[1] = ThreadSafeDropTracker("x", dropped2.clone());
        let d = dropped2.lock().unwrap();
        assert!(d.contains(&"d"));
        drop(d);
        assert_eq!(["c", "x"], right_iter.as_slice());
        assert_eq!("x", right_iter.next_back().unwrap());
    });
    assert_eq!(["a", "b"], iter.as_slice());
    iter.as_mut_slice()[0] = ThreadSafeDropTracker("y", dropped.clone());
    let d = dropped.lock().unwrap();
    assert!(d.contains(&"a"));
    drop(d);
    assert_eq!(["y", "b"], iter.as_slice());
    assert_eq!("y", iter.next().unwrap());
    handle.join().unwrap();
    let mut d = dropped.lock().unwrap();
    d.sort_unstable();
    // We moved right_iter into the other thread, so it's been totally dropped.
    // But iter still contains the "b" tracker and hasn't been dropped yet.
    assert_eq!(["a", "c", "d", "x", "y"], d[..]);
    drop(d);
    drop(iter);
    let d = dropped.lock().unwrap();
    // Now we've dropped "b"
    assert_eq!(["a", "c", "d", "x", "y", "b"], d[..]);
}

#[test]
#[should_panic(expected = "at <=")]
fn rc_slice_mut_iter_split_off_from_out_of_bounds() {
    let slice = ArcSliceMut::from_vec(vec![10, 20, 30, 40]);
    let mut iter = slice.into_iter();
    iter.split_off_from(5);
}

#[test]
#[should_panic(expected = "at <=")]
fn rc_slice_mut_iter_split_off_to_out_of_bounds() {
    let slice = ArcSliceMut::from_vec(vec![10, 20, 30, 40]);
    let mut iter = slice.into_iter();
    iter.split_off_to(5);
}

#[test]
fn split_into_parts_across_threads() {
    let dropped = Arc::new(Mutex::new(Vec::new()));
    let dropped2 = dropped.clone();
    let slice = ArcSliceMut::from_vec(vec![
        ThreadSafeDropTracker("a", dropped.clone()),
        ThreadSafeDropTracker("b", dropped.clone()),
        ThreadSafeDropTracker("c", dropped.clone()),
        ThreadSafeDropTracker("d", dropped.clone()),
        ThreadSafeDropTracker("e", dropped.clone()),
        ThreadSafeDropTracker("f", dropped.clone()),
        ThreadSafeDropTracker("g", dropped.clone()),
        ThreadSafeDropTracker("h", dropped.clone()),
    ]);
    let mut parts = ArcSliceMut::split_into_parts(slice, 8);
    let part_a = parts.next().unwrap();
    let part_h = parts.next_back().unwrap();
    let part_g = parts.next_back().unwrap();
    let part_b = parts.next().unwrap();
    let handle = thread::spawn(move || {
        assert_eq!(["a"], part_a[..]);
        assert_eq!(["b"], part_b[..]);
        drop(part_a);
        drop(part_b);
        let d = dropped2.lock().unwrap();
        assert!(d.contains(&"a"));
        assert!(d.contains(&"b"));
    });
    assert_eq!(["g"], part_g[..]);
    assert_eq!(["h"], part_h[..]);
    drop(part_g);
    drop(part_h);
    let d = dropped.lock().unwrap();
    assert!(d.contains(&"g"));
    assert!(d.contains(&"h"));
    drop(d);
    handle.join().unwrap();
    let mut d = dropped.lock().unwrap();
    d.sort_unstable();
    assert_eq!(["a", "b", "g", "h"], d[..]);
    drop(d);
    assert_eq!(["c", "d", "e", "f"], parts.as_slice());
    drop(parts);
    let mut d = dropped.lock().unwrap();
    d.sort_unstable();
    assert_eq!(["a", "b", "c", "d", "e", "f", "g", "h"], d[..]);
}

#[test]
fn arc_slice_mut_parts_as_mut_slice() {
    let slice = ArcSliceMut::from_vec(vec![10, 20, 30, 40, 50]);
    let mut parts = ArcSliceMut::split_into_parts(slice, 2);
    parts.as_mut_slice()[0] = 60;
    assert_eq!([60, 20, 30, 40, 50], parts.as_slice());
    assert_eq!([60, 20], parts.next().unwrap()[..]);
    parts.as_mut_slice()[2] = 70;
    assert_eq!([30, 40, 70], parts.as_slice()[..]);
    assert_eq!([30, 40, 70], parts.next_back().unwrap()[..]);
    assert_eq!(0, parts.len());
}

