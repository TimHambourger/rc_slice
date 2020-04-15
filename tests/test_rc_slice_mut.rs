extern crate rc_slice;

mod test_utils;

use std::{
    cell::RefCell,
    collections::hash_map::HashMap,
};

use rc_slice::RcSliceMut;
use test_utils::DropTracker;

#[test]
fn is_covariant() {
    #[allow(unused_variables)]
    fn use_slice<'a>(n: &'a u32, slice: &RcSliceMut<&'a u32>) {
    }

    let slice = RcSliceMut::from_vec(vec![&0]);
    // Important that x is declared after slice.
    let x = 0;
    // If RcSliceMut<T> were invariant in T, then the next line would give
    // error[E0597]: `x` does not live long enough
    //   --> tests/test_rc_slice_mut.rs:35:15
    //    |
    // 35 |     use_slice(&x, &slice)
    //    |               ^^ borrowed value does not live long enough
    // 36 | }
    //    | -
    //    | |
    //    | `x` dropped here while still borrowed
    //    | borrow might be used here, when `slice` is dropped and runs the destructor for type `rc_slice::RcSliceMut<&u32>`
    //    |
    //    = note: values in a scope are dropped in the opposite order they are defined
    use_slice(&x, &slice)
}

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

#[test]
fn rc_slice_mut_iter_as_slice() {
    let slice = RcSliceMut::from_vec(vec![10, 20, 30, 40, 50]);
    let mut iter = slice.into_iter();
    assert_eq!([10, 20, 30, 40, 50], iter.as_slice());
    iter.next();
    assert_eq!([20, 30, 40, 50], iter.as_slice());
    iter.next_back();
    assert_eq!([20, 30, 40], iter.as_slice());
}

#[test]
fn rc_slice_mut_iter_as_slice_mut() {
    let slice = RcSliceMut::from_vec(vec![10, 20, 30, 40, 50]);
    let mut iter = slice.into_iter();
    iter.as_slice_mut()[0] = 60;
    assert_eq!([60, 20, 30, 40, 50], iter.as_slice());
    assert_eq!(60, iter.next().unwrap());
    iter.as_slice_mut()[3] = 70;
    assert_eq!([20, 30, 40, 70], iter.as_slice());
    assert_eq!(70, iter.next_back().unwrap());
    iter.as_slice_mut()[1] = 80;
    assert_eq!([20, 80, 40], iter.as_slice());
    assert_eq!(20, iter.next().unwrap());
    assert_eq!(80, iter.next().unwrap());
}

#[test]
fn rc_slice_mut_iter_split_off_from() {
    let dropped = RefCell::new(Vec::new());
    let slice = RcSliceMut::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
        DropTracker("d", &dropped),
    ]);
    let mut iter = slice.into_iter();
    // Test a trivial split first: split off last 0 items
    let mut split = iter.split_off_from(4);
    assert_eq!(0, split.len());
    assert!(split.next().is_none());
    // Split off last item
    let mut split = iter.split_off_from(3);
    assert_eq!(1, split.len());
    assert_eq!(0, dropped.borrow().len());
    assert_eq!("d", split.next().unwrap());
    assert_eq!(["d"], dropped.borrow()[..]);
    assert!(split.next().is_none());
    // Assert current contents of iterator
    assert_eq!(["a", "b", "c"], iter.as_slice());
    assert_eq!("c", iter.next_back().unwrap());
    assert_eq!(["d", "c"], dropped.borrow()[..]);
    // Split off last 2 items, i.e. whole remaining iterator
    let mut split = iter.split_off_from(0);
    assert_eq!(0, iter.len());
    assert!(iter.next().is_none());
    assert_eq!(["a", "b"], split.as_slice());
    assert_eq!("b", split.next_back().unwrap());
    assert_eq!(["d", "c", "b"], dropped.borrow()[..]);
    assert_eq!("a", split.next_back().unwrap());
    assert_eq!(["d", "c", "b", "a"], dropped.borrow()[..]);
}

#[test]
fn rc_slice_mut_iter_split_off_to() {
    let dropped = RefCell::new(Vec::new());
    let slice = RcSliceMut::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
        DropTracker("d", &dropped),
    ]);
    let mut iter = slice.into_iter();
    // Test a trivial split first: split off first 0 items
    let mut split = iter.split_off_to(0);
    assert_eq!(0, split.len());
    assert!(split.next().is_none());
    // Split off first item
    let mut split = iter.split_off_to(1);
    assert_eq!(1, split.len());
    assert_eq!(0, dropped.borrow().len());
    assert_eq!("a", split.next().unwrap());
    assert_eq!(["a"], dropped.borrow()[..]);
    assert!(split.next().is_none());
    // Assert current contents of iterator
    assert_eq!(["b", "c", "d"], iter.as_slice());
    assert_eq!("b", iter.next().unwrap());
    assert_eq!(["a", "b"], dropped.borrow()[..]);
    // Split off first 2 items, i.e. whole remaining iterator
    let mut split = iter.split_off_to(2);
    assert_eq!(0, iter.len());
    assert!(iter.next().is_none());
    assert_eq!(["c", "d"], split.as_slice());
    assert_eq!("c", split.next().unwrap());
    assert_eq!(["a", "b", "c"], dropped.borrow()[..]);
    assert_eq!("d", split.next().unwrap());
    assert_eq!(["a", "b", "c", "d"], dropped.borrow()[..]);
}

#[test]
#[should_panic(expected = "at <=")]
fn rc_slice_mut_iter_split_off_from_out_of_bounds() {
    let slice = RcSliceMut::from_vec(vec![10, 20, 30, 40]);
    let mut iter = slice.into_iter();
    iter.split_off_from(5);
}

#[test]
#[should_panic(expected = "at <=")]
fn rc_slice_mut_iter_split_off_to_out_of_bounds() {
    let slice = RcSliceMut::from_vec(vec![10, 20, 30, 40]);
    let mut iter = slice.into_iter();
    iter.split_off_to(5);
}

#[test]
fn split_into_parts_basic() {
    let dropped = RefCell::new(Vec::new());
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
    assert_eq!(["a"], parts.next().unwrap()[..]);
    assert_eq!(["a"], dropped.borrow()[..]);
    assert_eq!(["b"], parts.next().unwrap()[..]);
    assert_eq!(["a", "b"], dropped.borrow()[..]);
    assert_eq!(["c"], parts.next().unwrap()[..]);
    assert_eq!(["a", "b", "c"], dropped.borrow()[..]);
    assert_eq!(["d"], parts.next().unwrap()[..]);
    assert_eq!(["a", "b", "c", "d"], dropped.borrow()[..]);
    assert_eq!(["e"], parts.next().unwrap()[..]);
    assert_eq!(["a", "b", "c", "d", "e"], dropped.borrow()[..]);
    assert_eq!(["f"], parts.next().unwrap()[..]);
    assert_eq!(["a", "b", "c", "d", "e", "f"], dropped.borrow()[..]);
    assert_eq!(["g"], parts.next().unwrap()[..]);
    assert_eq!(["a", "b", "c", "d", "e", "f", "g"], dropped.borrow()[..]);
    assert_eq!(["h"], parts.next().unwrap()[..]);
    assert_eq!(["a", "b", "c", "d", "e", "f", "g", "h"], dropped.borrow()[..]);
    // We've now yielded the last subslice
    assert!(parts.next().is_none());
}

#[test]
fn split_into_parts_partial_iteration() {
    let dropped = RefCell::new(Vec::new());
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
    assert_eq!(["a"], parts.next().unwrap()[..]);
    assert_eq!(["a"], dropped.borrow()[..]);
    assert_eq!(["b"], parts.next().unwrap()[..]);
    assert_eq!(["a", "b"], dropped.borrow()[..]);
    assert_eq!(["c"], parts.next().unwrap()[..]);
    assert_eq!(["a", "b", "c"], dropped.borrow()[..]);
    assert_eq!(["d"], parts.next().unwrap()[..]);
    assert_eq!(["a", "b", "c", "d"], dropped.borrow()[..]);
    // End iteration early. Dropping the iterator should drop the
    // remaining items.
    drop(parts);
    // sort to avoid asserting on the order individual items within
    // the iterator are dropped.
    dropped.borrow_mut().sort_unstable();
    assert_eq!(["a", "b", "c", "d", "e", "f", "g", "h"], dropped.borrow()[..]);
}

#[test]
fn split_into_parts_front_and_back() {
    let slice = RcSliceMut::from_vec(vec![0, 1, 2, 3]);

        // All possible "walks" (sequences of next/next_back calls) for a split
    // into 4 parts, excluding the walk consisting purely of next calls,
    // since we have other tests that focus just on forward iteration.
    // 2 ^ 4 - 1 = 15 different walks.

    // Walk #1: next, next, next, next_back
    let mut parts = RcSliceMut::split_into_parts(slice.clone(), 4);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next().unwrap()[..]);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #2: next, next, next_back, next
    let mut parts = RcSliceMut::split_into_parts(slice.clone(), 4);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #3: next, next, next_back, next_back
    let mut parts = RcSliceMut::split_into_parts(slice.clone(), 4);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #4: next, next_back, next, next
    let mut parts = RcSliceMut::split_into_parts(slice.clone(), 4);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #5: next, next_back, next, next_back
    let mut parts = RcSliceMut::split_into_parts(slice.clone(), 4);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #6: next, next_back, next_back, next
    let mut parts = RcSliceMut::split_into_parts(slice.clone(), 4);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #7: next, next_back, next_back, next_back
    let mut parts = RcSliceMut::split_into_parts(slice.clone(), 4);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #8: next_back, next, next, next
    let mut parts = RcSliceMut::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #9: next_back, next, next, next_back
    let mut parts = RcSliceMut::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #10: next_back, next, next_back, next
    let mut parts = RcSliceMut::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #11: next_back, next, next_back, next_back
    let mut parts = RcSliceMut::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #12: next_back, next_back, next, next
    let mut parts = RcSliceMut::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #13: next_back, next_back, next, next_back
    let mut parts = RcSliceMut::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #14: next_back, next_back, next_back, next
    let mut parts = RcSliceMut::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #15: next_back, next_back, next_back, next_back
    let mut parts = RcSliceMut::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());
}

#[test]
#[should_panic(expected = "power of 2")]
fn split_into_parts_not_power_of_2() {
    let slice = RcSliceMut::from_vec(vec![0]);
    RcSliceMut::split_into_parts(slice, 56);
}

#[test]
#[should_panic(expected = "> 0")]
fn split_into_zero_parts() {
    let slice = RcSliceMut::from_vec(vec![0]);
    RcSliceMut::split_into_parts(slice, 0);
}

#[test]
fn rc_slice_mut_parts_as_slice() {
    // Also use this as a test of num_parts > 8.
    let mut v = Vec::with_capacity(32);
    for i in 0..32 { v.push(i); }
    let slice = RcSliceMut::from_vec(v);
    let mut parts = RcSliceMut::split_into_parts(slice, 32);
    assert_eq!(32, parts.as_slice().len());
    assert_eq!([0, 1, 2, 3, 4, 5], parts.as_slice()[..6]);
    assert_eq!([26, 27, 28, 29, 30, 31], parts.as_slice()[26..]);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!(31, parts.as_slice().len());
    assert_eq!([1, 2, 3, 4, 5, 6], parts.as_slice()[..6]);
    assert_eq!([27, 28, 29, 30, 31], parts.as_slice()[26..]);
    assert_eq!([31], parts.next_back().unwrap()[..]);
    assert_eq!(30, parts.as_slice().len());
    assert_eq!([1, 2, 3, 4, 5, 6], parts.as_slice()[..6]);
    assert_eq!([27, 28, 29, 30], parts.as_slice()[26..]);
    assert_eq!([30], parts.next_back().unwrap()[..]);
    assert_eq!(29, parts.as_slice().len());
    assert_eq!([1, 2, 3, 4, 5, 6], parts.as_slice()[..6]);
    assert_eq!([27, 28, 29], parts.as_slice()[26..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!(28, parts.as_slice().len());
    assert_eq!([2, 3, 4, 5, 6, 7], parts.as_slice()[..6]);
    assert_eq!([28, 29], parts.as_slice()[26..]);
    assert_eq!([29], parts.next_back().unwrap()[..]);
    assert_eq!(27, parts.as_slice().len());
    assert_eq!([2, 3, 4, 5, 6, 7], parts.as_slice()[..6]);
    assert_eq!([28], parts.as_slice()[26..]);
    assert_eq!([28], parts.next_back().unwrap()[..]);
    assert_eq!(26, parts.as_slice().len());
    assert_eq!([2, 3, 4, 5, 6, 7], parts.as_slice()[..6]);
    assert_eq!([25, 26, 27], parts.as_slice()[23..]);
    assert_eq!([2], parts.next().unwrap()[..]);
    assert_eq!(25, parts.as_slice().len());
    assert_eq!([3, 4, 5, 6, 7, 8], parts.as_slice()[..6]);
    assert_eq!([26, 27], parts.as_slice()[23..]);
}

#[test]
fn rc_slice_mut_parts_as_slice_mut() {
    let slice = RcSliceMut::from_vec(vec![10, 20, 30, 40, 50]);
    let mut parts = RcSliceMut::split_into_parts(slice, 2);
    parts.as_slice_mut()[0] = 60;
    assert_eq!([60, 20, 30, 40, 50], parts.as_slice());
    assert_eq!([60, 20], parts.next().unwrap()[..]);
    parts.as_slice_mut()[2] = 70;
    assert_eq!([30, 40, 70], parts.as_slice()[..]);
    assert_eq!([30, 40, 70], parts.next_back().unwrap()[..]);
    assert_eq!(0, parts.len());
}
