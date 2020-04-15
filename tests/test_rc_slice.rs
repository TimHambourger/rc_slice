extern crate rc_slice;

mod test_utils;

use std::{
    cell::RefCell,
    collections::hash_map::HashMap,
};

use rc_slice::RcSlice;
use test_utils::DropTracker;

#[test]
fn is_covariant() {
    #[allow(unused_variables)]
    fn use_slice<'a>(n: &'a u32, slice: &RcSlice<&'a u32>) {
    }

    let slice = RcSlice::from_vec(vec![&0]);
    // Important that x is declared after slice.
    let x = 0;
    // If RcSlice<T> were invariant in T, then the next line would give
    // error[E0597]: `x` does not live long enough
    //   --> tests/test_rc_slice.rs:37:15
    //    |
    // 37 |     use_slice(&x, &slice)
    //    |               ^^ borrowed value does not live long enough
    // 38 | }
    //    | -
    //    | |
    //    | `x` dropped here while still borrowed
    //    | borrow might be used here, when `slice` is dropped and runs the destructor for type `rc_slice::RcSlice<&u32>`
    //    |
    //    = note: values in a scope are dropped in the opposite order they are defined
    use_slice(&x, &slice)
}

#[test]
fn drops_its_data() {
    let dropped = RefCell::new(Vec::new());
    RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);

    dropped.borrow_mut().sort_unstable();
    assert_eq!(["a", "b", "c"], dropped.borrow()[..]);
}

#[test]
fn drops_only_when_no_strong_refs() {
    let dropped = RefCell::new(Vec::new());
    let slice = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    let clone = slice.clone();
    drop(clone);
    // Still 0 even after clone is dropped
    assert_eq!(0, dropped.borrow().len());
    drop(slice);
    dropped.borrow_mut().sort_unstable();
    assert_eq!(["a", "b", "c"], dropped.borrow()[..]);
}

#[test]
fn drops_when_subs_dropped() {
    let dropped = RefCell::new(Vec::new());
    let mut slice = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    RcSlice::split_off_left(&mut slice);
    // We should've dropped the 1 item from the left subslice
    dropped.borrow_mut().sort_unstable();
    assert_eq!(["a"], dropped.borrow()[..]);
    drop(slice);
    dropped.borrow_mut().sort_unstable();
    assert_eq!(["a", "b", "c"], dropped.borrow()[..]);
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
fn split_into_parts_basic() {
    let dropped = RefCell::new(Vec::new());
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
fn split_into_various_parts() {
    let slice = RcSlice::from_vec(vec![0, 1, 2, 3, 4, 5]);

    // Split in 1
    let mut parts = RcSlice::split_into_parts(slice.clone(), 1);
    assert_eq!([0, 1, 2, 3, 4, 5], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());

    // Split in 2
    let mut parts = RcSlice::split_into_parts(slice.clone(), 2);
    assert_eq!([0, 1, 2], parts.next().unwrap()[..]);
    assert_eq!([3, 4, 5], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());

    // Split in 4
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1, 2], parts.next().unwrap()[..]);
    assert_eq!([3], parts.next().unwrap()[..]);
    assert_eq!([4, 5], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());

    // Split in 8
    let mut parts = RcSlice::split_into_parts(slice.clone(), 8);
    assert_eq!(0, parts.next().unwrap().len());
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next().unwrap()[..]);
    assert_eq!(0, parts.next().unwrap().len());
    assert_eq!([3], parts.next().unwrap()[..]);
    assert_eq!([4], parts.next().unwrap()[..]);
    assert_eq!([5], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
}

#[test]
fn split_into_parts_front_and_back() {
    let slice = RcSlice::from_vec(vec![0, 1, 2, 3]);

    // All possible "walks" (sequences of next/next_back calls) for a split
    // into 4 parts, excluding the walk consisting purely of next calls,
    // since we have other tests that focus just on forward iteration.
    // 2 ^ 4 - 1 = 15 different walks.

    // Walk #1: next, next, next, next_back
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next().unwrap()[..]);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #2: next, next, next_back, next
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #3: next, next, next_back, next_back
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #4: next, next_back, next, next
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #5: next, next_back, next, next_back
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #6: next, next_back, next_back, next
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #7: next, next_back, next_back, next_back
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #8: next_back, next, next, next
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #9: next_back, next, next, next_back
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #10: next_back, next, next_back, next
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #11: next_back, next, next_back, next_back
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #12: next_back, next_back, next, next
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #13: next_back, next_back, next, next_back
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #14: next_back, next_back, next_back, next
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());

    // Walk #15: next_back, next_back, next_back, next_back
    let mut parts = RcSlice::split_into_parts(slice.clone(), 4);
    assert_eq!([3], parts.next_back().unwrap()[..]);
    assert_eq!([2], parts.next_back().unwrap()[..]);
    assert_eq!([1], parts.next_back().unwrap()[..]);
    assert_eq!([0], parts.next_back().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());
}

#[test]
fn split_into_parts_sample_32() {
    let mut v = Vec::with_capacity(32);
    for i in 0..32 { v.push(i); }
    let slice = RcSlice::from_vec(v);
    let mut parts = RcSlice::split_into_parts(slice, 32);
    // One particular "walk" of 32 next/next_back calls. Nothing special
    // about this walk vs any other. Just want a test that uses both
    // next and next_back and deals w/ a higher num_parts than our other
    // tests.
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([1], parts.next().unwrap()[..]);
    assert_eq!([2], parts.next().unwrap()[..]);
    assert_eq!([31], parts.next_back().unwrap()[..]);
    assert_eq!([3], parts.next().unwrap()[..]);
    assert_eq!([30], parts.next_back().unwrap()[..]);
    assert_eq!([4], parts.next().unwrap()[..]);
    assert_eq!([29], parts.next_back().unwrap()[..]);
    assert_eq!([28], parts.next_back().unwrap()[..]);
    assert_eq!([5], parts.next().unwrap()[..]);
    assert_eq!([6], parts.next().unwrap()[..]);
    assert_eq!([27], parts.next_back().unwrap()[..]);
    assert_eq!([7], parts.next().unwrap()[..]);
    assert_eq!([26], parts.next_back().unwrap()[..]);
    assert_eq!([8], parts.next().unwrap()[..]);
    assert_eq!([25], parts.next_back().unwrap()[..]);
    assert_eq!([9], parts.next().unwrap()[..]);
    assert_eq!([24], parts.next_back().unwrap()[..]);
    assert_eq!([23], parts.next_back().unwrap()[..]);
    assert_eq!([10], parts.next().unwrap()[..]);
    assert_eq!([22], parts.next_back().unwrap()[..]);
    assert_eq!([11], parts.next().unwrap()[..]);
    assert_eq!([12], parts.next().unwrap()[..]);
    assert_eq!([13], parts.next().unwrap()[..]);
    assert_eq!([21], parts.next_back().unwrap()[..]);
    assert_eq!([14], parts.next().unwrap()[..]);
    assert_eq!([20], parts.next_back().unwrap()[..]);
    assert_eq!([15], parts.next().unwrap()[..]);
    assert_eq!([16], parts.next().unwrap()[..]);
    assert_eq!([17], parts.next().unwrap()[..]);
    assert_eq!([19], parts.next_back().unwrap()[..]);
    assert_eq!([18], parts.next().unwrap()[..]);
    assert!(parts.next().is_none());
    assert!(parts.next_back().is_none());
}

#[test]
#[should_panic(expected = "power of 2")]
fn split_into_parts_not_power_of_2() {
    let slice = RcSlice::from_vec(vec![0]);
    RcSlice::split_into_parts(slice, 30);
}

#[test]
#[should_panic(expected = "> 0")]
fn split_into_zero_parts() {
    let slice = RcSlice::from_vec(vec![0]);
    RcSlice::split_into_parts(slice, 0);
}

#[test]
fn rc_slice_parts_as_slice() {
    let slice = RcSlice::from_vec(vec![0, 5, 10, 15, 20]);
    let mut parts = RcSlice::split_into_parts(slice, 4);
    assert_eq!([0, 5, 10, 15, 20], parts.as_slice());
    assert_eq!([0], parts.next().unwrap()[..]);
    assert_eq!([5, 10, 15, 20], parts.as_slice());
    assert_eq!([15, 20], parts.next_back().unwrap()[..]);
    assert_eq!([5, 10], parts.as_slice());
    assert_eq!([10], parts.next_back().unwrap()[..]);
    assert_eq!([5], parts.as_slice());
    assert_eq!([5], parts.next().unwrap()[..]);
    assert_eq!(0, parts.len());
    assert_eq!(0, parts.as_slice().len());
}

#[test]
fn clone_rc_slice_parts() {
    let dropped = RefCell::new(Vec::new());
    let slice = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    let mut parts = RcSlice::split_into_parts(slice, 2);
    assert_eq!(["a"], parts.next().unwrap()[..]);
    assert_eq!(["a"], dropped.borrow()[..]);
    assert_eq!(1, parts.len());

    let mut clone = parts.clone();
    // Cloned iterator matches iteration state of original iterator.
    assert_eq!(1, clone.len());
    assert_eq!(["b", "c"], parts.next().unwrap()[..]);
    // We haven't dropped the righthand items yet since we cloned the iterator.
    assert_eq!(["a"], dropped.borrow()[..]);
    assert_eq!(["b", "c"], clone.next().unwrap()[..]);
    // Now we've dropped
    dropped.borrow_mut().sort_unstable();
    assert_eq!(["a", "b", "c"], dropped.borrow()[..]);
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
}

#[test]
fn ord_compares_as_slice() {
    let mut slice = RcSlice::from_vec(vec![0, 2, 1, 1]);
    let left = RcSlice::split_off_left(&mut slice);
    assert!(left < slice);
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
    let dropped = RefCell::new(Vec::new());
    let slice = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    let weak_slice = RcSlice::downgrade(&slice);

    drop(slice);

    dropped.borrow_mut().sort_unstable();
    assert_eq!(["a", "b", "c"], dropped.borrow()[..]);
    assert!(weak_slice.upgrade().is_none());
}

#[test]
fn downgrade_child_then_upgrade() {
    let dropped = RefCell::new(Vec::new());
    let parent = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    let child = RcSlice::clone_right(&parent);
    let weak_child = RcSlice::downgrade(&child);

    drop(child);
    // Nothing dropped b/c parent still alive.
    assert_eq!(0, dropped.borrow().len());
    // And fact that parent is still alive is enough that weak_child
    // should be upgradeable.
    assert!(weak_child.upgrade().is_some());
}

#[test]
fn downgrade_parent_then_upgrade() {
    let dropped = RefCell::new(Vec::new());
    let parent = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    let child = RcSlice::clone_right(&parent);
    let weak_parent = RcSlice::downgrade(&parent);

    drop(parent);

    // Dropped left half b/c we dropped the parent
    dropped.borrow_mut().sort_unstable();
    assert_eq!(["a"], dropped.borrow()[..]);
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
    let dropped = RefCell::new(Vec::new());
    let slice = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped),
    ]);
    // Create some child slices to exercise the recursive logic in
    // RcSliceData::forget_items.
    RcSlice::clone_left(&RcSlice::clone_right(&slice));
    RcSlice::clone_left(&slice);
    assert_eq!(0, dropped.borrow().len());
    let slice_mut = RcSlice::into_mut(slice).unwrap();
    // Not dropped yet
    assert_eq!(0, dropped.borrow().len());
    drop(slice_mut);
    // Now items are dropped
    dropped.borrow_mut().sort_unstable();
    assert_eq!(["a", "b", "c"], dropped.borrow()[..]);
}
