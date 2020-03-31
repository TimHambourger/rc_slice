extern crate rc_slice;

use std::cell::RefCell;

use rc_slice::RcSlice;

struct DropTracker<'a>(&'static str, &'a RefCell<Vec<&'static str>>);

impl<'a> Drop for DropTracker<'a> {
    fn drop(&mut self) {
        self.1.borrow_mut().push(self.0);
    }
}

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
    let dropped = RefCell::new(Vec::<&str>::new());
    RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped)
    ]);

    dropped.borrow_mut().sort_unstable();
    assert_eq!(&["a", "b", "c"], &dropped.borrow()[..]);
}

#[test]
fn drops_only_when_no_strong_refs() {
    let dropped = RefCell::new(Vec::<&str>::new());

    {
        let slice = RcSlice::from_vec(vec![
            DropTracker("a", &dropped),
            DropTracker("b", &dropped),
            DropTracker("c", &dropped)
        ]);
        {
            let _ = slice.clone();
        }
        // Still 0 even after clone is dropped
        assert_eq!(0, dropped.borrow().len());
    }

    dropped.borrow_mut().sort_unstable();
    assert_eq!(&["a", "b", "c"], &dropped.borrow()[..]);
}

#[test]
fn drops_when_subs_dropped() {
    let dropped = RefCell::new(Vec::<&str>::new());

    {
        let mut slice = RcSlice::from_vec(vec![
            DropTracker("a", &dropped),
            DropTracker("b", &dropped),
            DropTracker("c", &dropped)
        ]);
        {
            RcSlice::split_off_left(&mut slice);
        }
        // We should've dropped the 1 item from the left subslice
        dropped.borrow_mut().sort_unstable();
        assert_eq!(&["a"], &dropped.borrow()[..]);
    }

    dropped.borrow_mut().sort_unstable();
    assert_eq!(&["a", "b", "c"], &dropped.borrow()[..]);
}

#[test]
fn derefs_to_slice() {
    let slice = RcSlice::from_vec(vec![0, 1, 2, 3]);
    assert_eq!(&[0, 1, 2, 3], &*slice);
}

#[test]
fn clone_derefs_to_subslice() {
    let slice = RcSlice::from_vec(vec![0, 1, 2, 3, 4]);
    let left = RcSlice::clone_left(&slice);
    let right = RcSlice::clone_right(&slice);
    assert_eq!(&[0, 1], &*left);
    assert_eq!(&[2, 3, 4], &*right);
}

#[test]
fn get_mut_allows_mutation() {
    let mut slice = RcSlice::from_vec(vec![0, 1, 2, 3]);
    (*RcSlice::get_mut(&mut slice).unwrap())[0] = 4;
    assert_eq!(&[4, 1, 2, 3], &*slice);
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
fn downgrade_then_upgrade() {
    let slice = RcSlice::from_vec(vec![0, 1, 2, 3]);
    let weak_slice = RcSlice::downgrade(&slice);
    assert_eq!(&[0, 1, 2, 3], &*weak_slice.upgrade().unwrap());
}

#[test]
fn downgrade_lets_slice_get_dropped() {
    let dropped = RefCell::new(Vec::<&str>::new());
    let slice = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped)
    ]);
    let weak_slice = RcSlice::downgrade(&slice);

    drop(slice);

    dropped.borrow_mut().sort_unstable();
    assert_eq!(&["a", "b", "c"], &dropped.borrow()[..]);
    assert!(weak_slice.upgrade().is_none());
}

#[test]
fn downgrade_child_then_upgrade() {
    let dropped = RefCell::new(Vec::<&str>::new());
    let parent = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped)
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
    let dropped = RefCell::new(Vec::<&str>::new());
    let parent = RcSlice::from_vec(vec![
        DropTracker("a", &dropped),
        DropTracker("b", &dropped),
        DropTracker("c", &dropped)
    ]);
    let child = RcSlice::clone_right(&parent);
    let weak_parent = RcSlice::downgrade(&parent);

    drop(parent);

    // Dropped left half b/c we dropped the parent
    dropped.borrow_mut().sort_unstable();
    assert_eq!(&["a"], &dropped.borrow()[..]);
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
    assert_eq!(&[3], &*child);
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
    (*slice)[0] = 4;
    assert_eq!(&[4, 1, 2, 3], &*slice);
}

#[test]
fn into_mut_prevents_unsafe_mutation() {
    let mut slice1 = RcSlice::from_vec(vec![0, 1, 2, 3]);
    let slice2 = RcSlice::split_off_right(&mut slice1);
    let slice3 = RcSlice::clone_right(&slice2);
    assert_eq!(&[0, 1], &*RcSlice::into_mut(slice1).unwrap());
    // Can't convert slice2 into mutable b/c its child slice3 is still alive.
    let slice2 = RcSlice::into_mut(slice2).unwrap_err();
    assert_eq!(&[2, 3], &*slice2);
    // Likewise can't convert slice3 into mutable
    let slice3 = RcSlice::into_mut(slice3).unwrap_err();
    assert_eq!(&[3], &*slice3);
    drop(slice2);
    // But now can convert slice3
    assert_eq!(&[3], &*RcSlice::into_mut(slice3).unwrap());
}

#[test]
fn into_mut_tolerates_weak_slices() {
    let slice = RcSlice::from_vec(vec![0, 1, 2, 3, 4]);
    let weak_slice = RcSlice::downgrade(&slice);
    // Conversion into mutable is allowed
    let slice = RcSlice::into_mut(slice).unwrap();
    assert_eq!(&[0, 1, 2, 3, 4], &*slice);
    // And weak_slice is no longer upgradeable
    assert!(weak_slice.upgrade().is_none());
}
