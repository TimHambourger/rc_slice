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
        assert!(RcSlice::get_mut(&mut slice1).is_some());
        assert!(RcSlice::get_mut(&mut slice2).is_none());
        assert!(RcSlice::get_mut(&mut slice3).is_none());
    }
    assert!(RcSlice::get_mut(&mut slice1).is_some());
    assert!(RcSlice::get_mut(&mut slice2).is_some());
}
