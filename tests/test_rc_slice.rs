extern crate rc_slice;

use std::cell::Cell;

use rc_slice::RcSlice;

#[derive(Clone)]
struct DropCounter<'a>(&'a Cell<u32>);

impl<'a> Drop for DropCounter<'a> {
    fn drop(&mut self) {
        self.0.set(self.0.get() + 1);
    }
}


#[test]
fn drops_its_data() {
    let drop_count = Cell::new(0);

    {
        let slice = RcSlice::from_vec(vec![DropCounter(&drop_count); 3]);
        assert_eq!(0, drop_count.get());
    }

    assert_eq!(3, drop_count.get());
}

#[test]
fn respects_strong_count() {
    let drop_count = Cell::new(0);

    {
        let slice = RcSlice::from_vec(vec![DropCounter(&drop_count); 3]);
        {
            let clone = slice.clone();
        }
        // Still 0 even after clone is dropped
        assert_eq!(0, drop_count.get());
    }

    assert_eq!(3, drop_count.get());
}
