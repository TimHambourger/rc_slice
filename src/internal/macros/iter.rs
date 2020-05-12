macro_rules! from_iter_via_vec {
    ($struct:ident) => {
        impl<T> core::iter::FromIterator<T> for $struct<T> {
            fn from_iter<U>(iter: U) -> Self where U: core::iter::IntoIterator<Item = T> {
                alloc::vec::Vec::from_iter(iter).into()
            }
        }
    };
}

macro_rules! exact_size_hint {
    () => {
        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            (self.len(), Some(self.len()))
        }
    };
}

macro_rules! exact_count {
    () => {
        #[inline]
        fn count(self) -> usize { self.len() }
    };
}
