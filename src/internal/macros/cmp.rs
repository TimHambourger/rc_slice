#[macro_export]
macro_rules! compare_as_slice {
    ($struct:ident) => {
        impl<A, B> PartialEq<$struct<B>> for $struct<A> where A: PartialEq<B> {
            #[inline]
            fn eq(&self, other: &$struct<B>) -> bool { self[..] == other[..] }
            #[inline]
            fn ne(&self, other: &$struct<B>) -> bool { self[..] != other[..] }
        }

        impl<T: Eq> Eq for $struct<T> { }

        impl<T: PartialOrd> PartialOrd for $struct<T> {
            fn partial_cmp(&self, other: &$struct<T>) -> Option<Ordering> {
                PartialOrd::partial_cmp(&**self, &**other)
            }
        }

        impl<T: Ord> Ord for $struct<T> {
            fn cmp(&self, other: &$struct<T>) -> Ordering {
                Ord::cmp(&**self, &**other)
            }
        }
    };
}
