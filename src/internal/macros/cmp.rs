#[macro_export]
macro_rules! compare_as_slice {
    ($struct:ident) => {
        impl<A, B> core::cmp::PartialEq<$struct<B>> for $struct<A> where A: core::cmp::PartialEq<B> {
            #[inline]
            fn eq(&self, other: &$struct<B>) -> bool { self[..] == other[..] }
            #[inline]
            fn ne(&self, other: &$struct<B>) -> bool { self[..] != other[..] }
        }

        impl<T: core::cmp::Eq> core::cmp::Eq for $struct<T> { }

        impl<T: core::cmp::PartialOrd> core::cmp::PartialOrd for $struct<T> {
            fn partial_cmp(&self, other: &$struct<T>) -> Option<core::cmp::Ordering> {
                core::cmp::PartialOrd::partial_cmp(&**self, &**other)
            }
        }

        impl<T: core::cmp::Ord> core::cmp::Ord for $struct<T> {
            fn cmp(&self, other: &$struct<T>) -> core::cmp::Ordering {
                core::cmp::Ord::cmp(&**self, &**other)
            }
        }
    };
}
