#[macro_export]
macro_rules! borrow_as_slice {
    ($struct: ident) => {
        impl<T> AsRef<[T]> for $struct<T> {
            #[inline]
            fn as_ref(&self) -> &[T] { self }
        }

        impl<T> Borrow<[T]> for $struct<T> {
            #[inline]
            fn borrow(&self) -> &[T] { self }
        }
    };
}

#[macro_export]
macro_rules! borrow_mut_as_slice {
    ($struct:ident) => {
        impl<T> AsMut<[T]> for $struct<T> {
            #[inline]
            fn as_mut(&mut self) -> &mut [T] { self }
        }

        impl<T> BorrowMut<[T]> for $struct<T> {
            #[inline]
            fn borrow_mut(&mut self) -> &mut [T] { self }
        }
    };
}
