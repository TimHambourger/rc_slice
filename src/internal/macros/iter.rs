#[macro_export]
macro_rules! from_iter_via_vec {
    ($struct:ident) => {
        impl<T> FromIterator<T> for $struct<T> {
            fn from_iter<U>(iter: U) -> Self where U: IntoIterator<Item = T> {
                Vec::from_iter(iter).into()
            }
        }
    };
}
