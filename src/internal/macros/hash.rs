#[macro_export]
macro_rules! hash_as_slice {
    ($struct:ident) => {
        impl<T: Hash> Hash for $struct<T> {
            fn hash<H: Hasher>(&self, state: &mut H) {
                Hash::hash(&**self, state);
            }
        }
    };
}
