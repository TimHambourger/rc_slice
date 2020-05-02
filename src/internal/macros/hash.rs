macro_rules! hash_as_slice {
    ($struct:ident) => {
        impl<T: core::hash::Hash> core::hash::Hash for $struct<T> {
            fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
                core::hash::Hash::hash(&**self, state);
            }
        }
    };
}
