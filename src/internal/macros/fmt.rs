macro_rules! debug_as_slice {
    ($struct: ident) => {
        impl<T: core::fmt::Debug> core::fmt::Debug for $struct<T> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                core::fmt::Debug::fmt(&**self, f)
            }
        }
    };
}

macro_rules! debug_as_items_iter {
    ($struct: ident) => {
        impl<T: core::fmt::Debug> core::fmt::Debug for $struct<T> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_tuple(stringify!($struct))
                    .field(&self.as_slice())
                    .finish()
            }
        }
    };
}

macro_rules! debug_as_parts_iter {
    ($struct: ident) => {
        impl<T: core::fmt::Debug> core::fmt::Debug for $struct<T> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_struct(stringify!($struct))
                    .field("remaining_parts", &self.len())
                    .field("remaining_items", &self.as_slice())
                    .finish()
            }
        }
    };
}
