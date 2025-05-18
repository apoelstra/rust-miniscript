// SPDX-License-Identifier: CC0-1.0

//! Macros
//!
//! Macros meant to be used inside the Rust Miniscript library

/// Allows tests to create a miniscript directly from string as
/// `ms_str!("c:or_i(pk({}),pk({}))", pk1, pk2)`
#[cfg(test)]
macro_rules! ms_str {
    ($($arg:tt)*) => (Miniscript::from_str_with_validation_params(&format!($($arg)*), &$crate::ValidationParams::MAX).unwrap())
}

/// Allows tests to create a concrete policy directly from string as
/// `policy_str!("wsh(c:or_i(pk({}),pk({})))", pk1, pk2)`
#[cfg(all(feature = "compiler", test))]
macro_rules! policy_str {
    ($($arg:tt)*) => ($crate::policy::Concrete::from_str(&format!($($arg)*)).unwrap())
}

/// A macro that implements serde serialization and deserialization using the
/// `fmt::Display` and `str::FromStr` traits.
macro_rules! serde_string_impl_pk {
    ($name:ident, $expecting:expr $(, $gen:ident; $gen_con:ident)*) => {
        #[cfg(feature = "serde")]
        impl<'de, Pk $(, $gen)*> $crate::serde::Deserialize<'de> for $name<Pk $(, $gen)*>
        where
            Pk: $crate::FromStrKey,
            $($gen : $gen_con,)*
        {
            fn deserialize<D>(deserializer: D) -> Result<$name<Pk $(, $gen)*>, D::Error>
            where
                D: $crate::serde::de::Deserializer<'de>,
            {
                use core::fmt::{self, Formatter};
                use core::marker::PhantomData;
                use core::str::FromStr;

                #[allow(unused_parens)]
                struct Visitor<Pk $(, $gen)*>(PhantomData<(Pk $(, $gen)*)>);
                impl<'de, Pk $(, $gen)*> $crate::serde::de::Visitor<'de> for Visitor<Pk $(, $gen)*>
                where
                    Pk: $crate::FromStrKey,
                    $($gen: $gen_con,)*
                {
                    type Value = $name<Pk $(, $gen)*>;

                    fn expecting(&self, formatter: &mut Formatter) -> fmt::Result {
                        formatter.write_str($expecting)
                    }

                    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
                    where
                        E: $crate::serde::de::Error,
                    {
                        $name::from_str(v).map_err(E::custom)
                    }

                    fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
                    where
                        E: $crate::serde::de::Error,
                    {
                        self.visit_str(v)
                    }

                    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
                    where
                        E: $crate::serde::de::Error,
                    {
                        self.visit_str(&v)
                    }
                }

                deserializer.deserialize_str(Visitor(PhantomData))
            }
        }

        #[cfg(feature = "serde")]
        impl<'de, Pk $(, $gen)*> $crate::serde::Serialize for $name<Pk $(, $gen)*>
        where
            Pk: $crate::MiniscriptKey,
            $($gen: $gen_con,)*
        {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: $crate::serde::Serializer,
            {
                serializer.collect_str(&self)
            }
        }
    };
}
