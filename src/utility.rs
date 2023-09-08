//! Utility functions useful throughout the codebase.

use std::{
    cmp::Ordering,
    fmt::{Debug, Formatter},
};

use ethnum::U256;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use uuid::Uuid;

use crate::vm::value::known::KnownWord;

/// Formats a UUID as the first 16 bytes in hex, rather than the full thing.
/// This allows for more-compact printing.
#[must_use]
pub fn clip_uuid(uuid: &Uuid) -> String {
    let string = format!("{uuid}");
    string[0..8].to_string()
}

/// A type alias to make [`U256Wrapper`] easier to type internally.
pub type U256W = U256Wrapper;

/// The `U256Wrapper` is responsible for allowing the serialisation of the
/// [`U256`] type to JSON.
///
/// It provides reasonable conversions from a number of common types used within
/// the library.
#[derive(Clone, Copy, Default, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct U256Wrapper(pub U256);

impl Debug for U256Wrapper {
    /// The wrapper has absolutely no semantic meaning, so we print the
    /// underlying value for the debug representation.
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl PartialOrd for U256Wrapper {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Ord for U256Wrapper {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl From<U256> for U256Wrapper {
    fn from(value: U256) -> Self {
        Self(value)
    }
}

impl From<U256Wrapper> for U256 {
    fn from(U256Wrapper(value): U256Wrapper) -> Self {
        value
    }
}

impl From<KnownWord> for U256Wrapper {
    fn from(value: KnownWord) -> Self {
        Self(value.value_le())
    }
}

impl From<&KnownWord> for U256Wrapper {
    fn from(value: &KnownWord) -> Self {
        Self(value.value_le())
    }
}

impl From<U256Wrapper> for KnownWord {
    fn from(value: U256Wrapper) -> Self {
        KnownWord::from_le(value.0)
    }
}

impl From<usize> for U256Wrapper {
    fn from(value: usize) -> Self {
        Self(U256::from(value as u128))
    }
}

impl Serialize for U256Wrapper {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut value = String::from("0x");
        value.push_str(&hex::encode(self.0.to_be_bytes()));

        serializer.serialize_str(&value)
    }
}

impl<'de> Deserialize<'de> for U256Wrapper {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s: String = Deserialize::deserialize(deserializer)?;
        let u256 = U256::from_str_hex(&s).map_err(serde::de::Error::custom)?;
        Ok(U256Wrapper(u256))
    }
}
