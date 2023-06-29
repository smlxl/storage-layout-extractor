//! This module contains the definition of the solidity ABI types that the
//! analyzer is currently capable of dealing with.

use ethnum::U256;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Concretely known Solidity ABI types.
///
/// # Invariants
///
/// Each individual variant in the enum describes the invariants placed upon it.
/// It is the responsibility of the code constructing these values to ensure
/// that the invariants are satisfied. Code utilising them will assume that the
/// data has been correctly constructed.
///
/// # Note
///
/// Solidity supports a `fixed` and `ufixed` type in the ABI, but the language
/// support for them is lacking. For that reason we do not include them here for
/// now.
#[derive(Clone, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum AbiType {
    /// An unknown type, useful for the container types where we know something
    /// is a concrete container but not of what type(s).
    Any,

    /// Unsigned integers of a given `size` in bits, where `8 < size <= 256 &&
    /// size % 8 == 0`.
    UInt { size: u16 },

    /// Signed (two's complement) integers of a given `size` in bits, where `8 <
    /// size <= 256 && size % 8 == 0`.
    Int { size: u16 },

    /// Addresses, assumed equivalent to `UInt { size: 160 }` except for
    /// interpretation.
    Address,

    /// A selector, assumed equivalent to `Bytes { length: 4 }` except for
    /// interpretation.
    Selector,

    /// A function, consisting of an [`Self::Address`] followed by a
    /// [`Self::Selector`]. This is semantically equivalent to `Bytes { length:
    /// 24 }`.
    Function,

    /// Booleans, assumed equivalent to `UInt { size: 8 }` except for
    /// interpretation.
    Bool,

    /// A fixed-`size` array containing elements of an element type `tp`.
    Array {
        size: U256Wrapper,
        #[serde(rename = "type")]
        tp:   Box<AbiType>,
    },

    /// Byte arrays of a fixed `length`, where `0 < length <= 32`.
    Bytes { length: u8 },

    /// A dynamically-sized array containing elements of a type `tp`.
    DynArray {
        #[serde(rename = "type")]
        tp: Box<AbiType>,
    },

    /// A dynamically-sized byte array, with each element packed.
    DynBytes,

    /// A mapping from `key_tp` to `val_tp`.
    Mapping {
        #[serde(rename = "key_type")]
        key_tp: Box<AbiType>,
        #[serde(rename = "value_type")]
        val_tp: Box<AbiType>,
    },

    /// A type in the unifier that resolved to an infinite loop of type
    /// variables.
    InfiniteType,

    /// A type that could not be concretely resolved due to conflicting
    /// evidence.
    ///
    /// While the conflict is not usually useful itself, treating them as types
    /// ensures that we still complete unification as well as is possible.
    ConflictedType { left: String, right: String, reason: String },
}

/// The `U256Wrapper` is responsible for serializing the U256 type to JSON
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct U256Wrapper(pub U256);

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

#[cfg(test)]
mod tests {
    use ethnum::U256;
    use serde_json::json;

    use super::U256Wrapper;

    #[test]
    fn can_be_serialized() {
        let value = U256Wrapper(U256::from(0x42_u128));
        let expected = "0x0000000000000000000000000000000000000000000000000000000000000042";
        assert!(
            json!(value).as_str().unwrap().eq(expected),
            "Serialization failed"
        );
    }

    #[test]
    fn can_be_deserialized() {
        let value = U256Wrapper(U256::from(0x42_u128));
        let serialized = json!(value).to_string();
        let value: U256Wrapper = serde_json::from_str(&serialized).unwrap();
        assert!(value.0.as_u8() == 0x42, "Deserialized value is wrong");
    }
}
