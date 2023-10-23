//! This module contains the definition of the solidity ABI types that the
//! library is currently capable of dealing with.

use derivative::Derivative;
use serde::{Deserialize, Serialize};

use crate::utility::U256Wrapper;

/// Concretely known Solidity ABI types and additional informative types.
///
/// # Invariants
///
/// Each individual variant in the enum describes the invariants placed upon it.
/// It is the responsibility of the code constructing these values to ensure
/// that the invariants are satisfied. Code utilising them will assume that the
/// data has been correctly constructed.
///
/// # Missing Solidity Types
///
/// Solidity supports a `fixed` and `ufixed` type in the ABI, but the language
/// support for them is lacking. For that reason we do not include them here for
/// now as there are not enough operations to provide accurate heuristics with
/// which to discover them.
#[derive(Clone, Debug, Derivative, Deserialize, Eq, Serialize)]
#[derivative(PartialEq, Hash)]
#[serde(rename_all = "snake_case")]
pub enum AbiType {
    /// An unknown type, useful for the container types where we know something
    /// is a concrete container but not of what type(s).
    ///
    /// Note that **this is not a valid Solidity type**.
    Any,

    /// A number of a given `size` in bits, where, `8 < size <= 256 &&
    /// size % 8 == 0`.
    ///
    /// This is emitted when the library knows that something has been used
    /// numerically, but does not know whether it is concretely signed or not.
    Number { size: Option<usize> },

    /// Unsigned integers of a given `size` in bits, where `8 < size <= 256 &&
    /// size % 8 == 0`.
    UInt { size: Option<usize> },

    /// Signed (two's complement) integers of a given `size` in bits, where `8 <
    /// size <= 256 && size % 8 == 0`.
    Int { size: Option<usize> },

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
    Bytes { length: Option<usize> },

    /// A value that is used as raw bit data (like [`Self::Bytes`]) but has a
    /// length in bits that is not divisible by
    /// [`crate::constant::BYTE_SIZE_BITS`] to leave no remainder.
    ///
    /// Note that **this is not a valid Solidity type**.
    Bits { length: Option<usize> },

    /// A dynamically-sized array containing elements of a type `tp`.
    DynArray {
        #[serde(rename = "type")]
        tp: Box<AbiType>,
    },

    /// A dynamically-sized byte array, with each element packed.
    DynBytes,

    /// A mapping from `key_type` to `value_type`.
    Mapping { key_type: Box<AbiType>, value_type: Box<AbiType> },

    /// A struct, with the specified `elements`.
    Struct { elements: Vec<StructElement> },

    /// A type in the unifier that resolved to an infinite loop of type
    /// variables.
    ///
    /// Note that **this is not a valid Solidity type**.
    InfiniteType,

    /// A type that could not be concretely resolved due to conflicting
    /// evidence.
    ///
    /// While the conflict is not usually useful itself, treating them as types
    /// ensures that we still complete unification as well as is possible.
    ///
    /// Conflicted types compare equal regardless of the `conflicts` and
    /// `reasons` that they contain.
    ///
    /// Note that **this is not a valid Solidity type**.
    ConflictedType {
        #[derivative(Hash = "ignore", PartialEq = "ignore")]
        conflicts: Vec<String>,
        #[derivative(Hash = "ignore", PartialEq = "ignore")]
        reasons:   Vec<String>,
    },
}

impl AbiType {
    /// Creates an empty conflict.
    ///
    /// This is useful for testing purposes, as conflicted types compare equal
    /// regardless of the payloads they contain.
    #[must_use]
    pub fn conflict() -> Self {
        Self::ConflictedType {
            conflicts: Vec::new(),
            reasons:   Vec::new(),
        }
    }
}

/// An element of a struct in the ABI.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub struct StructElement {
    // The offset for the element.
    pub offset: usize,

    // The type of the element.
    #[serde(rename = "type")]
    pub typ: Box<AbiType>,
}

impl StructElement {
    /// Constructs a new struct element with the provided `typ` at the specified
    /// `offset`.
    #[must_use]
    pub fn new(offset: usize, typ: AbiType) -> Self {
        let typ = Box::new(typ);
        Self { offset, typ }
    }
}

#[cfg(test)]
mod tests {
    use ethnum::U256;
    use serde_json::json;

    use crate::utility::U256Wrapper;

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
