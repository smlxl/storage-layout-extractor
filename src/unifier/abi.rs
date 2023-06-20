//! This module contains the definition of the solidity ABI types that the
//! analyzer is currently capable of dealing with.

use ethnum::U256;

use crate::unifier::expression::TypeExpression;

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
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
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
    Array { size: U256, tp: Box<AbiType> },

    /// Byte arrays of a fixed `length`, where `0 < length <= 32`.
    Bytes { length: u8 },

    /// A dynamically-sized array containing elements of a type `tp`.
    DynArray { tp: Box<AbiType> },

    /// A dynamically-sized byte array, with each element packed.
    DynBytes,

    /// A mapping from `key_tp` to `val_tp`.
    Mapping { key_tp: Box<AbiType>, val_tp: Box<AbiType> },

    /// A type in the unifier that resolved to an infinite loop of type
    /// variables.
    InfiniteType,

    /// A type that could not be concretely resolved due to conflicting
    /// evidence.
    ///
    /// While the conflict is not usually useful itself, treating them as types
    /// ensures that we still complete unification as well as is possible.
    ConflictedType {
        left:   TypeExpression,
        right:  TypeExpression,
        reason: String,
    },
}
