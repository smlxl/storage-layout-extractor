//! This module contains the definition of the solidity ABI types that the
//! analyzer is currently capable of dealing with.

use ethnum::U256;

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
    /// Unsigned integers of a given `size` in bits, where `8 < size <= 256 &&
    /// size % 8 == 0`.
    UInt { size: u16 },

    /// Signed (two's complement) integers of a given `size` in bits, where `8 <
    /// size <= 256 && size % 8 == 0`.
    Int { size: u16 },

    /// Addresses, assumed equivalent to `UInt { size: 160 }` except for
    /// interpretation.
    Address,

    /// Booleans, assumed equivalent to `UInt { size: 8 }` except for
    /// interpretation.
    Bool,

    /// Byte arrays of a fixed `length`, where `0 < length <= 32`.
    Bytes { length: u8 },

    /// A selector, assumed equivalent to `Bytes { length: 4 }` except for
    /// interpretation.
    Selector,

    /// A function, consisting of an [`Self::Address`] followed by a
    /// [`Self::Selector`]. This is semantically equivalent to `Bytes { length:
    /// 24 }`.
    Function,

    /// A fixed-`size` array containing elements of an element type `tp`.
    Array { size: U256, tp: Box<AbiType> },

    /// A dynamically-sized byte array, with each element packed.
    DynBytes,

    /// A dynamically-sized array containing elements of a type `tp`.
    DynArray { tp: Box<AbiType> },

    /// A mapping from `key_tp` to `val_tp`.
    Mapping { key_tp: Box<AbiType>, val_tp: Box<AbiType> },

    /// An unknown type, useful for the container types where we know something
    /// is a concrete container but not of what type(s).
    Any,
}
