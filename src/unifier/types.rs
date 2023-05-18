//! This file contains information about the ABI types of the EVM.

use ethnum::U256;

/// The type representations that this analysis can figure out.
///
/// These types span the gamut from types that are concretely resolved to EVM
/// types, to those that very little (or nothing) is known about.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Type {
    /// A type that has been concretely resolved to an EVM type.
    ConcreteType { ty: AbiType },

    /// A type that is used as a numeric.
    Numeric,

    /// A type that is known to have a fixed width and be unsigned.
    UnsignedFixedWidth { width: u16 },

    /// A type that is known to have a fixed width and be signed.
    SignedFixedWidth { width: u16 },

    /// A type known to be a fixed-length array but not with a known element
    /// type.
    UnknownFixedArray { length: U256 },

    /// A dynamic array with unknown element type.
    UnknownDynamicArray,

    /// The type of a value where nothing is known about the type other than its
    /// existence.
    Any,
}

/// Concretely known Solidity ABI types.
///
/// # Note
///
/// Solidity supports a `fixed` and `ufixed` type in the ABI, but the language
/// support for them is lacking. For that reason we do not include them here for
/// now.
#[derive(Clone, Debug, Eq, PartialEq)]
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
