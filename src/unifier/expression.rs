//! This file contains the definition of the "type expression", which lets us
//! build expressions that describe the type of a value.
//!
//! It is intentionally kept separate from the [`crate::unifier::state`] to
//! ensure that you cannot create new type variables for it.

use std::collections::HashSet;

use ethnum::U256;

use crate::unifier::{abi::AbiType, state::TypeVariable};

/// An alias recommended for use when you have to write it out often.
pub type TE = TypeExpression;

/// The pieces of evidence that can be established through use of heuristics.
///
/// These types are combined through use of a conflict resolver that tries to
/// discover non-conflicting patterns of evidence in the evidence for each
/// value. It is this process that produces the best-known types for the storage
/// slots.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum TypeExpression {
    /// A representation of the possibly-unbound type of an expression.
    Equal { id: TypeVariable },

    /// A word, with `width` and potential `signed`ness.
    Word {
        /// The width of the word in bits.
        ///
        /// Defaults to [`None`].
        width: Option<usize>,

        /// Whether the word is used as signed.
        ///
        /// Set to [`None`] if the signedness is unknown. Otherwise set to
        /// `true` if signed, and `false` if unsigned.
        signed: Option<bool>,
    },

    /// A static array containing items of type `element` and with `length`.
    FixedArray { element: TypeVariable, length: U256 },

    /// A mapping composite type with `key` type and `value` type.
    Mapping { key: TypeVariable, value: TypeVariable },

    /// A dynamic array containing items with the type of `element`.
    DynamicArray { element: TypeVariable },

    /// A type that has been concretely resolved to an EVM type.
    ConcreteType { ty: AbiType },
}

impl TypeExpression {
    /// Constructs a word with the provided `width` and `size`.
    pub fn word(width: Option<usize>, signed: Option<bool>) -> Self {
        Self::Word { width, signed }
    }

    /// Constructs an unsigned word with the provided `width`.
    pub fn unsigned_word(width: Option<usize>) -> Self {
        let signed = Some(false);
        Self::Word { width, signed }
    }

    /// Constructs a signed word with the provided `width`.
    pub fn signed_word(width: Option<usize>) -> Self {
        let signed = Some(true);
        Self::Word { width, signed }
    }

    /// Constructs an equality wrapping the provided type variable `id`.
    pub fn eq(id: TypeVariable) -> Self {
        Self::Equal { id }
    }

    /// Constructs a new mapping wrapping the `key` and `value` types.
    pub fn mapping(key: TypeVariable, value: TypeVariable) -> Self {
        Self::Mapping { key, value }
    }

    /// Constructs a new dynamic array wrapping the `element` type.
    pub fn dyn_array(element: TypeVariable) -> Self {
        Self::DynamicArray { element }
    }
}

/// A set of typing judgements.
pub type InferenceSet = HashSet<TypeExpression>;
