//! This file contains the definition of the "type expression", which lets us
//! build expressions that describe the type of a value.
//!
//! It is intentionally kept separate from the [`crate::unifier::state`] to
//! ensure that you cannot create new type variables for it.

use std::collections::HashSet;

use serde::Serialize;

use crate::{
    constant::{ADDRESS_WIDTH_BITS, FUNCTION_WIDTH_BITS, SELECTOR_WIDTH_BITS},
    unifier::{state::TypeVariable, u256_wrapper::U256Wrapper},
};

/// An alias recommended for use when you have to write it out often.
pub type TE = TypeExpression;

/// The pieces of evidence that can be established through use of heuristics.
///
/// These types are combined through use of a conflict resolver that tries to
/// discover non-conflicting patterns of evidence in the evidence for each
/// value. It is this process that produces the best-known types for the storage
/// slots.
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize)]
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

        /// Any special way that the word has been used.
        usage: WordUse,
    },

    /// A static array containing items of type `element` and with `length`.
    FixedArray { element: TypeVariable, length: U256Wrapper },

    /// A mapping composite type with `key` type and `value` type.
    Mapping { key: TypeVariable, value: TypeVariable },

    /// A dynamic array containing items with the type of `element`.
    DynamicArray { element: TypeVariable },

    /// A representation of knowing nothing about the type.
    Any,

    /// A representation of two conflicting pieces of evidence.
    Conflict {
        left:   Box<TypeExpression>,
        right:  Box<TypeExpression>,
        reason: String,
    },
}

impl TypeExpression {
    /// Constructs a word with the provided `width` and `signed`.
    #[must_use]
    pub fn word(width: Option<usize>, signed: Option<bool>, usage: WordUse) -> Self {
        Self::Word {
            width,
            signed,
            usage,
        }
    }

    /// Creates a word with no known `width` or `signed`ness.
    #[must_use]
    pub fn default_word() -> Self {
        Self::word(None, None, WordUse::default())
    }

    /// Constructs an unsigned word with the provided `width`.
    #[must_use]
    pub fn unsigned_word(width: Option<usize>) -> Self {
        let signed = Some(false);
        Self::word(width, signed, WordUse::None)
    }

    /// Constructs a signed word with the provided `width`.
    #[must_use]
    pub fn signed_word(width: Option<usize>) -> Self {
        let signed = Some(true);
        Self::word(width, signed, WordUse::None)
    }

    /// Constructs a word that has been used as a boolean.
    #[must_use]
    pub fn bool() -> Self {
        Self::word(None, None, WordUse::Bool)
    }

    /// Constructs a word that has been used as an address.
    #[must_use]
    pub fn address() -> Self {
        let width = Some(ADDRESS_WIDTH_BITS);
        let signed = Some(false);
        Self::word(width, signed, WordUse::Address)
    }

    /// Constructs a word that has been used as a selector.
    #[must_use]
    pub fn selector() -> Self {
        let width = Some(SELECTOR_WIDTH_BITS);
        let signed = Some(false);
        Self::word(width, signed, WordUse::Selector)
    }

    /// Constructs a word that has been used as a function.
    #[must_use]
    pub fn function() -> Self {
        let width = Some(FUNCTION_WIDTH_BITS);
        let signed = Some(false);
        Self::word(width, signed, WordUse::Function)
    }

    /// Constructs an equality wrapping the provided type variable `id`.
    #[must_use]
    pub fn eq(id: TypeVariable) -> Self {
        Self::Equal { id }
    }

    /// Constructs a new mapping wrapping the `key` and `value` types.
    #[must_use]
    pub fn mapping(key: TypeVariable, value: TypeVariable) -> Self {
        Self::Mapping { key, value }
    }

    /// Constructs a new dynamic array wrapping the `element` type.
    #[must_use]
    pub fn dyn_array(element: TypeVariable) -> Self {
        Self::DynamicArray { element }
    }

    /// Creates a type expression representing a conflict of the `left` and
    /// `right` expressions due to `reason`.
    pub fn conflict(left: Self, right: Self, reason: impl Into<String>) -> Self {
        let left = Box::new(left);
        let right = Box::new(right);
        let reason = reason.into();
        Self::Conflict {
            left,
            right,
            reason,
        }
    }

    /// Returns `true` if `self` is a type constructor, otherwise returns
    /// `false`.
    #[must_use]
    pub fn is_type_constructor(&self) -> bool {
        match self {
            Self::Any | Self::Word { .. } | Self::Conflict { .. } => false,
            Self::FixedArray { .. }
            | Self::Mapping { .. }
            | Self::DynamicArray { .. }
            | Self::Equal { .. } => true,
        }
    }
}

/// A set of typing judgements.
pub type InferenceSet = HashSet<TypeExpression>;

/// A representation of the special ways in which a word could be used.
#[derive(Clone, Debug, Eq, Hash, PartialEq, Serialize)]
pub enum WordUse {
    /// The word has no special use.
    None,

    /// The word has been used specifically as a boolean (the result of
    /// `ISZERO`).
    Bool,

    /// The word has been used as the address of a contract.
    Address,

    /// The word has been used as a selector.
    Selector,

    /// The word has been used as a function (an address followed by a
    /// selector).
    Function,

    /// Conflicting usages found.
    Conflict { conflicts: Vec<WordUse> },
}

impl WordUse {
    /// Adds a conflict with `other` for `self`.
    #[must_use]
    pub fn conflict(self, other: Self) -> Self {
        match self {
            Self::Conflict { mut conflicts } => match other {
                Self::Conflict {
                    conflicts: other_conflicts,
                } => {
                    conflicts.extend(other_conflicts);
                    Self::Conflict { conflicts }
                }
                other => {
                    conflicts.push(other);
                    Self::Conflict { conflicts }
                }
            },
            this => match other {
                Self::Conflict { mut conflicts } => {
                    conflicts.push(this);
                    Self::Conflict { conflicts }
                }
                other => Self::Conflict {
                    conflicts: vec![this, other],
                },
            },
        }
    }

    /// Creates a usage conflict of `left` and `right`.
    #[must_use]
    pub fn conflict_of(left: Self, other: Self) -> Self {
        left.conflict(other)
    }

    /// Merges two usages if they are compatible, or returns a conflict if not.
    #[must_use]
    pub fn merge(self, other: Self) -> Self {
        if self == other {
            return self;
        }

        match (self, other) {
            // None can always merge with the other
            (Self::None, other) | (other, Self::None) => other,

            // If they aren't equal, then we have a conflict
            (l, r) => l.conflict(r),
        }
    }
}

impl Default for WordUse {
    fn default() -> Self {
        Self::None
    }
}
