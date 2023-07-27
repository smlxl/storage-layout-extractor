//! This file contains the definition of the "type expression", which lets us
//! build expressions that describe the type of a value.
//!
//! It is intentionally kept separate from the [`crate::inference::state`] to
//! ensure that you cannot create new type variables for it.

use std::collections::HashSet;

use ethnum::U256;

use crate::{
    constant::{ADDRESS_WIDTH_BITS, BOOL_WIDTH_BITS, FUNCTION_WIDTH_BITS, SELECTOR_WIDTH_BITS},
    inference::state::TypeVariable,
};

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
    /// A representation of knowing nothing about the type.
    Any,

    /// A representation of the possibly-unbound type of an expression.
    Equal { id: TypeVariable },

    /// A word, with `width` and potential `signed`ness.
    Word {
        /// The width of the word in bits.
        ///
        /// Defaults to [`None`].
        width: Option<usize>,

        /// The way in which the word has been used.
        usage: WordUse,
    },

    /// A static array containing items of type `element` and with `length`.
    FixedArray { element: TypeVariable, length: U256 },

    /// A mapping composite type with `key` type and `value` type.
    Mapping { key: TypeVariable, value: TypeVariable },

    /// A dynamic array containing items with the type of `element`.
    DynamicArray { element: TypeVariable },

    /// A representation of conflicting pieces of evidence.
    Conflict { conflicts: Vec<Box<TypeExpression>>, reasons: Vec<String> },
}

impl TypeExpression {
    /// Constructs a word with the provided `width` and `usage`.
    #[must_use]
    pub fn word(width: Option<usize>, usage: WordUse) -> Self {
        Self::Word { width, usage }
    }

    /// Creates a word that is numeric with the provided `width`.
    #[must_use]
    pub fn numeric(width: Option<usize>) -> Self {
        Self::word(width, WordUse::Numeric)
    }

    /// Constructs an unsigned word with the provided `width`.
    #[must_use]
    pub fn unsigned_word(width: Option<usize>) -> Self {
        Self::word(width, WordUse::UnsignedNumeric)
    }

    /// Constructs a signed word with the provided `width`.
    #[must_use]
    pub fn signed_word(width: Option<usize>) -> Self {
        Self::word(width, WordUse::SignedNumeric)
    }

    /// Constructs a word that has been used as a boolean.
    #[must_use]
    pub fn bool() -> Self {
        let usage = WordUse::Bool;
        Self::word(usage.size(), usage)
    }

    /// Constructs a word that has been used as an address.
    #[must_use]
    pub fn address() -> Self {
        let usage = WordUse::Address;
        Self::word(usage.size(), usage)
    }

    /// Constructs a word that has been used as a selector.
    #[must_use]
    pub fn selector() -> Self {
        let usage = WordUse::Selector;
        Self::word(usage.size(), usage)
    }

    /// Constructs a word that has been used as a function.
    #[must_use]
    pub fn function() -> Self {
        let usage = WordUse::Function;
        Self::word(usage.size(), usage)
    }

    /// Constructs a word that is actually used as one of the fixed-size byte
    /// arrays.
    ///
    /// Note that even though `bytesN` is traditionally denominated in a number
    /// of bytes, here the width is still specified in _bits_ as per the unified
    /// [`Self::Word`] representation of the type language.
    #[must_use]
    pub fn bytes(width: Option<usize>) -> Self {
        Self::word(width, WordUse::Bytes)
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
        left.conflict_with(right, reason)
    }

    /// Conflicts `self` with `other`, combining the conflicts if necessary.
    #[must_use]
    pub fn conflict_with(self, other: Self, reason: impl Into<String>) -> Self {
        let mut all_conflicts = Vec::new();
        let mut all_reasons = vec![reason.into()];

        let mut gather_expressions = |expr| match expr {
            Self::Conflict { conflicts, reasons } => {
                all_conflicts.extend(conflicts);
                all_reasons.extend(reasons);
            }
            a => all_conflicts.push(Box::new(a)),
        };

        gather_expressions(self);
        gather_expressions(other);

        Self::Conflict {
            conflicts: all_conflicts,
            reasons:   all_reasons,
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
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum WordUse {
    /// The word is used as data (equivalent to `bytesN`) where we know nothing
    /// more about it.
    Bytes,

    /// The word is used numerically, but is not known to be signed or unsigned.
    Numeric,

    /// The word is used numerically and is unsigned.
    UnsignedNumeric,

    /// The word is used numerically and is signed.
    SignedNumeric,

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
}

impl WordUse {
    /// Converts the usage to the appropriate size in bits if it has an
    /// associated size.
    #[must_use]
    pub fn size(&self) -> Option<usize> {
        Some(match self {
            Self::Bool => BOOL_WIDTH_BITS,
            Self::Address => ADDRESS_WIDTH_BITS,
            Self::Selector => SELECTOR_WIDTH_BITS,
            Self::Function => FUNCTION_WIDTH_BITS,
            _ => return None,
        })
    }

    /// Checks if `self` represents a definitely-signed usage of a word.
    #[must_use]
    pub fn is_definitely_signed(&self) -> bool {
        matches!(self, Self::SignedNumeric)
    }

    /// Merges two usages if they are compatible, or returns [`None`] if they
    /// are not.
    #[must_use]
    pub fn merge(self, other: Self) -> Option<Self> {
        if self == other {
            return Some(self);
        }

        Some(match (self, other) {
            // Data can always be merged with anything that is more specific.
            (Self::Bytes, other) | (other, Self::Bytes) => other,

            // Merge the numeric options
            (Self::Numeric, Self::UnsignedNumeric) | (Self::UnsignedNumeric, Self::Numeric) => {
                Self::UnsignedNumeric
            }
            (Self::Numeric, Self::SignedNumeric) | (Self::SignedNumeric, Self::Numeric) => {
                Self::SignedNumeric
            }

            _ => return None,
        })
    }
}

impl Default for WordUse {
    fn default() -> Self {
        Self::Bytes
    }
}

#[cfg(test)]
mod test {
    use crate::{
        constant::{ADDRESS_WIDTH_BITS, BOOL_WIDTH_BITS, FUNCTION_WIDTH_BITS, SELECTOR_WIDTH_BITS},
        inference::expression::WordUse,
    };

    #[test]
    fn returns_correct_sizes() {
        assert_eq!(WordUse::Bytes.size(), None);
        assert_eq!(WordUse::Numeric.size(), None);
        assert_eq!(WordUse::UnsignedNumeric.size(), None);
        assert_eq!(WordUse::SignedNumeric.size(), None);
        assert_eq!(WordUse::Bool.size(), Some(BOOL_WIDTH_BITS));
        assert_eq!(WordUse::Address.size(), Some(ADDRESS_WIDTH_BITS));
        assert_eq!(WordUse::Selector.size(), Some(SELECTOR_WIDTH_BITS));
        assert_eq!(WordUse::Function.size(), Some(FUNCTION_WIDTH_BITS));
    }

    #[test]
    fn returns_correct_signedness() {
        assert!(!WordUse::Bytes.is_definitely_signed());
        assert!(!WordUse::Numeric.is_definitely_signed());
        assert!(!WordUse::UnsignedNumeric.is_definitely_signed());
        assert!(WordUse::SignedNumeric.is_definitely_signed());
        assert!(!WordUse::Bool.is_definitely_signed());
        assert!(!WordUse::Address.is_definitely_signed());
        assert!(!WordUse::Selector.is_definitely_signed());
        assert!(!WordUse::Function.is_definitely_signed());
    }

    #[test]
    fn bytes_overridden_by_all_others_in_merge() {
        assert_eq!(
            WordUse::Bytes.merge(WordUse::Numeric),
            Some(WordUse::Numeric)
        );
        assert_eq!(
            WordUse::Bytes.merge(WordUse::UnsignedNumeric),
            Some(WordUse::UnsignedNumeric)
        );
        assert_eq!(
            WordUse::Bytes.merge(WordUse::SignedNumeric),
            Some(WordUse::SignedNumeric)
        );
        assert_eq!(WordUse::Bytes.merge(WordUse::Bool), Some(WordUse::Bool));
        assert_eq!(
            WordUse::Bytes.merge(WordUse::Address),
            Some(WordUse::Address)
        );
        assert_eq!(
            WordUse::Bytes.merge(WordUse::Selector),
            Some(WordUse::Selector)
        );
        assert_eq!(
            WordUse::Bytes.merge(WordUse::Function),
            Some(WordUse::Function)
        );
    }

    #[test]
    fn unsigned_numeric_overrides_numeric() {
        assert_eq!(
            WordUse::Numeric.merge(WordUse::UnsignedNumeric),
            Some(WordUse::UnsignedNumeric)
        );
        assert_eq!(
            WordUse::UnsignedNumeric.merge(WordUse::Numeric),
            Some(WordUse::UnsignedNumeric)
        );
    }

    #[test]
    fn signed_numeric_overrides_numeric() {
        assert_eq!(
            WordUse::Numeric.merge(WordUse::SignedNumeric),
            Some(WordUse::SignedNumeric)
        );
        assert_eq!(
            WordUse::SignedNumeric.merge(WordUse::Numeric),
            Some(WordUse::SignedNumeric)
        );
    }

    #[test]
    fn signed_numeric_conflicts_with_unsigned_numeric() {
        assert!(WordUse::UnsignedNumeric.merge(WordUse::SignedNumeric).is_none());
        assert!(WordUse::SignedNumeric.merge(WordUse::UnsignedNumeric).is_none());
    }

    #[test]
    fn returns_none_for_conflict() {
        assert!(WordUse::Address.merge(WordUse::Bool).is_none());
    }
}
