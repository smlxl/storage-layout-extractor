//! This file contains the definition of the "type expression", which lets us
//! build expressions that describe the type of a value.
//!
//! It is intentionally kept separate from the [`crate::tc::state`] to
//! ensure that you cannot create new type variables without use of the state.

use std::{
    collections::HashSet,
    fmt::{Display, Formatter},
};

use ethnum::U256;
use itertools::Itertools;

use crate::{
    constant::{
        ADDRESS_WIDTH_BITS,
        BOOL_WIDTH_BITS,
        BYTE_SIZE_BITS,
        FUNCTION_WIDTH_BITS,
        SELECTOR_WIDTH_BITS,
    },
    tc::state::type_variable::TypeVariable,
};

/// An alias recommended for use when you have to write it out often.
pub type TE = TypeExpression;

/// The pieces of evidence that can be established through use of heuristics.
///
/// These types are combined through use of a unifier that tries to discover
/// non-conflicting patterns of evidence in the evidence for each value. It is
/// this process that produces the best-known types for the storage slots.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum TypeExpression {
    /// Nothing is known about the type.
    Any,

    /// The type that has this expression ascribed has the same type as `id`.
    Equal { id: TypeVariable },

    /// A word, with `width` and potential `signed`ness.
    Word {
        /// The width of the word in **bits**.
        ///
        /// Note that the width is always encoded in bits internally, with
        /// conversion to bytes for byte-denominated types only occurring at the
        /// output.
        ///
        /// Defaults to [`None`].
        width: Option<usize>,

        /// The way in which the word has been used.
        usage: WordUse,
    },

    /// A dynamic packed byte array, or a `string` given we have no way to
    /// distinguish them at runtime.
    Bytes,

    /// A static array containing items of type `element` and with `length`.
    FixedArray { element: TypeVariable, length: U256 },

    /// A mapping composite type with `key` type and `value` type.
    Mapping { key: TypeVariable, value: TypeVariable },

    /// A dynamic array containing items with the type of `element`.
    DynamicArray { element: TypeVariable },

    /// A type that is a packed encoding of multiple other `types`, and is
    /// possibly a struct.
    Packed { types: Vec<Span>, is_struct: bool },

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

    /// Constructs a new packed encoding containing the provided `types`.
    #[must_use]
    pub fn packed_of(types: Vec<impl Into<Span>>) -> Self {
        let types: Vec<Span> = types.into_iter().map_into().collect();

        Self::Packed {
            types,
            is_struct: false,
        }
    }

    /// Constructs a new struct containing the provided `types`.
    #[must_use]
    pub fn struct_of(types: Vec<impl Into<Span>>) -> Self {
        let types = types.into_iter().map_into().collect();
        Self::Packed {
            types,
            is_struct: true,
        }
    }

    /// Creates a type expression representing a conflict of the `left` and
    /// `right` expressions due to `reason`.
    #[must_use]
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
            Self::Any | Self::Word { .. } | Self::Conflict { .. } | TE::Bytes => false,
            Self::FixedArray { .. }
            | Self::Mapping { .. }
            | Self::DynamicArray { .. }
            | Self::Equal { .. }
            | Self::Packed { .. } => true,
        }
    }
}

impl Display for TypeExpression {
    /// A pretty printer for typing expressions.
    ///
    /// For full details, please use the debug implementation instead. This is
    /// meant for higher-level observation and reasoning, and as such does not
    /// print full type variable identifiers, or the details of conflicted
    /// types.
    ///
    /// # Conventions
    ///
    /// All type representations use `PascalCase` representations so as to
    /// visually contrast with the value representations which use `snake_case`
    /// naming.
    ///
    /// This format uses angle brackets to denote type constructors, and square
    /// brackets to denote constant sizes.
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Any => write!(f, "Any"),
            Self::Equal { id } => write!(f, "Eq<{id}>"),
            Self::Word { width, usage } => {
                if let Some(width) = width {
                    write!(f, "Word<{usage}, {width}>")
                } else {
                    write!(f, "Word<{usage}, ???>")
                }
            }
            Self::Bytes => write!(f, "bytes"),
            Self::FixedArray { element, length } => write!(f, "Array<{element}>[{length}]"),
            Self::Mapping { key, value } => write!(f, "Mapping<{key}, {value}>"),
            Self::DynamicArray { element } => write!(f, "Array<{element}>"),
            Self::Packed { types, is_struct } => {
                if *is_struct {
                    write!(f, "Struct(")?;
                } else {
                    write!(f, "Packed(")?;
                }

                for (i, typ) in types.iter().enumerate() {
                    write!(f, "{typ}")?;

                    if i + 1 != types.len() {
                        write!(f, ", ")?;
                    }
                }

                write!(f, ")")
            }
            Self::Conflict { .. } => write!(f, "Conflicted"),
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

            // Addresses are often used numerically
            (Self::Numeric, Self::Address) | (Self::Address, Self::Numeric) => Self::Address,
            (Self::UnsignedNumeric, Self::Address) | (Self::Address, Self::UnsignedNumeric) => {
                Self::Address
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

impl Display for WordUse {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            Self::Address => "Use::Address",
            Self::Bool => "Use::Bool",
            Self::Function => "Use::Function",
            Self::Bytes => "Use::Bytes",
            Self::Selector => "Use::Selector",
            Self::Numeric => "Use::Number",
            Self::UnsignedNumeric => "Use::Unsigned",
            Self::SignedNumeric => "Use::Signed",
        };
        write!(f, "{str}")
    }
}

/// A representation of a type being at a specific position _inside_ an EVM
/// word.
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Span {
    /// The type variable of the type being positioned inside a word.
    pub typ: TypeVariable,

    /// The offset in bits within the word of `typ`.
    pub offset: usize,

    /// The size in bits within the word of `typ`.
    pub size: usize,
}

impl Span {
    /// Constructs a new span with type `typ` beginning at `offset` bits from
    /// the start of the parent word and extending for `size` bits from that
    /// position.
    ///
    /// Note that `offset` and `size` need not be byte-aligned.
    #[must_use]
    pub fn new(typ: TypeVariable, offset: usize, size: usize) -> Self {
        Self { typ, offset, size }
    }

    /// Gets the type of the span.
    #[must_use]
    pub fn typ(&self) -> TypeVariable {
        self.typ
    }

    /// Gets the offset of the span from the start of the word in bits.
    #[must_use]
    pub fn offset_bits(&self) -> usize {
        self.offset
    }

    /// Gets the offset of the span from the start of the word in bytes.
    #[must_use]
    pub fn offset_bytes(&self) -> usize {
        self.offset / BYTE_SIZE_BITS
    }

    /// Gets the size in bits of the span.
    #[must_use]
    pub fn size_bits(&self) -> usize {
        self.size
    }

    /// Gets the size in bytes of the span.
    #[must_use]
    pub fn size_bytes(&self) -> usize {
        self.size_bits() / BYTE_SIZE_BITS
    }

    /// Gets the bit in the word (zero-indexed) where this span begins.
    #[must_use]
    pub fn start_bit(&self) -> usize {
        self.offset
    }

    /// Gets the bit in the word (zero-indexed) where this span begins.
    #[must_use]
    pub fn start_byte(&self) -> usize {
        self.start_bit() / BYTE_SIZE_BITS
    }

    /// Gets the first bit in the word (zero-indexed) after the end of the span.
    #[must_use]
    pub fn end_bit(&self) -> usize {
        self.offset + self.size
    }

    /// Gets the first byte in the word (zero-indexed) after the end of the
    /// span.
    #[must_use]
    pub fn end_byte(&self) -> usize {
        self.end_bit() / BYTE_SIZE_BITS
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Span({}, {}, {})", self.offset, self.size, self.typ)
    }
}

impl From<&Span> for Span {
    fn from(value: &Span) -> Self {
        *value
    }
}

impl From<Span> for (TypeVariable, usize, usize) {
    fn from(value: Span) -> Self {
        (value.typ, value.offset, value.size)
    }
}

#[cfg(test)]
mod test {
    use crate::{
        constant::{ADDRESS_WIDTH_BITS, BOOL_WIDTH_BITS, FUNCTION_WIDTH_BITS, SELECTOR_WIDTH_BITS},
        tc::expression::WordUse,
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
