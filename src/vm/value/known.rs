#![cfg(target_endian = "little")]
//! This module contains a representation of concrete word values for the EVM
//! that can be known and manipulated statically.
//!
//! # Endianness
//!
//! As this module currently assumes a platform endianness of little-endian, it
//! will intentionally fail to compile if compiled for a big-endian architecture
//! in order to prevent subtle bugs.

use std::{
    fmt::{Display, Formatter},
    mem,
};

use bitvec::{
    prelude::{BitVec, Lsb0},
    view::BitView,
};
use ethnum::{I256, U256};

/// The type of data whose value is concretely known during symbolic execution.
///
/// # Representation
///
/// At the low level at which this extractor works, all values on the EVM are
/// just bags of bits in a 256-bit word. Operations on a `KnownValue` may treat
/// this word numerically in a signed or unsigned fashion. Such numeric
/// operations are, where possible, implemented in terms of standard operators
/// to provide a natural usage experience.
///
/// # Endianness
///
/// Internally, the value of the word is stored in platform (little-endian)
/// endianness (see above).
///
/// When altering this code, be very careful to understand which operations on
/// the underlying value actually alter the underlying data based on that
/// platform assumption. Functions like `to_{le,be}` and
/// `{to,from}_{le,be}_bytes` perform no conversion when converting to and from
/// platform endianness (LE in our case), but functions like `swap_bytes` will
/// always swap.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct KnownWord {
    value: U256,
}

impl KnownWord {
    /// Creates a known value representing zero as a 256-bit wide unsigned
    /// integer.
    #[must_use]
    pub fn zero() -> Self {
        Self::from_le(0x0u8)
    }

    /// Constructs a new `KnownWord` from `value` where the value is using
    /// little-endian byte ordering.
    #[must_use]
    pub fn from_le(value: impl Into<U256>) -> Self {
        // If it is LE we already have the correct byte ordering, so we just convert
        let value = value.into();
        Self { value }
    }

    /// Constructs a new `KnownWord` from `value` where the value is using
    /// big-endian byte ordering.
    #[must_use]
    pub fn from_be(value: impl Into<U256>) -> Self {
        // This unconditionally swaps the byte ordering to match the platform
        // endianness.
        let value = value.into().swap_bytes();
        Self { value }
    }

    /// Constructs a new `KnownWord` from `value` where the value is using
    /// little-endian byte ordering.
    #[must_use]
    pub fn from_le_signed(value: impl Into<I256>) -> Self {
        // As it is LE we already have the correct byte ordering, so we can just
        // reinterpret the bytes directly
        let value = U256::from_ne_bytes(value.into().to_ne_bytes());
        Self { value }
    }

    /// Constructs a new `KnownWord` from `value` where the value is using
    /// big-endian byte ordering.
    #[must_use]
    pub fn from_be_signed(value: impl Into<I256>) -> Self {
        // Here we want to reinterpret the existing (claimed big-endian) bytes into
        // little endian, so we convert on ingest but take the pattern as is otherwise
        let value = U256::from_be_bytes(value.into().to_ne_bytes());
        Self { value }
    }

    /// Constructs a new `KnownWord` from `bytes` where the bytes use
    /// little-endian ordering.
    #[must_use]
    pub fn from_le_bytes(bytes: impl Into<[u8; mem::size_of::<Self>()]>) -> Self {
        // Here we can take the bytes in the order they come in
        let value = U256::from_le_bytes(bytes.into());
        Self { value }
    }

    /// Constructs a new `KnownWord` from `bytes` where the bytes use
    /// big-endian ordering.
    #[must_use]
    pub fn from_be_bytes(bytes: impl Into<[u8; mem::size_of::<Self>()]>) -> Self {
        // Here we have to convert the order through use of `from_be_bytes`
        let value = U256::from_be_bytes(bytes.into());
        Self { value }
    }

    /// Gets the value of the known word using little-endian byte ordering.
    #[must_use]
    pub fn value_le(&self) -> U256 {
        self.value
    }

    /// Gets the value of the known word using little-endian byte ordering and
    /// interpreting the bit pattern as a signed number.
    #[must_use]
    pub fn value_le_signed(&self) -> I256 {
        // Things are LE internally, so we just reinterpret
        I256::from_ne_bytes(self.value.to_ne_bytes())
    }

    /// Gets the value of the known word using network byte ordering.
    #[must_use]
    pub fn value_be(&self) -> U256 {
        // In this case we want to return the value with flipped endianness
        self.value.to_be()
    }

    /// Gets the value of the known word using network byte ordering and
    /// interpreting the bit pattern as a signed number.
    #[must_use]
    pub fn value_be_signed(&self) -> I256 {
        // We want to flip the endianness via `to_be_bytes`, but then we want to
        // interpret the bytes directly, hence `from_ne_bytes`
        I256::from_ne_bytes(self.value.to_be_bytes())
    }

    /// Gets the low-level bits of this known word in little endian ordering.
    #[must_use]
    pub fn bits_le(&self) -> BitVec {
        // A no-op, but this is correct
        let bytes_le = self.value.to_le_bytes();

        let mut bits = BitVec::new();
        for byte in bytes_le {
            bits.extend(byte.view_bits::<Lsb0>());
        }

        bits
    }

    /// Gets the low-level bits of this known word in big endian ordering.
    #[must_use]
    pub fn bits_be(&self) -> BitVec {
        // We have to swap the byte order here
        let bytes_le = self.value.to_be_bytes();

        let mut bits = BitVec::new();
        for byte in bytes_le {
            bits.extend(byte.view_bits::<Lsb0>());
        }

        bits
    }

    /// Gets the bytes of this word in little endian ordering.
    #[must_use]
    pub fn bytes_le(&self) -> [u8; mem::size_of::<Self>()] {
        self.value.to_le_bytes()
    }

    /// Gets the bytes of this word in big endian ordering.
    #[must_use]
    pub fn bytes_be(&self) -> [u8; mem::size_of::<Self>()] {
        self.value.to_be_bytes()
    }

    /// Performs signed division of two known words.
    #[must_use]
    pub fn signed_div(self, rhs: Self) -> Self {
        // In order to get signed behaviour we reinterpret the byte patterns into I256
        // before performing the operation using `{to,from}_ne_bytes`
        let left_signed = I256::from_ne_bytes(self.value.to_ne_bytes());
        let right_signed = I256::from_ne_bytes(rhs.value.to_ne_bytes());

        let zero = I256::new(0);
        let result = if right_signed == zero {
            zero
        } else {
            left_signed.wrapping_div(right_signed)
        };

        // To convert it back internally we need to perform direct conversion of the
        // byte pattern, using native endianness
        KnownWord::from_le(U256::from_ne_bytes(result.to_ne_bytes()))
    }

    /// Performs signed modulo of two known words.
    #[must_use]
    pub fn signed_rem(self, rhs: Self) -> Self {
        // In order to get signed behaviour we reinterpret the byte patterns into I256
        // before performing the operation using `{to,from}_ne_bytes`
        let left_signed = I256::from_ne_bytes(self.value.to_ne_bytes());
        let right_signed = I256::from_ne_bytes(rhs.value.to_ne_bytes());

        let zero = I256::new(0);
        let result = if right_signed == zero {
            zero
        } else {
            left_signed.wrapping_rem(right_signed)
        };

        // To convert it back internally we need to perform direct conversion of the
        // byte pattern, using native endianness
        KnownWord::from_le(U256::from_ne_bytes(result.to_ne_bytes()))
    }

    /// Performs exponentiation of two known words.
    #[must_use]
    pub fn exp(self, rhs: Self) -> Self {
        // The operation takes place in native endianness, which in our case is LE
        KnownWord::from_le(self.value.wrapping_pow(rhs.value.as_u32()))
    }

    /// Computes less-than of two known words.
    #[must_use]
    pub fn lt(self, rhs: Self) -> Self {
        // Bool to KnownWord is a fixed operation
        KnownWord::from(self.value < rhs.value)
    }

    /// Computes greater-than of two known words.
    #[must_use]
    pub fn gt(self, rhs: Self) -> Self {
        // Bool to KnownWord is a fixed operation
        KnownWord::from(self.value > rhs.value)
    }

    /// Computes signed less-than of two known words.
    #[must_use]
    pub fn signed_lt(self, rhs: Self) -> Self {
        // In order to get signed behaviour we reinterpret the byte patterns into I256
        // before performing the operation using `{to,from}_ne_bytes`
        let left_signed = I256::from_ne_bytes(self.value.to_ne_bytes());
        let right_signed = I256::from_ne_bytes(rhs.value.to_ne_bytes());
        let result = left_signed < right_signed;

        // Converting it back in this case is simple as
        KnownWord::from(result)
    }

    /// Computes signed less-than of two known words.
    #[must_use]
    pub fn signed_gt(self, rhs: Self) -> Self {
        // In order to get signed behaviour we reinterpret the byte patterns into I256
        // before performing the operation using `{to,from}_ne_bytes`
        let left_signed = I256::from_ne_bytes(self.value.to_ne_bytes());
        let right_signed = I256::from_ne_bytes(rhs.value.to_ne_bytes());
        let result = left_signed > right_signed;

        // Converting it back in this case is simple as
        KnownWord::from(result)
    }

    /// Computes equality of two known words.
    #[must_use]
    pub fn eq(self, rhs: Self) -> Self {
        // This does not care about endianness, as it just compares the bit pattern
        // directly
        KnownWord::from(self.value == rhs.value)
    }

    /// Checks if `self` is zero.
    #[must_use]
    pub fn is_zero(self) -> Self {
        // This does not care about endianness, as it just compares the bit pattern
        // directly
        KnownWord::from(self == Self::zero())
    }

    /// Computes the signed right shift of `self` by `rhs`.
    #[must_use]
    pub fn sar(self, rhs: Self) -> Self {
        // We need the value to be signed to make it an arithmetic shift
        let result = self.value_le_signed() >> rhs.value_le();

        // We are already LE, but need to turn it back into the unsigned internal rep
        KnownWord::from_le_signed(result)
    }
}

impl std::ops::Add<KnownWord> for KnownWord {
    type Output = KnownWord;

    /// Performs addition of two known words.
    fn add(self, rhs: KnownWord) -> Self::Output {
        // The operation takes place in native endianness, which in our case is LE
        KnownWord::from_le(self.value.wrapping_add(rhs.value))
    }
}

impl std::ops::Mul<KnownWord> for KnownWord {
    type Output = KnownWord;

    /// Performs multiplication of two known words.
    fn mul(self, rhs: KnownWord) -> Self::Output {
        // The operation takes place in native endianness, which in our case is LE
        KnownWord::from_le(self.value.wrapping_mul(rhs.value))
    }
}

impl std::ops::Sub<KnownWord> for KnownWord {
    type Output = KnownWord;

    /// Performs subtraction of two known words.
    fn sub(self, rhs: KnownWord) -> Self::Output {
        // The operation takes place in native endianness, which in our case is LE
        KnownWord::from_le(self.value.wrapping_sub(rhs.value))
    }
}

impl std::ops::Div<KnownWord> for KnownWord {
    type Output = KnownWord;

    /// Performs unsigned division of two known words.
    fn div(self, rhs: KnownWord) -> Self::Output {
        // The operation takes place in native endianness, which in our case is LE
        let zero = KnownWord::zero();
        if rhs == zero {
            zero
        } else {
            KnownWord::from_le(self.value.wrapping_div(rhs.value))
        }
    }
}

impl std::ops::Rem<KnownWord> for KnownWord {
    type Output = KnownWord;

    /// Performs unsigned modulo of two known words.
    fn rem(self, rhs: KnownWord) -> Self::Output {
        let zero = KnownWord::zero();
        if rhs == zero {
            zero
        } else {
            KnownWord::from_le(self.value.wrapping_rem(rhs.value))
        }
    }
}

impl std::ops::BitAnd<KnownWord> for KnownWord {
    type Output = KnownWord;

    /// Computes bitwise and of two known words.
    fn bitand(self, rhs: KnownWord) -> Self::Output {
        // While the operation is endianness-agnostic, the result is still little-endian
        // ordered
        KnownWord::from_le(self.value & rhs.value)
    }
}

impl std::ops::BitOr<KnownWord> for KnownWord {
    type Output = KnownWord;

    /// Computes bitwise or of two known words.
    fn bitor(self, rhs: KnownWord) -> Self::Output {
        // While the operation is endianness-agnostic, the result is still little-endian
        // ordered
        KnownWord::from_le(self.value | rhs.value)
    }
}

impl std::ops::BitXor<KnownWord> for KnownWord {
    type Output = KnownWord;

    /// Computes bitwise or of two known words.
    fn bitxor(self, rhs: KnownWord) -> Self::Output {
        // While the operation is endianness-agnostic, the result is still little-endian
        // ordered
        KnownWord::from_le(self.value ^ rhs.value)
    }
}

impl std::ops::Not for KnownWord {
    type Output = KnownWord;

    /// Computes the bitwise negation of `self`.
    fn not(self) -> Self::Output {
        // While the operation is endianness-agnostic, the result is still little-endian
        // ordered
        KnownWord::from_le(self.value.not())
    }
}

impl std::ops::Shl<KnownWord> for KnownWord {
    type Output = KnownWord;

    /// Computes the left shift of `self` by `rhs`.
    fn shl(self, rhs: KnownWord) -> Self::Output {
        KnownWord::from_le(self.value_le() << rhs.value_le())
    }
}

impl std::ops::Shr<KnownWord> for KnownWord {
    type Output = KnownWord;

    /// Computes the unsigned right shift of `self` by `rhs`.
    fn shr(self, rhs: KnownWord) -> Self::Output {
        KnownWord::from_le(self.value_le() >> rhs.value_le())
    }
}

impl From<usize> for KnownWord {
    /// Constructs a known word from a [`usize`], where the `value` uses the
    /// platform byte order.
    fn from(value: usize) -> Self {
        let value = U256::from(value.to_le() as u128);
        Self { value }
    }
}

impl From<KnownWord> for U256 {
    /// Obtains a [`U256`] from a known word.
    fn from(value: KnownWord) -> Self {
        value.value
    }
}

impl From<KnownWord> for u32 {
    /// Obtains a [`u32`] from a known word.
    fn from(value: KnownWord) -> Self {
        value.value.as_u32()
    }
}

impl From<&KnownWord> for u32 {
    /// Obtains a [`u32`] from a known word.
    fn from(value: &KnownWord) -> Self {
        value.value.as_u32()
    }
}

impl From<KnownWord> for usize {
    /// Obtains a [`usize`] from a known word.
    fn from(value: KnownWord) -> Self {
        value.value.as_usize()
    }
}

impl From<&KnownWord> for usize {
    /// Obtains a [`usize`] from a known word.
    fn from(value: &KnownWord) -> Self {
        value.value.as_usize()
    }
}

impl From<KnownWord> for bool {
    /// Obtains a [`bool`] from a known word.
    fn from(value: KnownWord) -> Self {
        value.value != U256::from(0u8)
    }
}

impl From<&KnownWord> for bool {
    /// Obtains a [`bool`] from a known word.
    fn from(value: &KnownWord) -> Self {
        value.value != U256::from(0u8)
    }
}

impl From<bool> for KnownWord {
    /// Obtains a known word from a [`bool`].
    fn from(value: bool) -> Self {
        if value {
            Self::from_le(1u8)
        } else {
            Self::from_le(0u8)
        }
    }
}

/// Pretty-prints the known word as a hexadecimal-encoded number using
/// big-endian byte ordering as it is easier for humans to work with.
impl Display for KnownWord {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let str = hex::encode(self.value.to_be_bytes());
        let str = str.trim_start_matches('0');
        let str = if str.is_empty() { "0" } else { str };
        write!(f, "0x{str}")
    }
}

#[cfg(test)]
mod test {
    use ethnum::{I256, U256};

    use crate::vm::value::known::KnownWord;

    #[test]
    #[allow(clippy::similar_names)] // They make sense here
    fn can_construct_from_unsigned_value() {
        let value_le = U256::from(0x1u32).to_le();
        let value_be = value_le.swap_bytes();

        let word_from_le = KnownWord::from_le(value_le);
        let word_from_be = KnownWord::from_be(value_be);

        assert_eq!(word_from_be, word_from_le);
        assert_eq!(word_from_le.value_le(), value_le);
        assert_eq!(word_from_le.value_be(), value_be);
    }

    #[test]
    #[allow(clippy::similar_names)] // They make sense here
    fn can_construct_from_signed_value() {
        let value_le = I256::from(0x1u32).to_le();
        let value_be = value_le.swap_bytes();

        let word_from_le = KnownWord::from_le_signed(value_le);
        let word_from_be = KnownWord::from_be_signed(value_be);

        assert_eq!(word_from_be, word_from_le);
        assert_eq!(word_from_le.value_le_signed(), value_le);
        assert_eq!(word_from_le.value_be_signed(), value_be);
    }

    #[test]
    #[allow(clippy::similar_names)] // They make sense here
    fn can_construct_from_bytes() {
        let value = U256::from(0x1u32);
        let value_le_bytes = value.to_le_bytes();
        let value_be_bytes = value.to_be_bytes();

        let word_from_le = KnownWord::from_le_bytes(value_le_bytes);
        let word_from_be = KnownWord::from_be_bytes(value_be_bytes);

        assert_eq!(word_from_be, word_from_le);
        assert_eq!(word_from_le.value_le().to_ne_bytes(), value_le_bytes);
        assert_eq!(word_from_le.value_be().to_ne_bytes(), value_be_bytes);
    }

    #[test]
    fn can_get_bits_le() {
        let word = KnownWord::from_le(0x1u32);
        let bits = word.bits_le();

        // It should be 256 bits long
        assert_eq!(bits.len(), 256);

        // Only the 1st bit should be 1 in little-endian
        for (ix, bit) in bits.iter().enumerate() {
            if ix == 0 {
                assert!(bit);
            } else {
                assert!(!bit);
            }
        }
    }

    #[test]
    fn can_get_bits_be() {
        let word = KnownWord::from_le(0x1u32);
        let bits = word.bits_be();

        // It should be 256 bits long
        assert_eq!(bits.len(), 256);

        // Only the 249th bit should be 1 in little-endian
        for (ix, bit) in bits.iter().enumerate() {
            if ix == 248 {
                assert!(bit);
            } else {
                assert!(!bit);
            }
        }
    }

    #[test]
    fn arithmetic_can_add_known_words() {
        let left = KnownWord::from_le(0x1u32);
        let right = KnownWord::from_le(0x7u32);

        assert_eq!(left + right, KnownWord::from_le(0x8u32));
    }

    #[test]
    fn arithmetic_can_multiply_known_words() {
        let left = KnownWord::from_le(0x1u32);
        let right = KnownWord::from_le(0x7u32);

        assert_eq!(left * right, KnownWord::from_le(0x7u32));
    }

    #[test]
    fn arithmetic_can_subtract_known_words() {
        let left = KnownWord::from_le(0x7u32);
        let right = KnownWord::from_le(0x1u32);

        assert_eq!(left - right, KnownWord::from_le(0x6u32));
    }

    #[test]
    fn arithmetic_can_divide_known_words() {
        let left = KnownWord::from_le(0x8u32);
        let right = KnownWord::from_le(0x2u32);

        assert_eq!(left / right, KnownWord::from_le(0x4u32));
    }

    #[test]
    fn arithmetic_can_signed_divide_known_words() {
        let left_int = I256::from(-8i16).to_le();
        let left = KnownWord::from_le_bytes(left_int.to_le_bytes());
        let right = KnownWord::from_le(0x2u32);
        let result_int = I256::from(-4i16).to_le();
        let result = KnownWord::from_le_bytes(result_int.to_le_bytes());

        assert_eq!(left.signed_div(right), result);
    }

    #[test]
    fn arithmetic_can_mod_known_words() {
        let left = KnownWord::from_le(0x7u32);
        let right = KnownWord::from_le(0x2u32);

        assert_eq!(left % right, KnownWord::from_le(0x1u32));
    }

    #[test]
    fn arithmetic_can_signed_mod_known_words() {
        let left_int = I256::from(-8i16).to_le();
        let left = KnownWord::from_le_bytes(left_int.to_le_bytes());
        let right = KnownWord::from_le(0x3u32);
        let result_int = I256::from(-2i16).to_le();
        let result = KnownWord::from_le_bytes(result_int.to_le_bytes());

        assert_eq!(left.signed_rem(right), result);
    }

    #[test]
    fn arithmetic_can_exp_known_words() {
        let left = KnownWord::from_le(0x7u32);
        let right = KnownWord::from_le(0x2u32);

        assert_eq!(left.exp(right), KnownWord::from_le(49u32));
    }

    #[test]
    fn arithmetic_can_lt_known_words() {
        let left = KnownWord::from_le(0x7u32);
        let right = KnownWord::from_le(0x2u32);

        assert_eq!(left.lt(right), KnownWord::from(false));
    }

    #[test]
    fn arithmetic_can_gt_known_words() {
        let left = KnownWord::from_le(0x7u32);
        let right = KnownWord::from_le(0x2u32);

        assert_eq!(left.gt(right), KnownWord::from(true));
    }

    #[test]
    fn arithmetic_can_signed_lt_known_words() {
        let left_int = I256::from(-8i16).to_le();
        let left = KnownWord::from_le_bytes(left_int.to_le_bytes());
        let right = KnownWord::from_le(0x3u32);

        assert_eq!(left.signed_lt(right), KnownWord::from(true));
    }

    #[test]
    fn arithmetic_can_signed_gt_known_words() {
        let left_int = I256::from(-8i16).to_le();
        let left = KnownWord::from_le_bytes(left_int.to_le_bytes());
        let right = KnownWord::from_le(0x3u32);

        assert_eq!(left.signed_gt(right), KnownWord::from(false));
    }

    #[test]
    fn arithmetic_can_eq_known_words() {
        let left = KnownWord::from_le(0x7u32);
        let right = KnownWord::from_le(0x2u32);

        assert_eq!(left.eq(right), KnownWord::from(false));
    }

    #[test]
    fn arithmetic_can_check_if_zero_for_known_word() {
        assert_eq!(KnownWord::from_le(0x7u32).is_zero(), KnownWord::from(false));
        assert_eq!(KnownWord::zero().is_zero(), KnownWord::from(true));
    }

    #[test]
    fn arithmetic_can_and_known_words() {
        let left = KnownWord::from_le(0x7u32);
        let right = KnownWord::from_le(0x2u32);

        assert_eq!(
            left & right,
            KnownWord::from_le(U256::from(0x7u32) & U256::from(0x2u32))
        );
    }

    #[test]
    fn arithmetic_can_or_known_words() {
        let left = KnownWord::from_le(0x7u32);
        let right = KnownWord::from_le(0x2u32);

        assert_eq!(
            left | right,
            KnownWord::from_le(U256::from(0x7u32) | U256::from(0x2u32))
        );
    }

    #[test]
    fn arithmetic_can_xor_known_words() {
        let left = KnownWord::from_le(0x7u32);
        let right = KnownWord::from_le(0x2u32);

        assert_eq!(
            left ^ right,
            KnownWord::from_le(U256::from(0x7u32) ^ U256::from(0x2u32))
        );
    }

    #[test]
    fn arithmetic_can_negate_known_word() {
        let word = KnownWord::from_le_bytes([
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff,
            0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ]);
        let negated = KnownWord::from_le_bytes([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00,
            0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff,
        ]);
        assert_eq!(!word, negated);
    }

    #[test]
    fn arithmetic_can_shift_left() {
        let shift = KnownWord::from_le(0x4u32);
        let value = KnownWord::from_le(0b1110u32);

        assert_eq!(value << shift, KnownWord::from_le_signed(0b1110_0000));
    }

    #[test]
    fn arithmetic_can_shift_right() {
        let shift = KnownWord::from_le(2u32);
        let value = KnownWord::from_le(0b10_1100u32);

        assert_eq!(value >> shift, KnownWord::from_le(0b1011u32));
    }

    #[test]
    fn arithmetic_can_shift_right_signed() {
        let shift = KnownWord::from_le(0x2u32);
        let value = KnownWord::from_le_signed(0b1101_0100i32);

        assert_eq!(value.sar(shift), KnownWord::from_le_signed(0b11_0101i32));
    }

    #[test]
    fn arithmetic_can_get_zero_when_dividing_by_zero() {
        let a = KnownWord::from_le(0x2u32);
        let zero = KnownWord::zero();

        assert_eq!(a / zero, zero);
    }

    #[test]
    fn arithmetic_can_get_zero_when_signed_dividing_by_zero() {
        let a = KnownWord::from_le(0x2u32);
        let zero = KnownWord::zero();

        assert_eq!(a.signed_div(zero), zero);
    }

    #[test]
    fn arithmetic_can_get_zero_when_mod_by_zero() {
        let a = KnownWord::from_le(0x2u32);
        let zero = KnownWord::zero();

        assert_eq!(a % zero, zero);
    }

    #[test]
    fn arithmetic_can_get_zero_when_signed_mod_by_zero() {
        let a = KnownWord::from_le(0x2u32);
        let zero = KnownWord::zero();

        assert_eq!(a.signed_rem(zero), zero);
    }
}
