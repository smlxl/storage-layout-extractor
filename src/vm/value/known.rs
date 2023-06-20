use std::fmt::{Display, Formatter};

use ethnum::U256;

/// The type of data whose value is concretely known during symbolic execution.
///
/// It is assumed that all byte sequences are encoded in little-endian ordering.
/// This is _not_ the EVM convention, as it uses network byte ordering, but
/// here there is no interaction with a real EVM.
///
/// For more information on the concrete definition of these data types, please
/// see [`crate::unifier::abi::AbiType`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct KnownWord {
    value: U256,
}

impl KnownWord {
    /// Creates a known value representing zero as a 256-bit wide unsigned
    /// integer.
    #[must_use]
    pub fn zero() -> Self {
        Self::from(vec![0])
    }

    /// Gets the value of the known word.
    #[must_use]
    pub fn value(&self) -> U256 {
        self.value
    }
}

/// Constructs a known word from an array of little-endian bytes.
impl From<Vec<u8>> for KnownWord {
    fn from(mut value: Vec<u8>) -> Self {
        value.resize(32, 0);
        let value: U256 = U256::from_le_bytes(value.as_slice().try_into().unwrap());
        Self { value }
    }
}

/// Constructs a known word from a [`usize`].
impl From<usize> for KnownWord {
    fn from(value: usize) -> Self {
        let value = U256::from(value as u128);
        Self { value }
    }
}

/// Constructs a known word from a [`U256`].
impl From<U256> for KnownWord {
    fn from(value: U256) -> Self {
        Self { value }
    }
}

/// Obtains a [`U256`] from a known word.
impl From<KnownWord> for U256 {
    fn from(value: KnownWord) -> Self {
        value.value
    }
}

/// Obtains a [`u32`] from a known word.
impl From<KnownWord> for u32 {
    fn from(value: KnownWord) -> Self {
        value.value.as_u32()
    }
}

/// Obtains a [`u32`] from a known word.
impl From<&KnownWord> for u32 {
    fn from(value: &KnownWord) -> Self {
        value.value.as_u32()
    }
}

/// Obtains a [`usize`] from a known word.
impl From<KnownWord> for usize {
    fn from(value: KnownWord) -> Self {
        value.value.as_usize()
    }
}

/// Obtains a [`usize`] from a known word.
impl From<&KnownWord> for usize {
    fn from(value: &KnownWord) -> Self {
        value.value.as_usize()
    }
}

/// Obtains a [`bool`] from a known word.
impl From<KnownWord> for bool {
    fn from(value: KnownWord) -> Self {
        value.value != U256::from(0u8)
    }
}

/// Obtains a [`bool`] from a known word.
impl From<&KnownWord> for bool {
    fn from(value: &KnownWord) -> Self {
        value.value != U256::from(0u8)
    }
}

/// Obtains a known word from a [`bool`].
impl From<bool> for KnownWord {
    fn from(value: bool) -> Self {
        if value { Self::from(1) } else { Self::from(0) }
    }
}

/// Pretty-prints the known word as a hexadecimal-encoded number.
impl Display for KnownWord {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let str = hex::encode(self.value.to_be_bytes());
        let str = str.trim_start_matches('0');
        let str = if str.is_empty() { "0" } else { str };
        write!(f, "0x{str}")
    }
}
