use std::fmt::{Display, Formatter};

use ethnum::U256;

/// The type of data whose value is concretely known during symbolic execution.
///
/// It is assumed that all byte sequences are encoded in little-endian ordering.
/// This is _not_ the EVM convention, as it uses network byte ordering, but
/// here there is no interaction with a real EVM.
///
/// For more information on the concrete definition of these data types, please
/// see [`crate::unifier::types::AbiType`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum KnownData {
    Bytes { value: Vec<u8> },
    Address { value: [u8; 20] },
    UInt { value: Vec<u8> },
    Int { value: Vec<u8> },
    Bool { value: bool },
    Selector { value: [u8; 4] },
    Function { value: [u8; 24] },
}

impl KnownData {
    /// Creates a known value representing zero as a 256-bit wide unsigned
    /// integer.
    pub fn zero() -> Self {
        KnownData::UInt { value: vec![0; 32] }
    }
}

impl Display for KnownData {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bytes { value } => write!(f, "bytes({value:?})"),
            Self::UInt { value } => {
                let mut bytes = value.clone();
                bytes.resize(32, 0);
                write!(
                    f,
                    "uint({})",
                    U256::from_le_bytes(bytes.as_slice().try_into().unwrap())
                )
            }
            // TODO [Ara] This will change soon as `KnownData` is going to change.
            _ => write!(f, "{:?}", self),
        }
    }
}
