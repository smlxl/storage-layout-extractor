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
    UInt { size: u8, value: Vec<u8> },
    Int { size: u8, value: Vec<u8> },
    Bool { value: bool },
    Selector { value: [u8; 4] },
    Function { value: [u8; 24] },
}
