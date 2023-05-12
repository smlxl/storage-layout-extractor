//! This module contains the definition of the [`SymbolicValue`] and its
//! supporting types.

// TODO [Ara] Metavariable storage. Needs operations to mutate metavars and add
//   new ones, as well as consume the entire thing at the end (unifier).

// TODO [Ara] Metavariable representation.
// TODO [Ara] Metavariables held at top level in the VM, taken and then returned
//   with each split in execution (VMState holds references, perhaps)

// TODO [Ara] MetavariableHandle type, that makes it easy to reference things by
//   index, perhaps?

// TODO [Ara] The stored implication sets need to know some idea of where they
//   came from. (e.g. M3 resulted from the sum of M1 and M2). Metavar trees in a
//   vector for each metavar containing the ones that "contribute", by or index
//   (handle).

// TODO [Ara] When a symbolic value is going to disappear it should be added to
//   the `VM`s buffer of them.

// TODO [Ara] Have to deal with indexing into storage and memory based on
//   symbolic values. Symbolic equality is sufficient for now. Probably.

pub mod known_data;

use uuid::Uuid;

use crate::vm::symbolic_value::known_data::KnownData;

/// A symbolic value is an "execution tree" that records the informative
/// operations that are made to a piece of data.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicValue {
    /// The instruction pointer's value at the location where this part of the
    /// symbolic execution tree was recorded.
    instruction_pointer: u32,

    /// The actual execution tree that forms this value.
    data: SymbolicValueData,
}

impl SymbolicValue {
    /// Constructs a new `SymbolicValue` representing the operation performed at
    /// `instruction_pointer` on the symbolic `data`.
    ///
    /// It returns [`Box<Self>`] as in the vast majority of cases this type is
    /// used in a recursive data type and hence indirection is needed.
    pub fn new(instruction_pointer: u32, data: SymbolicValueData) -> Box<Self> {
        Box::new(Self {
            instruction_pointer,
            data,
        })
    }
}

/// The type of a boxed symbolic value.
pub type BoxedVal = Box<SymbolicValue>;

/// The execution tree structures that allow the executor to build traces of the
/// execution pertaining to certain symbolic values.
///
/// Note that these do not duplicate the opcodes 1:1, instead representing the
/// opcode operations that _provide information about the type of a value_ as an
/// execution tree. Notable (and intentional) omissions here are the opcodes
/// that deal with memory, storage, and the stack.
///
/// # Semantics
///
/// For the semantics of these operations at runtime, please see the
/// corresponding documentation comments in the [`crate::opcode`] subtree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SymbolicValueData {
    /// A value with identity, but about which nothing else is known.
    Value { id: Uuid },

    /// A value that has is made up of a known sequence of bytes.
    ///
    /// It has an `id` in order to allow the program to distinguish the same
    /// value created in different places.
    KnownData { id: Uuid, value: KnownData },

    /// Addition of symbolic values.
    Add { left: BoxedVal, right: BoxedVal },

    /// Multiplication of symbolic values.
    Mul { left: BoxedVal, right: BoxedVal },

    /// Subtraction of symbolic values.
    Sub { left: BoxedVal, right: BoxedVal },

    /// Division of symbolic values.
    Div { dividend: BoxedVal, divisor: BoxedVal },

    /// Signed division of symbolic values.
    SDiv { dividend: BoxedVal, divisor: BoxedVal },

    /// Modulo of symbolic values.
    Mod { dividend: BoxedVal, divisor: BoxedVal },

    /// Signed modulo of symbolic values.
    SMod { dividend: BoxedVal, divisor: BoxedVal },

    /// Addition followed by modulo.
    AddMod { left: BoxedVal, right: BoxedVal, exponent: BoxedVal },

    /// Multiplication followed by modulo.
    MulMod { left: BoxedVal, right: BoxedVal, exponent: BoxedVal },

    /// Exponentiation of symbolic values.
    Exp { value: BoxedVal, exponent: BoxedVal },

    /// Sign extension of a symbolic value to a symbolic length.
    SignExtend { size: BoxedVal, value: BoxedVal },

    /// Program counter.
    ProgramCounter,

    /// A standard message call.
    Call {
        gas:        BoxedVal,
        address:    BoxedVal,
        value:      BoxedVal,
        arg_offset: BoxedVal,
        arg_size:   BoxedVal,
        ret_offset: BoxedVal,
        ret_size:   BoxedVal,
    },

    /// A `CALLCODE` message call.
    CallCode {
        gas:        BoxedVal,
        address:    BoxedVal,
        value:      BoxedVal,
        arg_offset: BoxedVal,
        arg_size:   BoxedVal,
        ret_offset: BoxedVal,
        ret_size:   BoxedVal,
    },

    /// A `DELEGATECALL` message call.
    DelegateCall {
        gas:        BoxedVal,
        address:    BoxedVal,
        value:      BoxedVal,
        arg_offset: BoxedVal,
        arg_size:   BoxedVal,
        ret_offset: BoxedVal,
        ret_size:   BoxedVal,
    },

    /// A `STATICCALL` message call.
    StaticCall {
        gas:        BoxedVal,
        address:    BoxedVal,
        value:      BoxedVal,
        arg_offset: BoxedVal,
        arg_size:   BoxedVal,
        ret_offset: BoxedVal,
        ret_size:   BoxedVal,
    },

    /// A keccak256 hash on symbolic values.
    Sha3 { offset: BoxedVal, size: BoxedVal },

    /// The address of the currently-executing contract.
    Address,

    /// The balance of the target account.
    Balance { address: BoxedVal },

    /// The address of the transaction's origin.
    Origin,

    /// The caller of the transaction.
    Caller,

    /// The value deposited by the caller.
    CallValue,

    /// The current gas price.
    GasPrice,

    /// Compute the external code hash of a symbolic value.
    ExtCodeHash { address: BoxedVal },

    /// Gets the block hash from one of the
    BlockHash { block_number: u8 },

    /// Gets the block's beneficiary address.
    CoinBase,

    /// Gets the timestamp of the current block.
    Timestamp,

    /// Gets the number of the current block.
    Number,

    /// Gets the difficulty of the current block.
    Difficulty,

    /// Gets the gas limit of  the current block.
    GasLimit,

    /// Gets the identifier for the chain on which the current block is
    /// executing.
    ChainId,

    /// Gets the balance of the currently executing account.
    SelfBalance,

    /// Gets the block base fee.
    BaseFee,

    /// Gets the currently available gas.
    Gas,

    /// Creates a new contract.
    Create { value: BoxedVal, offset: BoxedVal, size: BoxedVal },

    /// Creates a new contract at a predictable address.
    Create2 {
        value:  BoxedVal,
        offset: BoxedVal,
        size:   BoxedVal,
        salt:   BoxedVal,
    },

    /// Registers the account for deletion.
    SelfDestruct { target: BoxedVal },

    /// Less than for symbolic values.
    Lt { left: BoxedVal, right: BoxedVal },

    /// Greater than for symbolic values.
    Gt { left: BoxedVal, right: BoxedVal },

    /// Less than for symbolic values where the values are signed.
    SLt { left: BoxedVal, right: BoxedVal },

    /// Greater than for symbolic values where the values are signed.
    SGt { left: BoxedVal, right: BoxedVal },

    /// Equality for symbolic values.
    Eq { left: BoxedVal, right: BoxedVal },

    /// Checking if a symbolic value is zero.
    IsZero { number: BoxedVal },

    /// Logical conjunction for symbolic values.
    And { left: BoxedVal, right: BoxedVal },

    /// Logical disjunction for symbolic values.
    Or { left: BoxedVal, right: BoxedVal },

    /// XOR for symbolic values.
    Xor { left: BoxedVal, right: BoxedVal },

    /// Negation of a symbolic value.
    Not { bool: BoxedVal },

    /// Gets a byte from a word.
    Byte { offset: BoxedVal, value: BoxedVal },

    /// Left shift with symbolic values.
    Shl { shift: BoxedVal, value: BoxedVal },

    /// Right shift with symbolic values.
    Shr { shift: BoxedVal, value: BoxedVal },

    /// Signed right shift with symbolic values.
    Sar { shift: BoxedVal, value: BoxedVal },
}

/// The default value for a symbolic value's data is a [`SymbolicValue::Value`]
/// about which nothing else is known.
impl Default for SymbolicValueData {
    fn default() -> Self {
        SymbolicValueData::Value { id: Uuid::new_v4() }
    }
}
