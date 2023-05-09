//! Opcodes that interact with the external environment on the EVM.

#![allow(dead_code)] // Temporary allow to suppress valid warnings for now.

use anyhow::anyhow;

use crate::{opcode::Opcode, vm::VM};

/// The `SHA3` opcode computes the keccak256 hash of the input.
///
/// The hash is computed on the data in memory at offset `o` over a size `s` in
/// bytes.
///
/// # Semantics
///
/// | Stack Index | Input | Output                  |
/// | :---------: | :---: | :---------------------: |
/// | 1           | o     | keccak256(mem\[o:o+s\]) |
/// | 2           | s     |                         |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Sha3;

impl Opcode for Sha3 {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        30
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "SHA3".into()
    }

    fn as_byte(&self) -> u8 {
        0x20
    }
}

/// The `ADDRESS` opcode gets the address of the currently executing account.
///
/// # Semantics
///
/// | Stack Index | Input | Output        |
/// | :---------: | :---: | :-----------: |
/// | 1           |       | address(this) |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Address;

impl Opcode for Address {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "ADDRESS".into()
    }

    fn as_byte(&self) -> u8 {
        0x30
    }
}

/// The `BALANCE` opcode gets the balance of the target account.
///
/// # Semantics
///
/// | Stack Index | Input | Output      |
/// | :---------: | :---: | :---------: |
/// | 1           | `a`   | `a.balance` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Balance;

impl Opcode for Balance {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        1
    }

    fn as_text_code(&self) -> String {
        "BALANCE".into()
    }

    fn as_byte(&self) -> u8 {
        0x31
    }
}

/// The `ORIGIN` opcode gets the address from which execution was started.
///
/// # Semantics
///
/// | Stack Index | Input | Output    |
/// | :---------: | :---: | :-------: |
/// | 1           |       | tx.origin |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Origin;

impl Opcode for Origin {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "ORIGIN".into()
    }

    fn as_byte(&self) -> u8 {
        0x32
    }
}

/// The `CALLER` opcode gets the calling address.
///
/// # Semantics
///
/// | Stack Index | Input | Output     |
/// | :---------: | :---: | :--------: |
/// | 1           |       | msg.sender |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Caller;

impl Opcode for Caller {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "CALLER".into()
    }

    fn as_byte(&self) -> u8 {
        0x33
    }
}

/// The `CALLVALUE` opcode gets the deposited value by the caller.
///
/// # Semantics
///
/// | Stack Index | Input | Output    |
/// | :---------: | :---: | :-------: |
/// | 1           |       | msg.value |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CallValue;

impl Opcode for CallValue {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "CALLVALUE".into()
    }

    fn as_byte(&self) -> u8 {
        0x34
    }
}

/// The `GASPRICE` opcode gets the current gas price from the environment.
///
/// # Semantics
///
/// | Stack Index | Input | Output      |
/// | :---------: | :---: | :---------: |
/// | 1           |       | tx.gasprice |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct GasPrice;

impl Opcode for GasPrice {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "GASPRICE".into()
    }

    fn as_byte(&self) -> u8 {
        0x3a
    }
}

/// The `EXTCODEHASH` computes the keccak256 hash of the code at the provided
/// address.
///
/// If there is no code at the specified address, this opcode returns the empty
/// hash. If the account does not exist or has been destroyed, returns 0.
///
/// # Semantics
///
/// | Stack Index | Input | Output            |
/// | :---------: | :---: | :---------------: |
/// | 1           | a     | keccak256(a.code) |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ExtCodeHash;

impl Opcode for ExtCodeHash {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        1
    }

    fn as_text_code(&self) -> String {
        "EXTCODEHASH".into()
    }

    fn as_byte(&self) -> u8 {
        0x3f
    }
}

/// The `BLOCKHASH` opcode gets the block hash of one of the 256 most recent
/// blocks.
///
/// # Semantics
///
/// | Stack Index | Input | Output       |
/// | :---------: | :---: | :----------: |
/// | 1           | n     | blockHash(n) |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct BlockHash;

impl Opcode for BlockHash {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        20
    }

    fn arg_count(&self) -> usize {
        1
    }

    fn as_text_code(&self) -> String {
        "BLOCKHASH".into()
    }

    fn as_byte(&self) -> u8 {
        0x40
    }
}

/// The `COINBASE` opcode gets the address of the block's beneficiary.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           | 0     | block.coinbase |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Coinbase;

impl Opcode for Coinbase {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "COINBASE".into()
    }

    fn as_byte(&self) -> u8 {
        0x41
    }
}

/// The `TIMESTAMP` opcode gets the timestamp of the current block.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | block.timestamp |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Timestamp;

impl Opcode for Timestamp {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "TIMESTAMP".into()
    }

    fn as_byte(&self) -> u8 {
        0x42
    }
}

/// The `NUMBER` opcode gets the number of the current block.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | block.number |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Number;

impl Opcode for Number {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "NUMBER".into()
    }

    fn as_byte(&self) -> u8 {
        0x43
    }
}

/// The `DIFFICULTY` opcode gets the difficulty of the current block.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | block.difficulty |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Difficulty;

impl Opcode for Difficulty {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "DIFFICULTY".into()
    }

    fn as_byte(&self) -> u8 {
        0x44
    }
}

/// The `GASLIMIT` opcode gets the gas limit for the current block.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | block.gaslimit |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct GasLimit;

impl Opcode for GasLimit {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "GASLIMIT".into()
    }

    fn as_byte(&self) -> u8 {
        0x45
    }
}

/// The `CHAINID` opcode gets the identifier of the chain the block is executing
/// on.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | block.chain_id |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ChainId;

impl Opcode for ChainId {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "CHAINID".into()
    }

    fn as_byte(&self) -> u8 {
        0x46
    }
}

/// The `SELFBALANCE` opcode gets the balance of the currently executing
/// account.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | address(this).balance |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SelfBalance;

impl Opcode for SelfBalance {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        5
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "SELFBALANCE".into()
    }

    fn as_byte(&self) -> u8 {
        0x47
    }
}

/// The `BASEFEE` opcode gets the base block fee in WEI.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | block.basefee |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct BaseFee;

impl Opcode for BaseFee {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "BASEFEE".into()
    }

    fn as_byte(&self) -> u8 {
        0x48
    }
}

/// The `GAS` opcode gets the amount of gas currently available.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | gasRemaining |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Gas;

impl Opcode for Gas {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "GAS".into()
    }

    fn as_byte(&self) -> u8 {
        0x5a
    }
}

/// The `LOGN` opcode logs `N` items, where `0 <= N <= 4`.
///
/// The items used as arguments _are not_ popped off the stack.
///
/// # Semantics
///
/// | Stack Index  | Input | Output |
/// | :----------: | :---: | :----: |
/// | 1            | o     | o      |
/// | 2            | s     | s      |
/// | i in 3..=3+N | t(i)  | t(i)   |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct LogN {
    topic_count: u8,
}

impl LogN {
    /// Constructs a new instance of the `LOGN` opcode.
    ///
    /// # Errors
    ///
    /// If the provided `n` is not in the specified range.
    pub fn new(n: u8) -> anyhow::Result<Self> {
        if n <= 4 {
            Ok(Self { topic_count: n })
        } else {
            Err(anyhow!(
                "Invalid number of topics provided to the LOG opcode: {n}"
            ))
        }
    }

    /// Gets the number of topics passed to this log call.
    pub fn n(&self) -> u8 {
        self.topic_count
    }
}

impl Opcode for LogN {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        match self.topic_count {
            0 => 375,
            1 => 750,
            2 => 1125,
            3 => 1500,
            4 => 1875,
            _ => unreachable!("Invalid number of log topics: {}", self.topic_count),
        }
    }

    fn arg_count(&self) -> usize {
        2 + self.topic_count as usize
    }

    fn as_text_code(&self) -> String {
        format!("LOG{}", self.topic_count)
    }

    fn as_byte(&self) -> u8 {
        const BASE_VALUE: u8 = 0xa0;
        BASE_VALUE + self.topic_count
    }
}

/// The `CREATE` opcode creates a contract and returns the address of the
/// created contract.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           | val   | keccak256(rlp_enc(\[address(this), this.nonce\])) |
/// | 2           | ofs   |        |
/// | 2           | sz    |        |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Create;

impl Opcode for Create {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        32000
    }

    fn arg_count(&self) -> usize {
        3
    }

    fn as_text_code(&self) -> String {
        "CREATE".into()
    }

    fn as_byte(&self) -> u8 {
        0xf0
    }
}

/// The `CREATE2` opcode creates a contract at a predictable address and returns
/// the address of the created contract.
///
/// ```text
/// keccak256(0xff ++ address(this) ++ salt ++ keccak256(mem[ost:ost+len]))[12:]
/// ```
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           | val   | address |
/// | 2           | ofs   |        |
/// | 3           | sz    |        |
/// | 4           | salt    |        |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Create2;

impl Opcode for Create2 {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        32000
    }

    fn arg_count(&self) -> usize {
        4
    }

    fn as_text_code(&self) -> String {
        "CREATE2".into()
    }

    fn as_byte(&self) -> u8 {
        0xf5
    }
}

/// The `SELFDESTRUCT` opcode halts execution and registers the account for
/// later deletion, sending all remaining balance to `addr`.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           | addr     |  |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SelfDestruct;

impl Opcode for SelfDestruct {
    fn execute(&self, _vm: &mut VM) -> anyhow::Result<()> {
        unimplemented!()
    }

    fn min_gas_cost(&self) -> usize {
        5000
    }

    fn arg_count(&self) -> usize {
        1
    }

    fn as_text_code(&self) -> String {
        "SELFDESTRUCT".into()
    }

    fn as_byte(&self) -> u8 {
        0xff
    }
}
