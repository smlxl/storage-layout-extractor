//! Opcodes that interact with the external environment on the EVM.

use crate::{
    constant::LOG_OPCODE_BASE_VALUE,
    error::disassembly,
    opcode::{ExecuteResult, Opcode},
    vm::{
        value::{RuntimeBoxedVal, RSVD},
        VM,
    },
};

/// The `SHA3` opcode computes the keccak256 hash of the input.
///
/// The hash is computed on the data in memory at `offset` over a `size` in
/// bytes.
///
/// # Semantics
///
/// | Stack Index | Input    | Output                                 |
/// | :---------: | :------: | :------------------------------------: |
/// | 1           | `offset` | `keccak256(mem\[offset:offset+size\])` |
/// | 2           | `size`   |                                        |
///
/// where:
///
/// - `offset` is the byte offset in memory where the data to be hashed starts
/// - `size` is the number of bytes in the data to be hashed
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Sha3;

impl Opcode for Sha3 {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let offset = stack.pop()?;
        let size = stack.pop()?;

        // Get the value at `offset` out of memory
        let memory = vm.state()?.memory_mut();
        let data = memory.load_slice(&offset, &size, instruction_pointer);

        // Build the result and push it onto the stack
        let result = vm.build().symbolic_exec(instruction_pointer, RSVD::Sha3 { data });
        vm.stack_handle()?.push(result)?;

        // Done, so return ok
        Ok(())
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
/// | Stack Index | Input | Output          |
/// | :---------: | :---: | :-------------: |
/// | 1           |       | `address(this)` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Address;

impl Opcode for Address {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;

        // Create and push the value onto the stack
        let value = vm.build().symbolic_exec(instruction_pointer, RSVD::Address);
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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
/// | Stack Index | Input     | Output                       |
/// | :---------: | :-------: | :--------------------------: |
/// | 1           | `address` | `balance := address.balance` |
///
/// where:
///
/// - `address` is the address of the account to check the balance for
/// - `balance` is the balance in WEI
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Balance;

impl Opcode for Balance {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the argument from the stack
        let address = stack.pop()?;

        // Create and push the value onto the stack
        let value = vm
            .build()
            .symbolic_exec(instruction_pointer, RSVD::Balance { address });
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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
/// | Stack Index | Input | Output                |
/// | :---------: | :---: | :-------------------: |
/// | 1           |       | `origin := tx.origin` |
///
/// where:
///
/// - `origin` is the address that was the sender of the transaction
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Origin;

impl Opcode for Origin {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;

        // Create and push the value onto the stack
        let value = vm.build().symbolic_exec(instruction_pointer, RSVD::Origin);
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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
/// | Stack Index | Input | Output                 |
/// | :---------: | :---: | :--------------------: |
/// | 1           |       | `caller := msg.sender` |
///
/// where:
///
/// - `caller` is the address of the message's sender
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Caller;

impl Opcode for Caller {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;

        // Create and push the value onto the stack
        let value = vm.build().symbolic_exec(instruction_pointer, RSVD::Caller);
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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
/// | Stack Index | Input | Output               |
/// | :---------: | :---: | :------------------: |
/// | 1           |       | `value := msg.value` |
///
/// where:
///
/// - `value` is the value of the current call in WEI
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CallValue;

impl Opcode for CallValue {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;

        // Create and push the value onto the stack
        let value = vm.build().symbolic_exec(instruction_pointer, RSVD::CallValue);
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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
/// | Stack Index | Input | Output                 |
/// | :---------: | :---: | :--------------------: |
/// | 1           |       | `price := tx.gasprice` |
///
/// where:
///
/// - `price` is the current gas price in WEI
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct GasPrice;

impl Opcode for GasPrice {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;

        // Create and push the value onto the stack
        let value = vm.build().symbolic_exec(instruction_pointer, RSVD::GasPrice);
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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
/// | Stack Index | Input     | Output                    |
/// | :---------: | :-------: | :-----------------------: |
/// | 1           | `address` | `keccak256(address.code)` |
///
/// where:
///
/// - `address` is the address of the contract to get the code hash of
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ExtCodeHash;

impl Opcode for ExtCodeHash {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the argument from the stack
        let address = stack.pop()?;

        // Create and push the value onto the stack
        let value = vm
            .build()
            .symbolic_exec(instruction_pointer, RSVD::ExtCodeHash { address });
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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
/// | Stack Index | Input | Output                 |
/// | :---------: | :---: | :--------------------: |
/// | 1           | `n`   | `hash := blockHash(n)` |
///
/// where:
///
/// - `n` is the number of the block, one of the last 256 blocks not including
///   the current one
/// - `hash` is the keccak256 hash of the chosen block, or 0 if `n` is not in
///   the valid range
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct BlockHash;

impl Opcode for BlockHash {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the argument from the stack
        let block_number = stack.pop()?;

        // Create and push the value onto the stack
        let value = vm
            .build()
            .symbolic_exec(instruction_pointer, RSVD::BlockHash { block_number });
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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
/// | Stack Index | Input | Output                   |
/// | :---------: | :---: | :----------------------: |
/// | 1           |       | `base := block.coinbase` |
///
/// where:
///
/// - `base` is the address of the miner
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CoinBase;

impl Opcode for CoinBase {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;

        // Create and push the value onto the stack
        let value = vm.build().symbolic_exec(instruction_pointer, RSVD::CoinBase);
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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
/// | Stack Index | Input | Output                  |
/// | :---------: | :---: | :---------------------: |
/// | 1           |       | `ts := block.timestamp` |
///
/// where:
///
/// - `ts` is the unix timestamp of the current block
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Timestamp;

impl Opcode for Timestamp {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;

        // Create and push the value onto the stack
        let value = vm.build().symbolic_exec(instruction_pointer, RSVD::BlockTimestamp);
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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
/// | Stack Index | Input | Output         |
/// | :---------: | :---: | :------------: |
/// | 1           |       | `block.number` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Number;

impl Opcode for Number {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;

        // Create and push the value onto the stack
        let value = vm.build().symbolic_exec(instruction_pointer, RSVD::BlockNumber);
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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

/// The `PREVRANDAO` opcode gets the difficulty of the current block.
///
/// # Semantics
///
/// | Stack Index | Input | Output             |
/// | :---------: | :---: | :----------------: |
/// | 1           |       | `block.difficulty` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Prevrandao;

impl Opcode for Prevrandao {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;

        // Create and push the value onto the stack
        let value = vm.build().symbolic_exec(instruction_pointer, RSVD::Prevrandao);
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "PREVRANDAO".into()
    }

    fn as_byte(&self) -> u8 {
        0x44
    }
}

/// The `GASLIMIT` opcode gets the gas limit for the current block.
///
/// # Semantics
///
/// | Stack Index | Input | Output           |
/// | :---------: | :---: | :--------------: |
/// | 1           |       | `block.gaslimit` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct GasLimit;

impl Opcode for GasLimit {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;

        // Create and push the value onto the stack
        let value = vm.build().symbolic_exec(instruction_pointer, RSVD::GasLimit);
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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
/// | Stack Index | Input | Output           |
/// | :---------: | :---: | :--------------: |
/// | 1           |       | `block.chain_id` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ChainId;

impl Opcode for ChainId {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;

        // Create and push the value onto the stack
        let value = vm.build().symbolic_exec(instruction_pointer, RSVD::ChainId);
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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
/// | Stack Index | Input | Output                         |
/// | :---------: | :---: | :----------------------------: |
/// | 1           |       | `bal := address(this).balance` |
///
/// where:
///
/// - `bal` is the balance of the current account in WEI
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SelfBalance;

impl Opcode for SelfBalance {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;

        // Create and push the value onto the stack
        let value = vm.build().symbolic_exec(instruction_pointer, RSVD::SelfBalance);
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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
/// | Stack Index | Input | Output                 |
/// | :---------: | :---: | :--------------------: |
/// | 1           |       | `fee := block.basefee` |
///
/// where:
///
/// - `fee` is the block's base fee in WEI
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct BaseFee;

impl Opcode for BaseFee {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;

        // Create and push the value onto the stack
        let value = vm.build().symbolic_exec(instruction_pointer, RSVD::BaseFee);
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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
/// | Stack Index | Input | Output                |
/// | :---------: | :---: | :-------------------: |
/// | 1           |       | `gas := gasRemaining` |
///
/// where:
///
/// - `gas` is the amount of gas remaining _after_ executing the `GAS`
///   instruction
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Gas;

impl Opcode for Gas {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment data
        let instruction_pointer = vm.instruction_pointer()?;

        // Create and push the value onto the stack
        let value = vm.build().symbolic_exec(instruction_pointer, RSVD::Gas);
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
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
/// # Note
///
/// The items used as arguments _are not_ popped off the stack. That means that
/// executing this instruction has no effect on the EVM's state.
///
/// # Semantics
///
/// | Stack Index      | Input    | Output   |
/// | :--------------: | :------: | :------: |
/// | 1                | `offset` | `offset` |
/// | 2                | `size`   | `size`   |
/// | `i` in `3..=3+N` | `t(i)`   | `t(i)`   |
///
/// where:
///
/// - `offset` is the byte offset in memory where the log data begins
/// - `size` is the size of the log data in bytes
/// - `t(i)` is the `i`th topic for the log message
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
    pub fn new(n: u8) -> Result<Self, disassembly::Error> {
        if n <= 4 {
            Ok(Self { topic_count: n })
        } else {
            Err(disassembly::Error::InvalidTopicCount(n))
        }
    }

    /// Gets the number of topics passed to this log call.
    #[must_use]
    pub fn n(&self) -> u8 {
        self.topic_count
    }
}

impl Opcode for LogN {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and instruction pointer
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the arguments
        let offset = stack.pop()?;
        let size = stack.pop()?;
        let mut topics: Vec<RuntimeBoxedVal> = Vec::new();

        // Safely bounded during disassembly
        let upper_bound = u32::from(self.n()) + 2;
        for _ in 2..upper_bound {
            topics.push(stack.pop()?);
        }

        // Read the log value from memory
        let data = vm
            .state()?
            .memory_mut()
            .load_slice(&offset, &size, instruction_pointer);

        // Build the log call
        let log = vm
            .build()
            .symbolic_exec(instruction_pointer, RSVD::Log { data, topics });

        // Write it to the log buffer
        vm.state()?.log_value(log);

        // Done, so return ok
        Ok(())
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
        LOG_OPCODE_BASE_VALUE + self.topic_count
    }
}

/// The `CREATE` opcode creates a contract and returns the address of the
/// created contract.
///
/// The creation process enters a new sub-context of the calculated destination
/// address and executes the provided initialisation code before resuming the
/// current context
///
/// # Semantics
///
/// | Stack Index | Input    | Output    |
/// | :---------: | :------: | :-------: |
/// | 1           | `value`  | `address` |
/// | 2           | `offset` |           |
/// | 3           | `size`   |           |
///
/// where:
///
/// - `value` is the amount of WEI to send to the new contract
/// - `offset` is the byte offset in memory where the initialisation code for
///   the new contract begins
/// - `size` is the length in bytes of the initialisation code
/// - `address` is the address of the new contract, calculated as `address :=
///   keccak256(rlp\[sender_address, sender_nonce\]))\[12:\]`
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Create;

impl Opcode for Create {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let value = stack.pop()?;
        let offset = stack.pop()?;
        let size = stack.pop()?;

        // Read the create payload from memory
        let data = vm
            .state()?
            .memory_mut()
            .load_slice(&offset, &size, instruction_pointer);

        // Construct the intermediate and push it onto the stack
        let address = vm
            .build()
            .symbolic_exec(instruction_pointer, RSVD::Create { value, data });
        vm.stack_handle()?.push(address)?;

        // Done, so return ok
        Ok(())
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
///
/// The creation process enters a new sub-context of the calculated destination
/// address and executes the provided initialisation code before resuming the
/// current context
///
/// # Semantics
///
/// | Stack Index | Input    | Output    |
/// | :---------: | :------: | :-------: |
/// | 1           | `value`  | `address` |
/// | 2           | `offset` |           |
/// | 3           | `size`   |           |
/// | 3           | `salt`   |           |
///
/// where:
///
/// - `value` is the amount of WEI to send to the new contract
/// - `offset` is the byte offset in memory where the initialisation code for
///   the new contract begins
/// - `size` is the length in bytes of the initialisation code
/// - `salt` is a 32-byte value used to create the new account at a
///   deterministic address
/// - `address` is the address of the new contract, calculated as `address :=
///   keccak256(0xff ++ address(this) ++ salt ++
///   keccak256(mem\[offset:offset+size\]))\[12:\]`
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Create2;

impl Opcode for Create2 {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let value = stack.pop()?;
        let offset = stack.pop()?;
        let size = stack.pop()?;
        let salt = stack.pop()?;

        // Read the create payload from memory
        let data = vm
            .state()?
            .memory_mut()
            .load_slice(&offset, &size, instruction_pointer);

        // Construct the intermediate and push it onto the stack
        let address = vm
            .build()
            .symbolic_exec(instruction_pointer, RSVD::Create2 { value, salt, data });
        vm.stack_handle()?.push(address)?;

        // Done, so return ok
        Ok(())
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
/// later deletion.
///
/// # Semantics
///
/// | Stack Index | Input     | Output |
/// | :---------: | :-------: | :----: |
/// | 1           | `address` |        |
///
/// where:
///
/// - `address` is the value to which all of the remaining [`SelfBalance`] is
///   sent upon account deletion
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SelfDestruct;

impl Opcode for SelfDestruct {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the argument from the stack
        let target = stack.pop()?;

        // Construct the result
        let destroy = vm
            .build()
            .symbolic_exec(instruction_pointer, RSVD::SelfDestruct { target });

        // Store it in the recorded values store, as otherwise it would be dropped and
        // we would lose info
        vm.state()?.record_value(destroy);

        // Done, so return ok
        Ok(())
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

#[cfg(test)]
mod test {
    use crate::{
        opcode::{environment, test_util as util, Opcode},
        vm::value::{Provenance, RuntimeBoxedVal, RSV, RSVD},
    };

    #[test]
    fn sha_3_modifies_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_offset = RSV::new_synthetic(0, RSVD::new_value());
        let stored_value = RSV::new_synthetic(1, RSVD::new_value());
        let input_size = RSV::new_synthetic(0, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![input_size, input_offset.clone()])?;
        vm.state()?.memory_mut().store(input_offset, stored_value.clone());

        // Prepare and run the opcode
        let opcode = environment::Sha3;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        match result.data() {
            RSVD::Sha3 { data } => {
                assert_eq!(data, &stored_value);
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }

    #[test]
    fn address_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = environment::Address;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        assert_eq!(result.data(), &RSVD::Address);

        Ok(())
    }

    #[test]
    fn balance_modifies_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_address = RSV::new_synthetic(0, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![input_address.clone()])?;

        // Prepare and run the opcode
        let opcode = environment::Balance;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        match result.data() {
            RSVD::Balance { address } => {
                assert_eq!(address, &input_address);
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }

    #[test]
    fn origin_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = environment::Origin;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        assert_eq!(result.data(), &RSVD::Origin);

        Ok(())
    }

    #[test]
    fn caller_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = environment::Caller;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        assert_eq!(result.data(), &RSVD::Caller);

        Ok(())
    }

    #[test]
    fn call_value_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = environment::CallValue;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        assert_eq!(result.data(), &RSVD::CallValue);

        Ok(())
    }

    #[test]
    fn gas_price_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = environment::GasPrice;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        assert_eq!(result.data(), &RSVD::GasPrice);

        Ok(())
    }

    #[test]
    fn ext_code_hash_modifies_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_address = RSV::new_synthetic(0, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![input_address.clone()])?;

        // Prepare and run the opcode
        let opcode = environment::ExtCodeHash;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        match result.data() {
            RSVD::ExtCodeHash { address } => {
                assert_eq!(address, &input_address);
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }

    #[test]
    fn block_hash_modifies_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_block_number = RSV::new_synthetic(0, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![input_block_number.clone()])?;

        // Prepare and run the opcode
        let opcode = environment::BlockHash;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        match result.data() {
            RSVD::BlockHash { block_number } => {
                assert_eq!(block_number, &input_block_number);
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }

    #[test]
    fn coin_base_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = environment::CoinBase;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        assert_eq!(result.data(), &RSVD::CoinBase);

        Ok(())
    }

    #[test]
    fn timestamp_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = environment::Timestamp;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        assert_eq!(result.data(), &RSVD::BlockTimestamp);

        Ok(())
    }

    #[test]
    fn number_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = environment::Number;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        assert_eq!(result.data(), &RSVD::BlockNumber);

        Ok(())
    }

    #[test]
    fn difficulty_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = environment::Prevrandao;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        assert_eq!(result.data(), &RSVD::Prevrandao);

        Ok(())
    }

    #[test]
    fn gas_limit_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = environment::GasLimit;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        assert_eq!(result.data(), &RSVD::GasLimit);

        Ok(())
    }

    #[test]
    fn chain_id_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = environment::ChainId;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        assert_eq!(result.data(), &RSVD::ChainId);

        Ok(())
    }

    #[test]
    fn self_balance_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = environment::SelfBalance;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        assert_eq!(result.data(), &RSVD::SelfBalance);

        Ok(())
    }

    #[test]
    fn base_fee_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = environment::BaseFee;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        assert_eq!(result.data(), &RSVD::BaseFee);

        Ok(())
    }

    #[test]
    fn gas_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = environment::Gas;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance(), Provenance::Execution);
        assert_eq!(result.data(), &RSVD::Gas);

        Ok(())
    }

    #[test]
    fn log_leaves_stack_unchanged() -> anyhow::Result<()> {
        // We want to test all sizes of log
        for topic_count in 0..=4 {
            // Construct the stack
            let mut topics: Vec<RuntimeBoxedVal> = vec![];
            let input_offset = RSV::new_synthetic(0, RSVD::new_value());
            let input_size = RSV::new_synthetic(1, RSVD::new_value());
            let stored_data = RSV::new_synthetic(2, RSVD::new_value());

            for i in 0..u32::from(topic_count) {
                let value = RSV::new_synthetic(3 + i, RSVD::new_value());
                topics.push(value);
            }

            let mut input_stack = topics.clone();
            input_stack.push(input_size.clone());
            input_stack.push(input_offset.clone());

            // Prepare the vm
            let mut vm = util::new_vm_with_values_on_stack(input_stack.clone())?;
            vm.state()?
                .memory_mut()
                .store(input_offset.clone(), stored_data.clone());

            // Prepare and run the opcode
            let opcode = environment::LogN { topic_count };
            opcode.execute(&mut vm)?;

            // Inspect the log data
            let state = vm.state()?;
            assert_eq!(state.logged_values().len(), 1);
            let log_message = &state.logged_values()[0];
            assert_eq!(log_message.provenance(), Provenance::Execution);
            match log_message.data() {
                RSVD::Log { data, topics } => {
                    assert_eq!(data, &stored_data);
                    assert_eq!(topics, topics);
                }
                _ => panic!("Invalid payload"),
            }

            // Inspect the stack
            let stack = vm.state()?.stack_mut();
            assert!(stack.is_empty());
        }

        Ok(())
    }

    #[test]
    fn create_modifies_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_value = RSV::new_synthetic(0, RSVD::new_value());
        let input_offset = RSV::new_synthetic(1, RSVD::new_value());
        let input_size = RSV::new_synthetic(2, RSVD::new_value());
        let input_data = RSV::new_synthetic(3, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![
            input_size,
            input_offset.clone(),
            input_value.clone(),
        ])?;
        vm.state()?.memory_mut().store(input_offset, input_data.clone());

        // Prepare and run the opcode
        let opcode = environment::Create;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let address = stack.read(0)?;
        assert_eq!(address.provenance(), Provenance::Execution);
        match address.data() {
            RSVD::Create { value, data } => {
                assert_eq!(value, &input_value);
                assert_eq!(data, &input_data);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn create_2_modifies_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_value = RSV::new_synthetic(0, RSVD::new_value());
        let input_offset = RSV::new_synthetic(1, RSVD::new_value());
        let input_size = RSV::new_synthetic(2, RSVD::new_value());
        let input_salt = RSV::new_synthetic(3, RSVD::new_value());
        let input_data = RSV::new_synthetic(3, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![
            input_salt.clone(),
            input_size,
            input_offset.clone(),
            input_value.clone(),
        ])?;
        vm.state()?.memory_mut().store(input_offset, input_data.clone());

        // Prepare and run the opcode
        let opcode = environment::Create2;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let address = stack.read(0)?;
        assert_eq!(address.provenance(), Provenance::Execution);
        match address.data() {
            RSVD::Create2 { value, salt, data } => {
                assert_eq!(value, &input_value);
                assert_eq!(salt, &input_salt);
                assert_eq!(data, &input_data);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn self_destruct_modifies_stack_and_records_value() -> anyhow::Result<()> {
        // Prepare the vm
        let input_address = RSV::new_synthetic(0, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![input_address.clone()])?;

        // Prepare and run the opcode
        let opcode = environment::SelfDestruct;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert!(stack.is_empty());

        // Inspect the state
        let state = vm.state()?;
        assert_eq!(state.recorded_values().len(), 1);
        let value = &state.recorded_values()[0];
        assert_eq!(value.provenance(), Provenance::Execution);
        match value.data() {
            RSVD::SelfDestruct { target } => {
                assert_eq!(target, &input_address);
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }
}
