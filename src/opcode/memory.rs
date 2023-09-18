//! Opcodes that perform operations on memory or stack on the EVM.

use std::mem;

use crate::{
    constant::{
        CONTRACT_MAXIMUM_SIZE_BYTES,
        DUP_OPCODE_BASE_VALUE,
        PUSH_OPCODE_BASE_VALUE,
        PUSH_OPCODE_MAX_BYTES,
        SWAP_OPCODE_BASE_VALUE,
    },
    error::{container::Locatable, disassembly, execution::Error},
    opcode::{ExecuteResult, Opcode},
    vm::{
        value::{known::KnownWord, Provenance, RSV, RSVD},
        VM,
    },
};

/// The `CALLDATALOAD` opcode gets the input data for the current environment.
///
/// # Semantics
///
/// | Stack Index | Input    | Output                                   |
/// | :---------: | :------: | :--------------------------------------: |
/// | 1           | `offset` | `result := msg.data\[offset:offset+32\]` |
///
/// where:
///
/// - `offset` is the byte offset in the call data from which to start loading
/// - `result` is the result of the specified load, with any bytes after the end
///   of the calldata set to zero
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CallDataLoad;

impl Opcode for CallDataLoad {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the current thread's stack from the VM
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // The offset defines where in the call data is read from
        let offset = stack.pop()?;

        // Construct a constant representing the word read
        let size = vm.build().known(
            instruction_pointer,
            KnownWord::from_le(32u8),
            Provenance::Synthetic,
        );

        // Then we construct the returned value
        let value = vm
            .build()
            .symbolic_exec(instruction_pointer, RSVD::call_data(offset, size));

        // And push it onto the stack
        let mut stack = vm.stack_handle()?;
        stack.push(value)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        1
    }

    fn as_text_code(&self) -> String {
        "CALLDATALOAD".into()
    }

    fn as_byte(&self) -> u8 {
        0x35
    }
}

/// The `CALLDATASIZE` opcode gets the size of the input data for the current
/// environment.
///
/// # Semantics
///
/// | Stack Index | Input | Output          |
/// | :---------: | :---: | :-------------: |
/// | 1           |       | `len(msg.data)` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CallDataSize;

impl Opcode for CallDataSize {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack so a value can be pushed onto it
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Construct the value and push it onto the stack.
        let length = RSV::new_value(instruction_pointer, Provenance::CallDataSize);
        stack.push(length)?;

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
        "CALLDATASIZE".into()
    }

    fn as_byte(&self) -> u8 {
        0x36
    }
}

/// The `CALLDATACOPY` opcode copies the input data for the current environment
/// into memory.
///
/// # Semantics
///
/// | Stack Index | Input        | Output |
/// | :---------: | :----------: | :----: |
/// | 1           | `destOffset` |        |
/// | 2           | `offset`     |        |
/// | 3           | `size`       |        |
///
/// where:
///
/// - `destOffset` is the byte offset in the memory where the call data will be
///   copied to (`mem\[destOffset:destOffset+size\] :=
///   msg.data\[offset:offset+size\]`)
/// - `offset` is the byte offset in the call data from which to start copying
/// - `size` is the number of bytes to copy
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CallDataCopy;

impl Opcode for CallDataCopy {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the current stack to pull the inputs from
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the inputs
        let dest_offset = stack.pop()?;
        let offset = stack.pop()?.constant_fold();
        let size = stack.pop()?.constant_fold();

        // Modify the memory
        if let RSVD::KnownData { value } = size.data() {
            let num_32 = vm.build().known_exec(instruction_pointer, KnownWord::from(32));

            // We bound the copied size to the contract size as anything bigger is going to
            // be impossible at runtime
            let actual_size: usize = value.into();
            let size_limit = actual_size.min(vm.config().single_memory_operation_size_limit);

            let polling_interval = vm.watchdog().poll_every();

            for (count, internal_offset) in (0..size_limit).step_by(32).enumerate() {
                // If we have been told to stop, stop and return an error
                if count % polling_interval == 0 && vm.watchdog().should_stop() {
                    Err(Error::StoppedByWatchdog).locate(instruction_pointer)?;
                }

                let to_add_to_offset = vm
                    .build()
                    .known_exec(instruction_pointer, KnownWord::from(internal_offset));
                let dest_offset = vm.build().symbolic_exec(
                    instruction_pointer,
                    RSVD::Add {
                        left:  dest_offset.clone(),
                        right: to_add_to_offset.clone(),
                    },
                );
                let src_offset = vm.build().symbolic_exec(
                    instruction_pointer,
                    RSVD::Add {
                        left:  offset.clone(),
                        right: to_add_to_offset,
                    },
                );
                let value = vm.build().symbolic_exec(
                    instruction_pointer,
                    RSVD::call_data(src_offset, num_32.clone()),
                );
                let memory = vm.state()?.memory_mut();
                memory.store(dest_offset, value);
            }
        } else {
            let value = vm
                .build()
                .symbolic_exec(instruction_pointer, RSVD::call_data(offset, size));
            let memory = vm.state()?.memory_mut();
            memory.store(dest_offset, value);
        }

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        3
    }

    fn as_text_code(&self) -> String {
        "CALLDATACOPY".into()
    }

    fn as_byte(&self) -> u8 {
        0x37
    }
}

/// The `CODESIZE` opcode gets the code size of the current contract.
///
/// # Semantics
///
/// | Stack Index | Input | Output           |
/// | :---------: | :---: | :--------------: |
/// | 1           |       | `len(this.code)` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CodeSize;

impl Opcode for CodeSize {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the state
        let instruction_pointer = vm.instruction_pointer()?;
        let true_code_size = vm.instructions().len();

        // Construct the value
        let code_size_constant = vm
            .build()
            .known_exec(instruction_pointer, KnownWord::from(true_code_size));

        // Push it onto the stack
        let mut stack = vm.stack_handle()?;
        stack.push(code_size_constant)?;

        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "CODESIZE".into()
    }

    fn as_byte(&self) -> u8 {
        0x38
    }
}

/// The `CODECOPY` opcode copies the current contract's code into memory.
///
/// # Semantics
///
/// | Stack Index | Input        | Output |
/// | :---------: | :----------: | :----: |
/// | 1           | `destOffset` |        |
/// | 2           | `offset`     |        |
/// | 3           | `size`       |        |
///
/// where:
///
/// - `destOffset` is the byte offset in the memory where the call data will be
///   copied to (`mem\[destOffset:destOffset+size\] :=
///   this.code\[offset:offset+size\]`)
/// - `offset` is the byte offset in the code from which to start copying
/// - `size` is the number of bytes to copy
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CodeCopy;

impl Opcode for CodeCopy {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the current stack to pull the inputs from
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the inputs
        let dest_offset = stack.pop()?;
        let offset = stack.pop()?.constant_fold();
        let size = stack.pop()?.constant_fold();

        // Modify the memory
        if let RSVD::KnownData { value } = size.data() {
            let num_32 = vm.build().known_exec(instruction_pointer, KnownWord::from(32));

            // We bound the copied size to the contract size as anything bigger is going to
            // be impossible at runtime
            let actual_size: usize = value.into();
            let size_limit = actual_size.min(CONTRACT_MAXIMUM_SIZE_BYTES);

            let polling_interval = vm.watchdog().poll_every();

            for (count, internal_offset) in (0..size_limit).step_by(32).enumerate() {
                // If we have been told to stop, stop and return an error
                if count % polling_interval == 0 && vm.watchdog().should_stop() {
                    Err(Error::StoppedByWatchdog).locate(instruction_pointer)?;
                }

                let to_add_to_offset = vm
                    .build()
                    .known_exec(instruction_pointer, KnownWord::from(internal_offset));
                let dest_offset = vm.build().symbolic_exec(
                    instruction_pointer,
                    RSVD::Add {
                        left:  dest_offset.clone(),
                        right: to_add_to_offset.clone(),
                    },
                );
                let src_offset = vm.build().symbolic_exec(
                    instruction_pointer,
                    RSVD::Add {
                        left:  offset.clone(),
                        right: to_add_to_offset,
                    },
                );
                let value = vm.build().symbolic_exec(
                    instruction_pointer,
                    RSVD::CodeCopy {
                        offset: src_offset,
                        size:   num_32.clone(),
                    },
                );
                let memory = vm.state()?.memory_mut();
                memory.store(dest_offset, value);
            }
        } else {
            let value = vm
                .build()
                .symbolic_exec(instruction_pointer, RSVD::CodeCopy { offset, size });
            let memory = vm.state()?.memory_mut();
            memory.store(dest_offset, value);
        }

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        3
    }

    fn as_text_code(&self) -> String {
        "CODECOPY".into()
    }

    fn as_byte(&self) -> u8 {
        0x39
    }
}

/// The `EXTCODESIZE` opcode gets the code size of the contract at the target
/// address.
///
/// # Semantics
///
/// | Stack Index | Input     | Output              |
/// | :---------: | :-------: | :-----------------: |
/// | 1           | `address` | `len(address.code)` |
///
/// where:
///
/// - `address` is the address of the contract to get the code size from
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ExtCodeSize;

impl Opcode for ExtCodeSize {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and other necessities
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the target value from the stack
        let address = stack.pop()?;

        // Construct the value and push it onto the stack
        let value = vm
            .build()
            .symbolic_exec(instruction_pointer, RSVD::ExtCodeSize { address });
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
        "EXTCODESIZE".into()
    }

    fn as_byte(&self) -> u8 {
        0x3b
    }
}

/// The `EXTCODECOPY` opcode copies the target contract's code into memory.
///
/// # Semantics
///
/// | Stack Index | Input        | Output |
/// | :---------: | :----------: | :----: |
/// | 1           | `address`    |        |
/// | 2           | `destOffset` |        |
/// | 3           | `offset`     |        |
/// | 4           | `size`       |        |
///
/// where:
///
/// - `address` is the address of the contract to copy the code from
/// - `destOffset` is the byte offset in the memory where the call data will be
///   copied to (`mem\[destOffset:destOffset+size\] :=
///   address.code\[offset:offset+size\]`)
/// - `offset` is the byte offset in the code from which to start copying
/// - `size` is the number of bytes to copy
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ExtCodeCopy;

impl Opcode for ExtCodeCopy {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the current stack to pull the inputs from
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the inputs
        let address = stack.pop()?;
        let dest_offset = stack.pop()?;
        let offset = stack.pop()?.constant_fold();
        let size = stack.pop()?.constant_fold();

        // Modify the memory
        if let RSVD::KnownData { value } = size.data() {
            let num_32 = vm.build().known_exec(instruction_pointer, KnownWord::from(32));

            // We bound the copied size to the contract size as anything bigger is going to
            // be impossible at runtime
            let actual_size: usize = value.into();
            let size_limit = actual_size.min(CONTRACT_MAXIMUM_SIZE_BYTES);

            let polling_interval = vm.watchdog().poll_every();

            for (count, internal_offset) in (0..size_limit).step_by(32).enumerate() {
                // If we have been told to stop, stop and return an error
                if count % polling_interval == 0 && vm.watchdog().should_stop() {
                    Err(Error::StoppedByWatchdog).locate(instruction_pointer)?;
                }

                let to_add_to_offset = vm
                    .build()
                    .known_exec(instruction_pointer, KnownWord::from(internal_offset));
                let dest_offset = vm.build().symbolic_exec(
                    instruction_pointer,
                    RSVD::Add {
                        left:  dest_offset.clone(),
                        right: to_add_to_offset.clone(),
                    },
                );
                let src_offset = vm.build().symbolic_exec(
                    instruction_pointer,
                    RSVD::Add {
                        left:  offset.clone(),
                        right: to_add_to_offset,
                    },
                );
                let value = vm.build().symbolic_exec(
                    instruction_pointer,
                    RSVD::ExtCodeCopy {
                        address: address.clone(),
                        offset:  src_offset,
                        size:    num_32.clone(),
                    },
                );
                let memory = vm.state()?.memory_mut();
                memory.store(dest_offset, value);
            }
        } else {
            let value = vm.build().symbolic_exec(
                instruction_pointer,
                RSVD::ExtCodeCopy {
                    address,
                    offset,
                    size,
                },
            );
            let memory = vm.state()?.memory_mut();
            memory.store(dest_offset, value);
        }

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        4
    }

    fn as_text_code(&self) -> String {
        "EXTCODECOPY".into()
    }

    fn as_byte(&self) -> u8 {
        0x3c
    }
}

/// The `RETURNDATASIZE` opcode gets the size of the output data from the
/// previous (sub-)context.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | `size` |
///
/// where:
///
/// - `size` is the size of the return data
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ReturnDataSize;

impl Opcode for ReturnDataSize {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and environment
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Construct the value and shove it onto the stack.
        let size = RSV::new_value(instruction_pointer, Provenance::ReturnDataSize);
        stack.push(size)?;

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
        "RETURNDATASIZE".into()
    }

    fn as_byte(&self) -> u8 {
        0x3d
    }
}

/// The `RETURNDATACOPY` opcode copies the output data from the previous call
/// into memory.
///
/// # Semantics
///
/// | Stack Index | Input        | Output |
/// | :---------: | :----------: | :----: |
/// | 1           | `destOffset` |        |
/// | 2           | `offset`     |        |
/// | 3           | `size`       |        |
///
/// where:
///
/// - `destOffset` is the byte offset in the memory where the call data will be
///   copied to (`mem\[destOffset:destOffset+size\] :=
///   returnData\[offset:offset+size\]`)
/// - `offset` is the byte offset in the code from which to start copying
/// - `size` is the number of bytes to copy
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ReturnDataCopy;

impl Opcode for ReturnDataCopy {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the current stack to pull the inputs from
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the inputs
        let dest_offset = stack.pop()?;
        let offset = stack.pop()?.constant_fold();
        let size = stack.pop()?.constant_fold();

        // Modify the memory
        if let RSVD::KnownData { value } = size.data() {
            let num_32 = vm.build().known_exec(instruction_pointer, KnownWord::from(32));

            // We bound the copied size to the contract size as anything bigger is going to
            // be impossible at runtime
            let actual_size: usize = value.into();
            let size_limit = actual_size.min(vm.config().single_memory_operation_size_limit);

            let polling_interval = vm.watchdog().poll_every();

            for (count, internal_offset) in (0..size_limit).step_by(32).enumerate() {
                // If we have been told to stop, stop and return an error
                if count % polling_interval == 0 && vm.watchdog().should_stop() {
                    Err(Error::StoppedByWatchdog).locate(instruction_pointer)?;
                }

                let to_add_to_offset = vm
                    .build()
                    .known_exec(instruction_pointer, KnownWord::from(internal_offset));
                let dest_offset = vm.build().symbolic_exec(
                    instruction_pointer,
                    RSVD::Add {
                        left:  dest_offset.clone(),
                        right: to_add_to_offset.clone(),
                    },
                );
                let src_offset = vm.build().symbolic_exec(
                    instruction_pointer,
                    RSVD::Add {
                        left:  offset.clone(),
                        right: to_add_to_offset,
                    },
                );
                let value = vm.build().symbolic_exec(
                    instruction_pointer,
                    RSVD::ReturnData {
                        offset: src_offset,
                        size:   num_32.clone(),
                    },
                );
                let memory = vm.state()?.memory_mut();
                memory.store(dest_offset, value);
            }
        } else {
            let value = vm
                .build()
                .symbolic_exec(instruction_pointer, RSVD::ReturnData { offset, size });
            let memory = vm.state()?.memory_mut();
            memory.store(dest_offset, value);
        }

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        3
    }

    fn as_text_code(&self) -> String {
        "RETURNDATACOPY".into()
    }

    fn as_byte(&self) -> u8 {
        0x3e
    }
}

/// The `POP` opcode pops the top item from the stack.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           | `i`   |        |
///
/// where:
///
/// - `i` is the current top item on the stack
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Pop;

impl Opcode for Pop {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and context data
        let mut stack = vm.stack_handle()?;

        // Pop the value from the stack.
        let value = stack.pop()?;
        vm.state()?.record_value(value);

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        2
    }

    fn arg_count(&self) -> usize {
        1
    }

    fn as_text_code(&self) -> String {
        "POP".into()
    }

    fn as_byte(&self) -> u8 {
        0x50
    }
}

/// The `MLOAD` opcode loads a word from memory.
///
/// # Semantics
///
/// | Stack Index | Input    | Output                              |
/// | :---------: | :------: | :---------------------------------: |
/// | 1           | `offset` | `result := mem\[offset:offset+32\]` |
///
/// where:
///
/// - `offset` is the byte offset in memory to read the word from
/// - `result` is the 32 bytes beginning at `offset`, with any bytes beyond the
///   current memory size (see [`MSize`]) filled with 0s
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MLoad;

impl Opcode for MLoad {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Load the input from the stack
        let offset = vm.stack_handle()?.pop()?;

        // Load the word at that offset from memory
        let result = vm.state()?.memory_mut().load(&offset);

        // Push it onto the stack
        vm.stack_handle()?.push(result)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        1
    }

    fn as_text_code(&self) -> String {
        "MLOAD".into()
    }

    fn as_byte(&self) -> u8 {
        0x51
    }
}

/// The `MSTORE` opcode stores a word to memory.
///
/// # Semantics
///
/// | Stack Index | Input    | Output                            |
/// | :---------: | :------: | :-------------------------------: |
/// | 1           | `offset` |                                   |
/// | 2           | `value`  |                                   |
///
/// where:
///
/// - `offset` is the target byte offset in the memory
/// - `value` is the 32-byte value to write at `offset` as follows
///   `mem\[offset:offset+32\] := value`
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MStore;

impl Opcode for MStore {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack
        let mut stack = vm.stack_handle()?;

        // Get the inputs off the stack
        let offset = stack.pop()?;
        let value = stack.pop()?;

        // Write these to memory
        let memory = vm.state()?.memory_mut();
        memory.store(offset, value);

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "MSTORE".into()
    }

    fn as_byte(&self) -> u8 {
        0x52
    }
}

/// The `MSTORE8` opcode stores a byte to memory.
///
/// # Semantics
///
/// | Stack Index | Input    | Output |
/// | :---------: | :------: | :----: |
/// | 1           | `offset` |        |
/// | 2           | `value`  |        |
///
/// where:
///
/// - `offset` is the byte offset in memory to write to
/// - `value` is the one-byte value to write at `offset` as follows
///   `mem\[offset:offset+1\] := v`
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MStore8;

impl Opcode for MStore8 {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack
        let mut stack = vm.stack_handle()?;

        // Get the inputs off the stack
        let offset = stack.pop()?;
        let value = stack.pop()?;

        // Write these to memory
        let memory = vm.state()?.memory_mut();
        memory.store_8(offset, value);

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "MSTORE8".into()
    }

    fn as_byte(&self) -> u8 {
        0x53
    }
}

/// The `SLOAD` opcode loads a word from storage.
///
/// # Semantics
///
/// | Stack Index | Input | Output                    |
/// | :---------: | :---: | :-----------------------: |
/// | 1           | `key` | `value := storage\[key\]` |
///
/// where:
///
/// - `key` is the 32-byte storage key to read from
/// - `value` is the 32-byte value read from storage, or 0 if that key was never
///   written to
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SLoad;

impl Opcode for SLoad {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the key from the stack
        let key = vm.stack_handle()?.pop()?;

        // Read from storage using that key
        let storage = vm.state()?.storage_mut();
        let result = storage.load(&key);

        // Write it into the stack
        vm.stack_handle()?.push(result)?;

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
        "SLOAD".into()
    }

    fn as_byte(&self) -> u8 {
        0x54
    }
}

/// The `SSTORE` opcode writes a word to storage based on a 32-byte key `k`.
///
/// # Semantics
///
///
/// | Stack Index | Input   | Output |
/// | :---------: | :-----: | :----: |
/// | 1           | `key`   |        |
/// | 2           | `value` |        |
///
/// where:
///
/// - `key` is the 32-byte storage key to write to
/// - `value` is the 32-byte value to be written to as follows `storage\[key\]
///   := value`
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SStore;

impl Opcode for SStore {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        let mut stack = vm.stack_handle()?;

        // Load the inputs from the stack
        let key = stack.pop()?;
        let value = stack.pop()?;

        // Store the value into storage
        vm.state()?.storage_mut().store(key, value);

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "SSTORE".into()
    }

    fn as_byte(&self) -> u8 {
        0x55
    }
}

/// The `MSIZE` opcode gets the size of the active memory in bytes. This is
/// equivalent to the highest offset that has been accessed during the current
/// execution.
///
/// # Semantics
///
/// | Stack Index | Input | Output     |
/// | :---------: | :---: | :--------: |
/// | 1           |       | `len(mem)` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MSize;

impl Opcode for MSize {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Prepare the value
        let size = RSV::new_value(instruction_pointer, Provenance::MSize);

        // Push it onto the stack
        stack.push(size)?;

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
        "MSIZE".into()
    }

    fn as_byte(&self) -> u8 {
        0x59
    }
}

/// The `PUSH0` opcode places the value 0 on the top of the stack.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | `0`    |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Push0;

impl Opcode for Push0 {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;

        // Construct the value of zero
        let zero = vm.build().symbolic(
            instruction_pointer,
            RSVD::new_known(KnownWord::zero()),
            Provenance::Bytecode,
        );

        // Push it onto the stack
        let mut stack = vm.stack_handle()?;
        stack.push(zero)?;

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
        "PUSH0".into()
    }

    fn as_byte(&self) -> u8 {
        0x5f
    }
}

/// The `PUSHN` opcodes push an `N`-byte item onto the stack, where `0 < N <=
/// 32`. The item is specified as the next `N` bytes of the instruction stream.
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           |       | `item` |
///
/// where:
///
/// - `item` is the next `N` bytes of the instruction stream; the value to push
///   onto the stack
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PushN {
    byte_count: u8,
    bytes:      Vec<u8>,
}

impl PushN {
    /// Construct a new instance of the `PUSHN` opcode for some `n`.
    ///
    /// The `bytes` are assumed to be in big-endian byte ordering, and are
    /// converted to be stored in little endian ordering.
    ///
    /// # Errors
    ///
    /// If `n` is not in the specified range.
    pub fn new(n: u8, bytes: impl Into<Vec<u8>>) -> Result<Self, disassembly::Error> {
        let mut bytes: Vec<u8> = bytes.into();
        bytes = bytes.into_iter().rev().collect();
        if n > 0 && n <= PUSH_OPCODE_MAX_BYTES && bytes.len() == n as usize {
            Ok(Self {
                byte_count: n,
                bytes,
            })
        } else {
            Err(disassembly::Error::InvalidPushSize(n))
        }
    }

    /// Get the number of bytes this `PUSHN` opcode pushes onto the stack.
    #[must_use]
    pub fn byte_size(&self) -> u8 {
        self.byte_count
    }

    /// Get the data to be pushed onto the stack by this opcode. It is
    /// guaranteed that `bytes_data.len() == byte_size()`.
    #[must_use]
    pub fn bytes_data(&self) -> &[u8] {
        &self.bytes
    }

    /// Gets the bytes that are pushed as a known word.
    #[must_use]
    #[allow(clippy::missing_panics_doc)] // Unwrapped array has known size
    pub fn bytes_as_word(&self) -> KnownWord {
        // Get the bytes we have and extend them out to be long enough
        let mut bytes = self.bytes.clone();
        bytes.resize(mem::size_of::<KnownWord>(), 0x0);

        // This gives us a word we want to interpret as LE
        let bytes: [u8; mem::size_of::<KnownWord>()] = bytes
            .as_slice()
            .try_into()
            .expect("A known size array was not of that size");
        KnownWord::from_le_bytes(bytes)
    }
}

impl Opcode for PushN {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;

        // Pull the data out of the opcode; validation is done in parsing
        let item_data = self.bytes_as_word();

        // Construct the value to push
        let item = vm.build().symbolic(
            instruction_pointer,
            RSVD::new_known(item_data),
            Provenance::Bytecode,
        );

        // Push it onto the stack
        let mut stack = vm.stack_handle()?;
        stack.push(item)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        format!("PUSH{}", self.byte_count)
    }

    fn as_byte(&self) -> u8 {
        PUSH_OPCODE_BASE_VALUE + self.byte_count
    }

    fn encode(&self) -> Vec<u8> {
        let mut data = vec![self.as_byte()];
        let bytes_be: Vec<u8> = self.bytes_data().iter().rev().copied().collect();
        data.extend(bytes_be);
        data
    }
}

/// The `DUPN` opcode duplicates the `N`th item on the stack, where `0 < N <=
/// 16`, pushing it on the top of the stack. This makes the duplicated item the
/// `N+1`th item.
///
/// # Semantics
///
/// | Stack Index | Input  | Output |
/// | :---------: | :----: | :----: |
/// | 1           |        | `item` |
/// | ...         |        |        |
/// | `N+1`       | `item` | `item` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct DupN {
    item: u8,
}

impl DupN {
    /// Constructs a new instance of the `DUPN` opcode.
    ///
    /// # Errors
    ///
    /// If the provided `n` is not in the specified range.
    pub fn new(n: u8) -> Result<Self, disassembly::Error> {
        if 0 < n && n <= 16 {
            Ok(Self { item: n })
        } else {
            Err(disassembly::Error::InvalidStackItem {
                item: n,
                name: "DUP".into(),
            })
        }
    }

    /// Gets the item on the stack that this opcode is duplicating.
    #[must_use]
    pub fn n(&self) -> u8 {
        self.item
    }
}

impl Opcode for DupN {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack
        let mut stack = vm.stack_handle()?;

        // Get the dup frame, converting from EVM to internal semantics and with the
        // subtraction always safe as `DupN` is guaranteed to have `item >= 1`.
        let frame = u32::from(self.n()) - 1;

        // Duplicate the specified item; verification is done in parsing
        stack.dup(frame)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        self.item as usize
    }

    fn as_text_code(&self) -> String {
        format!("DUP{}", self.item)
    }

    fn as_byte(&self) -> u8 {
        DUP_OPCODE_BASE_VALUE + self.item
    }
}

/// The `SWAPN` opcode exchanges the first and `N+1`th stack items, where `0 < N
/// <= 16`.
///
/// # Semantics
///
/// | Stack Index | Input   | Output  |
/// | :---------: | :-----: | :-----: |
/// | 1           | `item1` | `item2` |
/// | ...         |         |         |
/// | `N+1`       | `item2` | `item1` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SwapN {
    item: u8,
}

impl SwapN {
    /// Constructs a new instance of the `SWAPN` opcode.
    ///
    /// # Errors
    ///
    /// If the provided `n` is not in the specified range.
    pub fn new(n: u8) -> Result<Self, disassembly::Error> {
        if 0 < n && n <= 16 {
            Ok(Self { item: n })
        } else {
            Err(disassembly::Error::InvalidStackItem {
                item: n,
                name: "SWAP".into(),
            })
        }
    }

    /// Gets the item on the stack that this opcode is swapping with.
    #[must_use]
    pub fn n(&self) -> u8 {
        self.item
    }
}

impl Opcode for SwapN {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack
        let mut stack = vm.stack_handle()?;

        // Compute the internal item to swap with
        let frame = u32::from(self.n());

        // Swap the items
        stack.swap(frame)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        3
    }

    fn arg_count(&self) -> usize {
        self.item as usize + 1
    }

    fn as_text_code(&self) -> String {
        format!("SWAP{}", self.item)
    }

    fn as_byte(&self) -> u8 {
        SWAP_OPCODE_BASE_VALUE + self.item
    }
}

#[cfg(test)]
mod test {
    use rand::random;

    use crate::{
        opcode::{memory, test_util as util, Opcode},
        vm::{
            state::memory::MemStoreSize,
            value::{known::KnownWord, Provenance, RuntimeBoxedVal, RSV, RSVD},
        },
    };

    #[test]
    fn call_data_load_inserts_value_with_correct_provenance() -> anyhow::Result<()> {
        // First we have to prepare the virtual machine and the instruction
        let input_offset = RSV::new_value(0, Provenance::Synthetic);
        let mut vm = util::new_vm_with_values_on_stack(vec![input_offset])?;

        // Run the opcode
        let opcode = memory::CallDataLoad;
        opcode.execute(&mut vm)?;

        // And then inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);

        let item = stack.read(0)?;
        assert_eq!(item.instruction_pointer(), 0);
        match item.data() {
            RSVD::CallData { offset, .. } => {
                assert_eq!(offset.provenance(), Provenance::Synthetic);
            }
            _ => panic!("Invalid data"),
        };
        assert_eq!(item.provenance(), Provenance::Execution);

        Ok(())
    }

    #[test]
    fn call_data_size_pushes_sentinel_onto_stack() -> anyhow::Result<()> {
        // Prepare the virtual-machine
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Run the opcode
        let opcode = memory::CallDataSize;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let value = stack.read(0)?;
        assert_eq!(value.provenance(), Provenance::CallDataSize);

        Ok(())
    }

    #[test]
    fn call_data_copy_copies_into_memory() -> anyhow::Result<()> {
        // Prepare the values on stack and VM
        let dest_offset = RSV::new_synthetic(0, RSVD::new_value());
        let input_offset = RSV::new_synthetic(1, RSVD::new_value());
        let input_size = RSV::new_synthetic(2, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![
            input_size.clone(),
            input_offset.clone(),
            dest_offset.clone(),
        ])?;

        // Prepare and run the opcode
        let opcode = memory::CallDataCopy;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert!(stack.is_empty());

        // Inspect the memory
        let memory = vm.state()?.memory_mut();
        let loaded = memory.load(&dest_offset);
        match loaded.data() {
            RSVD::CallData { offset, size, .. } => {
                assert_eq!(offset, &input_offset);
                assert_eq!(size, &input_size);
            }
            _ => panic!("Incorrect payload"),
        };
        assert_eq!(loaded.provenance(), Provenance::Execution);

        Ok(())
    }

    #[test]
    fn code_size_pushes_value_onto_stack() -> anyhow::Result<()> {
        // First we have to prepare the virtual machine
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;
        let code_size_actual = vm.instructions().len();

        // Run the opcode
        let opcode = memory::CodeSize;
        opcode.execute(&mut vm)?;

        // Check that the correct value is on the stack.
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let value = stack.read(0)?;
        assert_eq!(value.provenance(), Provenance::Execution);
        match value.data() {
            RSVD::KnownData { value, .. } => {
                assert_eq!(value, &KnownWord::from(code_size_actual));
            }
            _ => panic!("Incorrect data payload"),
        }

        Ok(())
    }

    #[test]
    fn code_copy_copies_into_memory() -> anyhow::Result<()> {
        // Prepare the values on stack and VM
        let dest_offset = RSV::new_synthetic(0, RSVD::new_value());
        let input_offset = RSV::new_synthetic(1, RSVD::new_value());
        let input_size = RSV::new_synthetic(2, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![
            input_size.clone(),
            input_offset.clone(),
            dest_offset.clone(),
        ])?;

        // Prepare and run the opcode
        let opcode = memory::CodeCopy;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert!(stack.is_empty());

        // Inspect the memory
        let memory = vm.state()?.memory_mut();
        let loaded = memory.load(&dest_offset);
        match loaded.data() {
            RSVD::CodeCopy { offset, size } => {
                assert_eq!(offset, &input_offset);
                assert_eq!(size, &input_size);
            }
            _ => panic!("Incorrect payload"),
        }
        assert_eq!(loaded.provenance(), Provenance::Execution);

        Ok(())
    }

    #[test]
    fn ext_code_size_puts_value_on_stack() -> anyhow::Result<()> {
        // Prepare the virtual machine
        let address = RSV::new_synthetic(0, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![address.clone()])?;

        // Prepare and run the opcode
        let opcode = memory::ExtCodeSize;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let value = stack.read(0)?;
        assert_eq!(value.provenance(), Provenance::Execution);
        assert_eq!(value.data(), &RSVD::ExtCodeSize { address });

        Ok(())
    }

    #[test]
    fn ext_code_copy_copies_into_memory() -> anyhow::Result<()> {
        // Prepare the values on stack and VM
        let input_address = RSV::new_synthetic(7, RSVD::new_value());
        let dest_offset = RSV::new_synthetic(0, RSVD::new_value());
        let input_offset = RSV::new_synthetic(1, RSVD::new_value());
        let input_size = RSV::new_synthetic(2, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![
            input_size.clone(),
            input_offset.clone(),
            dest_offset.clone(),
            input_address.clone(),
        ])?;

        // Prepare and run the opcode
        let opcode = memory::ExtCodeCopy;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert!(stack.is_empty());

        // Inspect the memory
        let memory = vm.state()?.memory_mut();
        let loaded = memory.load(&dest_offset);
        match loaded.data() {
            RSVD::ExtCodeCopy {
                address,
                offset,
                size,
            } => {
                assert_eq!(address, &input_address);
                assert_eq!(offset, &input_offset);
                assert_eq!(size, &input_size);
            }
            _ => panic!("Incorrect payload"),
        };
        assert_eq!(loaded.provenance(), Provenance::Execution);

        Ok(())
    }

    #[test]
    fn return_data_size_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = memory::ReturnDataSize;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let item = stack.read(0)?;
        assert_eq!(item.provenance(), Provenance::ReturnDataSize);

        Ok(())
    }

    #[test]
    fn return_data_copy_copies_into_memory() -> anyhow::Result<()> {
        // Prepare the values on stack and VM
        let dest_offset = RSV::new_synthetic(0, RSVD::new_value());
        let input_offset = RSV::new_synthetic(1, RSVD::new_value());
        let input_size = RSV::new_synthetic(2, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![
            input_size.clone(),
            input_offset.clone(),
            dest_offset.clone(),
        ])?;

        // Prepare and run the opcode
        let opcode = memory::ReturnDataCopy;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert!(stack.is_empty());

        // Inspect the memory
        let memory = vm.state()?.memory_mut();
        let loaded = memory.load(&dest_offset);
        match loaded.data() {
            RSVD::ReturnData { offset, size } => {
                assert_eq!(offset, &input_offset);
                assert_eq!(size, &input_size);
            }
            _ => panic!("Incorrect payload"),
        }
        assert_eq!(loaded.provenance(), Provenance::Execution);

        Ok(())
    }

    #[test]
    fn pop_pops_value_from_stack() -> anyhow::Result<()> {
        // Prepare the value on stack and the VM
        let mut vm =
            util::new_vm_with_values_on_stack(vec![RSV::new_synthetic(0, RSVD::new_value())])?;

        // Prepare and run the opcode
        let opcode = memory::Pop;
        opcode.execute(&mut vm)?;

        // Inspect the stack state
        let stack = vm.state()?.stack_mut();
        assert!(stack.is_empty());

        Ok(())
    }

    #[test]
    fn m_load_loads_word_from_memory() -> anyhow::Result<()> {
        // Prepare the values and the vm
        let offset = RSV::new_synthetic(0, RSVD::new_value());
        let data = RSV::new_synthetic(1, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![offset.clone()])?;
        vm.state()?.memory_mut().store(offset.clone(), data.clone());

        // Prepare and run the opcode
        let opcode = memory::MLoad;
        opcode.execute(&mut vm)?;

        // Inspect the stack state
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        assert_eq!(stack.read(0)?, &data);

        // Inspect the memory state
        let memory = vm.state()?.memory_mut();
        assert_eq!(memory.load(&offset), data);

        Ok(())
    }

    #[test]
    fn m_store_stores_word_to_memory() -> anyhow::Result<()> {
        // Prepare the values and the vm
        let offset = RSV::new_synthetic(0, RSVD::new_value());
        let data = RSV::new_synthetic(1, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![data.clone(), offset.clone()])?;

        // Prepare and run the opcode
        let opcode = memory::MStore;
        opcode.execute(&mut vm)?;

        // Inspect the stack state
        assert!(vm.state()?.stack_mut().is_empty());

        // Inspect the memory state
        let memory = vm.state()?.memory_mut();
        assert_eq!(memory.load(&offset), data);
        assert_eq!(memory.query_store_size(&offset), Some(MemStoreSize::Word));

        Ok(())
    }

    #[test]
    fn m_store_8_stores_word_to_memory() -> anyhow::Result<()> {
        // Prepare the values and the vm
        let offset = RSV::new_synthetic(0, RSVD::new_value());
        let data = RSV::new_synthetic(1, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![data.clone(), offset.clone()])?;

        // Prepare and run the opcode
        let opcode = memory::MStore8;
        opcode.execute(&mut vm)?;

        // Inspect the stack state
        assert!(vm.state()?.stack_mut().is_empty());

        // Inspect the memory state
        let memory = vm.state()?.memory_mut();
        assert_eq!(memory.load(&offset), data);
        assert_eq!(memory.query_store_size(&offset), Some(MemStoreSize::Byte));

        Ok(())
    }

    #[test]
    fn s_load_loads_word_from_storage() -> anyhow::Result<()> {
        // Prepare the values and the vm
        let input_key = RSV::new_synthetic(0, RSVD::new_value());
        let input_value = RSV::new_synthetic(1, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![input_key.clone()])?;
        vm.state()?
            .storage_mut()
            .store(input_key.clone(), input_value.clone());

        // Prepare and run the opcode
        let opcode = memory::SLoad;
        opcode.execute(&mut vm)?;

        // Inspect the stack state
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        match stack.read(0)?.data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(key, &input_key);
                assert_eq!(value, &input_value);
            }
            _ => panic!("Incorrect payload"),
        }

        // Inspect the storage state
        let storage = vm.state()?.storage_mut();
        assert_eq!(storage.entry_count(), 1);
        match storage.load(&input_key).data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(key, &input_key);
                assert_eq!(value, &input_value);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn s_store_writes_word_to_storage() -> anyhow::Result<()> {
        // Prepare the values and the vm
        let input_key = RSV::new_synthetic(0, RSVD::new_value());
        let input_value = RSV::new_synthetic(1, RSVD::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_value.clone(), input_key.clone()])?;

        // Prepare and run the opcode
        let opcode = memory::SStore;
        opcode.execute(&mut vm)?;

        // Inspect the stack state
        assert!(vm.state()?.stack_mut().is_empty());

        // Inspect the storage state
        let storage = vm.state()?.storage_mut();
        assert_eq!(storage.entry_count(), 1);
        match storage.load(&input_key).data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(key, &input_key);
                assert_eq!(value, &input_value);
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }

    #[test]
    fn m_size_writes_variable_to_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = memory::MSize;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let value = stack.read(0)?;
        assert_eq!(value.provenance(), Provenance::MSize);

        Ok(())
    }

    #[test]
    fn push_0_pushes_zero_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = memory::Push0;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let value = stack.read(0)?;
        assert_eq!(value.provenance(), Provenance::Bytecode);
        match value.data() {
            RSVD::KnownData { value, .. } => assert_eq!(value, &KnownWord::zero()),
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    #[allow(unreachable_code)]
    fn push_n_pushes_encoded_value_onto_stack() -> anyhow::Result<()> {
        // We want to test for all valid push sizes
        for byte_count in 1..=32 {
            // Generate some random data to push onto the stack
            let mut bytes: Vec<u8> = Vec::new();
            for _ in 0..byte_count {
                bytes.push(random());
            }

            // Prepare the vm
            let mut vm = util::new_vm_with_values_on_stack(vec![])?;

            // Prepare and run the opcode
            let opcode = memory::PushN {
                byte_count,
                bytes: bytes.clone(),
            };
            opcode.execute(&mut vm)?;

            // Inspect the stack to check on things
            let stack = vm.state()?.stack_mut();
            assert_eq!(stack.depth(), 1);
            let value = stack.read(0)?;
            assert_eq!(value.provenance(), Provenance::Bytecode);
            match value.data() {
                RSVD::KnownData { value, .. } => {
                    assert_eq!(value, &opcode.bytes_as_word());
                }
                _ => panic!("Incorrect payload"),
            };
        }

        Ok(())
    }

    #[test]
    fn dup_n_duplicates_specified_value_on_stack() -> anyhow::Result<()> {
        // We want to test for all valid dup sizes
        for item in 1..=16 {
            // Prepare the items
            let item_to_dup = RSV::new_synthetic(0, RSVD::new_known(KnownWord::zero()));
            let other_item = RSV::new_synthetic(1, RSVD::new_value());

            // Prepare the vm's stack
            let mut stack: Vec<RuntimeBoxedVal> = Vec::new();
            stack.push(item_to_dup.clone());
            for _ in 1..item {
                stack.push(other_item.clone());
            }

            // Prepare the vm
            let mut vm = util::new_vm_with_values_on_stack(stack)?;

            // Prepare and run the opcode
            let opcode = memory::DupN { item };
            opcode.execute(&mut vm)?;

            // Inspect the stack
            let stack = vm.state()?.stack_mut();
            assert_eq!(stack.depth(), item as usize + 1);
            assert_eq!(stack.read(0)?, &item_to_dup);
        }

        Ok(())
    }

    #[test]
    fn swap_swaps_values_on_stack() -> anyhow::Result<()> {
        // We want to test for all the valid swap depths
        for item in 1..=16 {
            // Prepare the items
            let stack_top = RSV::new_synthetic(0, RSVD::new_known(KnownWord::zero()));
            let item_to_swap = RSV::new_synthetic(1, RSVD::new_known(KnownWord::from_le(1u32)));
            let other_item = RSV::new_synthetic(1, RSVD::new_value());

            // Prepare the VM's stack
            let mut stack: Vec<RuntimeBoxedVal> = Vec::new();
            stack.push(item_to_swap.clone());
            for _ in 0..item - 1 {
                stack.push(other_item.clone());
            }
            stack.push(stack_top.clone());
            let input_stack_size = stack.len();
            assert_eq!(input_stack_size, item as usize + 1);

            // Prepare the vm
            let mut vm = util::new_vm_with_values_on_stack(stack)?;

            // Prepare and run the opcode
            let opcode = memory::SwapN { item };
            opcode.execute(&mut vm)?;

            // Inspect the stack
            let stack = vm.state()?.stack_mut();
            assert_eq!(stack.depth(), input_stack_size);
            let item_at_depth = stack.read(u32::from(item))?;
            let item_at_top = stack.read(0)?;
            assert_eq!(item_at_depth, &stack_top);
            assert_eq!(item_at_top, &item_to_swap);
        }

        Ok(())
    }
}
