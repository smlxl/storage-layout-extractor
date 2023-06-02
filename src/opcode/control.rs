//! Opcodes that perform control(-flow) operations on the EVM.

use crate::{
    error::execution,
    opcode::{util, ExecuteResult, Opcode},
    vm::{
        value::{known_data::KnownData, Provenance, SymbolicValue, SymbolicValueData},
        VM,
    },
};

/// The `STOP` opcode halts execution on the EVM, exiting the current call
/// context.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Stop;

impl Opcode for Stop {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // In the case of symbolic execution we only want to stop executing the current
        // thread, so we mark it as such to return control to the VM.
        vm.kill_current_thread();

        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        0
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "STOP".into()
    }

    fn as_byte(&self) -> u8 {
        0x00
    }
}

/// The `INVALID` opcode is invalid and instantly reverts execution.
///
/// Equivalent to [`Revert`] with 0 and 0 as its stack parameters.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Invalid;

impl Opcode for Invalid {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Symbolic execution explores _all_ branches in the code speculatively. This
        // means that, even if we reach a revert on a given branch, we may have learned
        // useful information during the execution on that branch that led up to the
        // revert.
        //
        // To this end, we continue to execute all other branches, and only kill the
        // current branch as _its_ execution has ended.
        vm.kill_current_thread();

        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        0
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "INVALID".into()
    }

    fn as_byte(&self) -> u8 {
        0xfe
    }
}

/// The `JUMP` opcode alters the program counter to a new offset in the code.
///
/// The destination `counter` must be a [`JumpDest`] instruction.
///
/// # Semantics
///
/// | Stack Index | Input     | Output           |
/// | :---------: | :-------: | :--------------: |
/// | 1           | `counter` | `$pc := counter` |
///
/// where:
///
/// - `$pc` is the program counter
/// - `counter` is the new value for the program counter
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
///
/// Execution is reverted if the target instruction is not `JUMPDEST`.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Jump;

impl Opcode for Jump {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the argument
        let counter = vm.stack_handle()?.pop()?;

        // In `solc` compiled code, the top of the stack at jump time is a non-computed
        // immediate, allowing us to actually alter the program counter
        let jump_target = match util::validate_jump_destination(&counter, vm) {
            Ok(target) => target,
            Err(payload) => {
                // Counter was non-trivial here, so we hold onto it.
                vm.state()?.record_value(counter);

                return match payload.payload {
                    execution::Error::NoConcreteJumpDestination => {
                        // If we do not have an immediate, we instead want to halt
                        // execution on this branch as it would not be valid to
                        // continue without knowing where to jump to
                        vm.kill_current_thread();
                        Ok(())
                    }
                    _ => Err(payload),
                };
            }
        };

        // If it is, we set the execution position to there, as executing the next
        // instruction would be incorrect. Note that the `VM` will step from the target,
        // but as it is a JUMPDEST no-op this is fine.
        vm.execution_thread_mut()?.jump(jump_target);

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        8
    }

    fn arg_count(&self) -> usize {
        1
    }

    fn as_text_code(&self) -> String {
        "JUMP".into()
    }

    fn as_byte(&self) -> u8 {
        0x56
    }
}

/// The `JUMPI` opcode conditionally alters the program counter based on the
/// value of a boolean `b`.
///
/// The destination `c` must be a [`JumpDest`] instruction.
///
/// # Semantics
///
/// | Stack Index | Input     | Output                                        |
/// | :---------: | :-------: | :-------------------------------------------: |
/// | 1           | `counter` | `if cond then $pc := counter else $pc := $pc` |
/// | 2           | `cond`    |                                               |
///
/// where:
///
/// - `$pc` is the program counter
/// - `counter` is the new value for the program counter
/// - `cond` is the boolean value to check before executing the jump.
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
///
/// Execution is reverted if the target instruction is not `JUMPDEST`.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct JumpI;

impl Opcode for JumpI {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the arguments
        let counter = vm.stack_handle()?.pop()?;
        let condition = vm.stack_handle()?.pop()?;

        // We want to store that the condition was indeed a condition, even if the jump
        // target is invalid
        let condition = SymbolicValue::new_from_execution(
            vm.instruction_pointer()?,
            SymbolicValueData::Condition { value: condition },
        );
        vm.state()?.record_value(condition);

        // In `solc` compiled code, the top of the stack at jump time is a non-computed
        // immediate, allowing us to actually alter the program counter
        match util::validate_jump_destination(&counter, vm) {
            Ok(target) => {
                // If we do have a valid jump target, we need to fork off an execution thread so
                // that both branches can be executed. Note that the `VM` will step from the
                // target, but as it is a JUMPDEST no-op this is fine.
                vm.fork_current_thread(target)?;

                // Done, so return ok, leaving the current thread in the same position as it
                // needs to be stepped by the `VM`
                Ok(())
            }
            Err(payload) => {
                // Counter was non-trivial here, so we hold onto it.
                vm.state()?.record_value(counter);

                // If we get an error here, we need to change what we do based on whether it is
                // in this thread or the target thread.
                let result = match payload.payload {
                    execution::Error::NoConcreteJumpDestination { .. } => Ok(payload),
                    execution::Error::NonExistentJumpTarget { .. } => Ok(payload),
                    execution::Error::InvalidJumpTarget { .. } => Ok(payload),
                    execution::Error::InvalidOffsetForJump { .. } => Ok(payload),
                    _ => Err(payload),
                }?;

                // If it is an error that only affects the potential _target_ thread, we need to
                // store it and continue execution on the current thread.
                vm.store_error(result);
                Ok(())
            }
        }
    }

    fn min_gas_cost(&self) -> usize {
        10
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "JUMPI".into()
    }

    fn as_byte(&self) -> u8 {
        0x57
    }
}

/// The `PC` opcode gets the value of the program counter _prior_ to the
/// increment corresponding to this instruction.
///
/// # Semantics
///
/// | Stack Index | Input | Output  |
/// | :---------: | :---: | :-----: |
/// | 1           |       | $pc - 1 |
///
/// where:
///
/// - `$pc` is the value of the program counter
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct PC;

impl Opcode for PC {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and instruction pointer
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Construct the value and push it onto the stack
        let result = SymbolicValue::new_known_value(
            instruction_pointer,
            KnownData::UInt {
                value: instruction_pointer.to_le_bytes().to_vec(),
            },
            Provenance::ProgramCounter,
        );
        stack.push(result)?;

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
        "PC".into()
    }

    fn as_byte(&self) -> u8 {
        0x58
    }
}

/// The `JUMPDEST` opcode marks a valid destination for a jump.
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct JumpDest;

impl Opcode for JumpDest {
    fn execute(&self, _vm: &mut VM) -> ExecuteResult {
        // This is a no-op at execution time, but allows the virtual machine to perform
        // some validation.
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        1
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "JUMPDEST".into()
    }

    fn as_byte(&self) -> u8 {
        0x5b
    }
}

/// The `CALL` opcode performs a message call into an account.
///
/// # Semantics
///
/// | Stack Index | Input       | Output                             |
/// | :---------: | :---------: | :--------------------------------: |
/// | 1           | `gas`       | `if call_did_revert then 0 else 1` |
/// | 2           | `addr`      |                                    |
/// | 3           | `value`     |                                    |
/// | 4           | `argOffset` |                                    |
/// | 5           | `argSize`   |                                    |
/// | 6           | `retOffset` |                                    |
/// | 7           | `retSize`   |                                    |
///
/// where:
///
/// - `gas` is the amount of gas sent to the sub-context for execution
/// - `address` is the account with the context to execute
/// - `value` is the value in WEI to send to `address`
/// - `argOffset` is the byte offset in the memory where the calldata can be
///   found
/// - `argSize` is the number of bytes in memory from `argOffset` to the end of
///   the calldata
/// - `retOffset` the byte offset in memory where the return data from the sub
///   context can be found
/// - `retSize` the number of bytes to copy for the return data
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Call;

impl Opcode for Call {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env info
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Pull the arguments off the stack
        let gas = stack.pop()?;
        let address = stack.pop()?;
        let value = stack.pop()?;
        let arg_offset = stack.pop()?;
        let arg_size = stack.pop()?;
        let ret_offset = stack.pop()?;
        let ret_size = stack.pop()?;

        // Read the input data to touch it if it hasn't already been touched
        vm.state()?.memory_mut().load(&arg_offset);

        // Create the return value and store it in memory
        let ret_value = SymbolicValue::new_value(instruction_pointer, Provenance::MessageCall);
        vm.state()?.memory_mut().store(ret_offset, ret_value);

        // Create the value representing the call
        let call_return = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::CallWithValue {
                gas,
                address,
                value,
                arg_size,
                ret_size,
            },
        );

        // Push it onto the stack
        vm.stack_handle()?.push(call_return)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        7
    }

    fn as_text_code(&self) -> String {
        "CALL".into()
    }

    fn as_byte(&self) -> u8 {
        0xf1
    }
}

/// The `CALLCODE` opcode performs a message call into the current account with
/// another account's code.
///
/// # Note
///
/// This opcode is deprecated and almost never used.
///
/// # Semantics
///
/// | Stack Index | Input       | Output                             |
/// | :---------: | :---------: | :--------------------------------: |
/// | 1           | `gas`       | `if call_did_revert then 0 else 1` |
/// | 2           | `addr`      |                                    |
/// | 3           | `value`     |                                    |
/// | 4           | `argOffset` |                                    |
/// | 5           | `argSize`   |                                    |
/// | 6           | `retOffset` |                                    |
/// | 7           | `retSize`   |                                    |
///
/// where:
///
/// - `gas` is the amount of gas sent to the sub-context for execution
/// - `address` is the account with the code to execute
/// - `value` is the value in WEI to send to `address`
/// - `argOffset` is the byte offset in the memory where the calldata can be
///   found
/// - `argSize` is the number of bytes in memory from `argOffset` to the end of
///   the calldata
/// - `retOffset` the byte offset in memory where the return data from the sub
///   context can be found
/// - `retSize` the number of bytes to copy for the return data
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CallCode;

impl Opcode for CallCode {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // As the implementation for symbolic execution is identical, we delegate to the
        // standard call opcode.
        Call.execute(vm)
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        7
    }

    fn as_text_code(&self) -> String {
        "CALLCODE".into()
    }

    fn as_byte(&self) -> u8 {
        0xf2
    }
}

/// The `DELEGATECALL` opcode performs a call using code from another account
/// while reusing the storage, sender, and value of the current account.
///
/// # Semantics
///
/// | Stack Index | Input       | Output                             |
/// | :---------: | :---------: | :--------------------------------: |
/// | 1           | `gas`       | `if call_did_revert then 0 else 1` |
/// | 2           | `addr`      |                                    |
/// | 3           | `argOffset` |                                    |
/// | 4           | `argSize`   |                                    |
/// | 5           | `retOffset` |                                    |
/// | 6           | `retSize`   |                                    |
///
/// where:
///
/// - `gas` is the amount of gas sent to the sub-context for execution
/// - `address` is the account with the code to execute
/// - `argOffset` is the byte offset in the memory where the calldata can be
///   found
/// - `argSize` is the number of bytes in memory from `argOffset` to the end of
///   the calldata
/// - `retOffset` the byte offset in memory where the return data from the sub
///   context can be found
/// - `retSize` the number of bytes to copy for the return data
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct DelegateCall;

impl Opcode for DelegateCall {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env info
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Pull the arguments off the stack
        let gas = stack.pop()?;
        let address = stack.pop()?;
        let arg_offset = stack.pop()?;
        let arg_size = stack.pop()?;
        let ret_offset = stack.pop()?;
        let ret_size = stack.pop()?;

        // Read the input data to touch it if it hasn't already been touched
        vm.state()?.memory_mut().load(&arg_offset);

        // Create the return value and store it in memory
        let ret_value = SymbolicValue::new_value(instruction_pointer, Provenance::MessageCall);
        vm.state()?.memory_mut().store(ret_offset, ret_value);

        // Create the value representing the call
        let call_return = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::CallWithoutValue {
                gas,
                address,
                arg_size,
                ret_size,
            },
        );

        // Push it onto the stack
        vm.stack_handle()?.push(call_return)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        7
    }

    fn as_text_code(&self) -> String {
        "DELEGATECALL".into()
    }

    fn as_byte(&self) -> u8 {
        0xf4
    }
}

/// The `STATICCALL` opcode performs a call using code from another account
/// while disallowing modification of state in the sub-context.
///
/// In particular, it disallows use of the following opcodes:
///
/// - [`crate::opcode::environment::Create`]
/// - [`crate::opcode::environment::Create2`]
/// - [`crate::opcode::environment::LogN`]
/// - [`crate::opcode::memory::SStore`]
/// - [`crate::opcode::environment::SelfDestruct`]
/// - [`Call`] if the `value` sent is not 0
///
/// # Semantics
///
/// | Stack Index | Input       | Output                             |
/// | :---------: | :---------: | :--------------------------------: |
/// | 1           | `gas`       | `if call_did_revert then 0 else 1` |
/// | 2           | `addr`      |                                    |
/// | 3           | `argOffset` |                                    |
/// | 4           | `argSize`   |                                    |
/// | 5           | `retOffset` |                                    |
/// | 6           | `retSize`   |                                    |
///
/// where:
///
/// - `gas` is the amount of gas sent to the sub-context for execution
/// - `address` is the account with the code to execute
/// - `argOffset` is the byte offset in the memory where the calldata can be
///   found
/// - `argSize` is the number of bytes in memory from `argOffset` to the end of
///   the calldata
/// - `retOffset` the byte offset in memory where the return data from the sub
///   context can be found
/// - `retSize` the number of bytes to copy for the return data
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct StaticCall;

impl Opcode for StaticCall {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // As the implementation for symbolic execution is identical, we delegate to the
        // delegatecall opcode.
        DelegateCall.execute(vm)
    }

    fn min_gas_cost(&self) -> usize {
        100
    }

    fn arg_count(&self) -> usize {
        7
    }

    fn as_text_code(&self) -> String {
        "STATICCALL".into()
    }

    fn as_byte(&self) -> u8 {
        0xfa
    }
}

/// The `RETURN` opcode halts execution and returns the provided data of `size`
/// at `offset` in memory.
///
/// This opcode exits the current context with a success.
///
/// # Semantics
///
/// | Stack Index | Input    | Output |
/// | :---------: | :------: | :----: |
/// | 1           | `offset` |        |
/// | 2           | `size`   |        |
///
/// where:
///
/// - `offset` is the byte offset in memory where the return data is located
/// - `size` the number of bytes in the return data
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Return;

impl Opcode for Return {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands
        let offset = stack.pop()?;
        let size = stack.pop()?;

        // Construct the value and hold onto it
        let return_val = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::Return { offset, size },
        );
        vm.state()?.record_value(return_val);

        // Now end execution
        vm.kill_current_thread();

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        0
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "RETURN".into()
    }

    fn as_byte(&self) -> u8 {
        0xf3
    }
}

/// The `REVERT` opcode halts execution returning data specified at the `offset`
/// and `size` in memory. It reverts any state changes and returns any unused
/// gas.
///
/// This opcode exits the current context with a success.
///
/// # Semantics
///
/// | Stack Index | Input    | Output |
/// | :---------: | :------: | :----: |
/// | 1           | `offset` |        |
/// | 2           | `size`   |        |
///
/// where:
///
/// - `offset` is the byte offset in memory where the return data is located
/// - `size` the number of bytes in the return data
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Revert;

impl Opcode for Revert {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands
        let offset = stack.pop()?;
        let size = stack.pop()?;

        // Construct the value and hold onto it
        let return_val = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::Revert { offset, size },
        );
        vm.state()?.record_value(return_val);

        // Now end execution
        vm.kill_current_thread();

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        0
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "REVERT".into()
    }

    fn as_byte(&self) -> u8 {
        0xfd
    }
}

/// Not a true EVM opcode, this structure exists to help in maintaining the
/// correspondence between position in the instruction stream and the byte
/// offset in the bytecode.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Nop;

impl Opcode for Nop {
    fn execute(&self, _vm: &mut VM) -> ExecuteResult {
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        0
    }

    fn arg_count(&self) -> usize {
        0
    }

    fn as_text_code(&self) -> String {
        "NOP".into()
    }

    fn as_byte(&self) -> u8 {
        panic!("NOP cannot be converted into a byte")
    }

    fn encode(&self) -> Vec<u8> {
        vec![] // This operation takes up no space in the instruction stream.
    }
}

#[cfg(test)]
mod test {
    use crate::{
        error::execution,
        opcode::{control, macros::bytecode, test_util as util, Opcode},
        vm::{
            instructions::InstructionStream,
            value::{known_data::KnownData, Provenance, SymbolicValue, SymbolicValueData},
        },
    };

    #[test]
    fn stop_halts_execution_on_thread() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = control::Stop;
        opcode.execute(&mut vm)?;

        // Check that it has marked execution as needing to halt on the current thread
        assert!(vm.current_thread_killed());

        Ok(())
    }

    #[test]
    fn invalid_instruction_halts_execution_on_thread() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and run the opcode
        let opcode = control::Invalid;
        opcode.execute(&mut vm)?;

        // Check that it has marked execution as needing to halt on the current thread
        assert!(vm.current_thread_killed());

        Ok(())
    }

    #[test]
    fn valid_jump_continues_execution() -> anyhow::Result<()> {
        // Prepare the instruction stream, as it actually does matter this time
        let bytes: Vec<u8> = bytecode![
            control::Jump,
            control::Invalid,
            control::Invalid,
            control::JumpDest,
        ];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the VM
        let immediate = SymbolicValue::new_known_value(
            0,
            KnownData::Bytes { value: vec![0x03] }, // Offset of JUMPDEST in the bytes above
            Provenance::Synthetic,
        );
        let mut vm =
            util::new_vm_with_instructions_and_values_on_stack(instructions, vec![immediate])?;

        // Prepare and execute the opcode
        let opcode = control::Jump;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        assert!(vm.state()?.stack_mut().is_empty());

        // Inspect the execution position.
        assert_eq!(vm.execution_thread_mut()?.instruction_pointer(), 0x03);

        Ok(())
    }

    #[test]
    fn jump_without_concrete_immediate_halts_execution() -> anyhow::Result<()> {
        // Prepare the instruction stream, as it actually does matter this time
        let bytes: Vec<u8> = bytecode![
            control::Jump,
            control::Invalid,
            control::Invalid,
            control::JumpDest,
        ];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the VM
        let immediate = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let mut vm =
            util::new_vm_with_instructions_and_values_on_stack(instructions, vec![immediate])?;

        // Prepare and execute the opcode
        let opcode = control::Jump;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        assert!(vm.state()?.stack_mut().is_empty());

        // Inspect the execution position.
        assert_eq!(vm.execution_thread_mut()?.instruction_pointer(), 0x00);

        // Ensure that the current thread has been marked for death
        assert!(vm.current_thread_killed());

        Ok(())
    }

    #[test]
    fn jump_with_oob_target_halts_execution() -> anyhow::Result<()> {
        // Prepare the instruction stream, as it actually does matter this time
        let bytes: Vec<u8> = bytecode![
            control::Jump,
            control::Invalid,
            control::Invalid,
            control::JumpDest,
        ];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the VM
        let immediate = SymbolicValue::new_known_value(
            0,
            KnownData::Bytes { value: vec![0x04] }, // Out of bounds
            Provenance::Synthetic,
        );
        let mut vm =
            util::new_vm_with_instructions_and_values_on_stack(instructions, vec![immediate])?;

        // Prepare and execute the opcode
        let opcode = control::Jump;
        let result = opcode.execute(&mut vm);

        // Check that it errored
        assert!(result.is_err());
        let error = result.unwrap_err();
        assert_eq!(
            error.payload,
            execution::Error::NonExistentJumpTarget { offset: 0x04 }
        );

        Ok(())
    }

    #[test]
    fn jump_with_invalid_destination_halts_execution() -> anyhow::Result<()> {
        // Prepare the instruction stream, as it actually does matter this time
        let bytes: Vec<u8> = bytecode![
            control::Jump,
            control::Invalid,
            control::Invalid,
            control::Invalid,
        ];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the VM
        let immediate = SymbolicValue::new_known_value(
            0,
            KnownData::Bytes { value: vec![0x03] }, // The final INVALID in the bytes above
            Provenance::Synthetic,
        );
        let mut vm =
            util::new_vm_with_instructions_and_values_on_stack(instructions, vec![immediate])?;

        // Prepare and execute the opcode
        let opcode = control::Jump;
        let result = opcode.execute(&mut vm);

        // Check that it errored
        assert!(result.is_err());
        let error = result.unwrap_err();
        assert_eq!(
            error.payload,
            execution::Error::InvalidJumpTarget { offset: 0x03 }
        );

        Ok(())
    }

    #[test]
    fn valid_conditional_jump_continues_execution() -> anyhow::Result<()> {
        // Prepare the instruction stream, as it actually does matter this time
        let bytes: Vec<u8> = bytecode![control::Jump, control::PC, control::JumpDest, control::PC];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the VM
        let immediate = SymbolicValue::new_known_value(
            0,
            KnownData::Bytes { value: vec![0x02] }, // Offset of JUMPDEST in the bytes above
            Provenance::Synthetic,
        );
        let cond = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm = util::new_vm_with_instructions_and_values_on_stack(
            instructions,
            vec![cond.clone(), immediate],
        )?;

        // Ensure that we start with one thread
        assert_eq!(vm.remaining_thread_count(), 1);

        // Prepare and execute the opcode
        let opcode = control::JumpI;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        assert!(vm.state()?.stack_mut().is_empty());

        // Inspect the execution position.
        assert_eq!(vm.execution_thread_mut()?.instruction_pointer(), 0x00);

        // Check that there is an additional thread in the VM
        assert_eq!(vm.remaining_thread_count(), 2);

        // Check that the second thread's execution position is where it should be
        assert_eq!(
            vm.remaining_threads_mut()
                .back_mut()
                .expect("No threads remaining")
                .instructions_mut()
                .instruction_pointer(),
            0x02
        );

        // Check that we stored the condition in the auxiliary buffer
        assert_eq!(
            vm.state()?.recorded_values()[0].data,
            SymbolicValueData::Condition { value: cond }
        );

        Ok(())
    }

    #[test]
    fn conditional_jump_with_oob_target_halts_execution() -> anyhow::Result<()> {
        // Prepare the instruction stream, as it actually does matter this time
        let bytes: Vec<u8> = bytecode![control::Jump, control::PC, control::JumpDest, control::PC];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the VM
        let immediate = SymbolicValue::new_known_value(
            0,
            KnownData::Bytes { value: vec![0x04] }, // OOB target
            Provenance::Synthetic,
        );
        let cond = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm = util::new_vm_with_instructions_and_values_on_stack(
            instructions,
            vec![cond, immediate],
        )?;

        // Prepare and execute the opcode
        let opcode = control::Jump;
        let result = opcode.execute(&mut vm);

        // Check that it errored
        assert!(result.is_err());
        let error = result.unwrap_err();
        assert_eq!(
            error.payload,
            execution::Error::NonExistentJumpTarget { offset: 0x04 }
        );

        Ok(())
    }

    #[test]
    fn conditional_jump_with_invalid_destination_halts_execution() -> anyhow::Result<()> {
        // Prepare the instruction stream, as it actually does matter this time
        let bytes: Vec<u8> = bytecode![control::Jump, control::PC, control::Invalid, control::PC];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the VM
        let immediate = SymbolicValue::new_known_value(
            0,
            KnownData::Bytes { value: vec![0x02] }, // Invalid jump target
            Provenance::Synthetic,
        );
        let cond = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm = util::new_vm_with_instructions_and_values_on_stack(
            instructions,
            vec![cond, immediate],
        )?;

        // Prepare and execute the opcode
        let opcode = control::Jump;
        let result = opcode.execute(&mut vm);

        // Check that it errored
        assert!(result.is_err());
        let error = result.unwrap_err();
        assert_eq!(
            error.payload,
            execution::Error::InvalidJumpTarget { offset: 0x02 }
        );

        Ok(())
    }

    #[test]
    fn pc_pushes_value_onto_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;

        // Prepare and execute the opcode
        let opcode = control::PC;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let value = stack.read(0)?;
        match &value.data {
            SymbolicValueData::KnownData { value, .. } => {
                assert_eq!(
                    value,
                    &KnownData::UInt {
                        value: 0x00u32.to_le_bytes().to_vec(),
                    }
                )
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }

    #[test]
    fn jump_dest_does_nothing() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;
        let initial_state = vm.state()?.clone();

        // Prepare and execute the opcode
        let opcode = control::JumpDest;
        opcode.execute(&mut vm)?;

        // Check that no state has changed
        assert_eq!(vm.state()?, &initial_state);

        Ok(())
    }

    #[test]
    fn call_manipulates_stack_and_memory() -> anyhow::Result<()> {
        // Prepare the vm
        let input_gas = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_address = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_value = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_arg_offset = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_arg_size = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_ret_offset = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_ret_size = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_data = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![
            input_ret_size.clone(),
            input_ret_offset.clone(),
            input_arg_size.clone(),
            input_arg_offset.clone(),
            input_value.clone(),
            input_address.clone(),
            input_gas.clone(),
        ])?;
        vm.state()?
            .memory_mut()
            .store(input_arg_offset.clone(), input_data.clone());

        // Prepare and execute the opcode
        let opcode = control::Call;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let value = stack.read(0)?;
        assert_eq!(value.provenance, Provenance::Execution);
        match &value.data {
            SymbolicValueData::CallWithValue {
                gas,
                address,
                value,
                arg_size,
                ret_size,
            } => {
                assert_eq!(gas, &input_gas);
                assert_eq!(address, &input_address);
                assert_eq!(value, &input_value);
                assert_eq!(arg_size, &input_arg_size);
                assert_eq!(ret_size, &input_ret_size);
            }
            _ => panic!("Invalid payload"),
        }

        // Inspect the memory state
        let memory = vm.state()?.memory_mut();
        let return_value = memory.load(&input_ret_offset);
        assert_eq!(return_value.provenance, Provenance::MessageCall);
        let input_value = memory.load(&input_arg_offset);
        assert_eq!(input_value, &input_data);

        Ok(())
    }

    #[test]
    fn delegate_call_manipulates_stack_and_memory() -> anyhow::Result<()> {
        // Prepare the vm
        let input_gas = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_address = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_arg_offset = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_arg_size = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_ret_offset = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_ret_size = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_data = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![
            input_ret_size.clone(),
            input_ret_offset.clone(),
            input_arg_size.clone(),
            input_arg_offset.clone(),
            input_address.clone(),
            input_gas.clone(),
        ])?;
        vm.state()?
            .memory_mut()
            .store(input_arg_offset.clone(), input_data.clone());

        // Prepare and execute the opcode
        let opcode = control::DelegateCall;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let value = stack.read(0)?;
        assert_eq!(value.provenance, Provenance::Execution);
        match &value.data {
            SymbolicValueData::CallWithoutValue {
                gas,
                address,
                arg_size,
                ret_size,
            } => {
                assert_eq!(gas, &input_gas);
                assert_eq!(address, &input_address);
                assert_eq!(arg_size, &input_arg_size);
                assert_eq!(ret_size, &input_ret_size);
            }
            _ => panic!("Invalid payload"),
        }

        // Inspect the memory state
        let memory = vm.state()?.memory_mut();
        let return_value = memory.load(&input_ret_offset);
        assert_eq!(return_value.provenance, Provenance::MessageCall);
        let input_value = memory.load(&input_arg_offset);
        assert_eq!(input_value, &input_data);

        Ok(())
    }

    #[test]
    fn return_stores_data_and_ends_execution() -> anyhow::Result<()> {
        // Prepare the vm
        let input_offset = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_size = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_size.clone(), input_offset.clone()])?;

        // Prepare and run the opcode
        let opcode = control::Return;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        assert!(vm.state()?.stack_mut().is_empty());

        // Ensure the value was stored
        let value = &vm.state()?.recorded_values()[0];
        assert_eq!(value.provenance, Provenance::Execution);
        match &value.data {
            SymbolicValueData::Return { offset, size } => {
                assert_eq!(offset, &input_offset);
                assert_eq!(size, &input_size);
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }

    #[test]
    fn revert_stores_data_and_ends_execution() -> anyhow::Result<()> {
        // Prepare the vm
        let input_offset = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_size = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_size.clone(), input_offset.clone()])?;

        // Prepare and run the opcode
        let opcode = control::Revert;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        assert!(vm.state()?.stack_mut().is_empty());

        // Ensure the value was stored
        let value = &vm.state()?.recorded_values()[0];
        assert_eq!(value.provenance, Provenance::Execution);
        match &value.data {
            SymbolicValueData::Revert { offset, size } => {
                assert_eq!(offset, &input_offset);
                assert_eq!(size, &input_size);
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }

    #[test]
    fn nop_does_nothing() -> anyhow::Result<()> {
        // Prepare the vm
        let mut vm = util::new_vm_with_values_on_stack(vec![])?;
        let initial_state = vm.state()?.clone();

        // Prepare and execute the opcode
        let opcode = control::Nop;
        opcode.execute(&mut vm)?;

        // Check that no state has changed
        assert_eq!(vm.state()?, &initial_state);

        Ok(())
    }
}
