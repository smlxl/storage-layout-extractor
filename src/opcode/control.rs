//! Opcodes that perform control(-flow) operations on the EVM.

use crate::{
    error::{container::Locatable, execution, execution::Error},
    opcode::{util, ExecuteResult, Opcode},
    vm::{
        value::{known::KnownWord, Provenance, RuntimeBoxedVal, RSVD},
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
pub struct Invalid {
    pub byte: u8,
}

impl Invalid {
    /// Creates a new invalid wrapping the specified byte.
    #[must_use]
    pub fn new(byte: u8) -> Self {
        Self { byte }
    }
}

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
        self.byte
    }
}

impl Default for Invalid {
    /// The default invalid opcode is the one that has a byte corresponding to
    /// the one specified by the EVM.
    fn default() -> Self {
        Self::new(0xfe)
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
                    Error::NoConcreteJumpDestination => {
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
        let instruction_pointer = vm.instruction_pointer()?;
        let counter = vm.stack_handle()?.pop()?;
        let condition = vm.stack_handle()?.pop()?;

        // We want to store that the condition existed, even if the jump target is
        // invalid, so we record it in the buffer of otherwise-lost values
        vm.state()?.record_value(condition);

        // In `solc` compiled code, the top of the stack at jump time is a non-computed
        // immediate, allowing us to actually alter the program counter
        match util::validate_jump_destination(&counter, vm) {
            Ok(target) => {
                // We only want to fork up to the provided limit, so we check if we can first
                if vm.jump_targets_mut().fork_to(instruction_pointer, target)? {
                    // If we do have a valid jump target, we need to fork off an execution thread so
                    // that both branches can be executed. Note that the `VM` will step from the
                    // target, but as it is a JUMPDEST no-op this is fine.
                    vm.fork_current_thread(target)?;
                }

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
                    execution::Error::NoConcreteJumpDestination { .. }
                    | execution::Error::NonExistentJumpTarget { .. }
                    | execution::Error::InvalidJumpTarget { .. }
                    | execution::Error::InvalidOffsetForJump { .. } => Ok(payload),
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
        // Get the instruction pointer
        let instruction_pointer = vm.instruction_pointer()?;

        // Construct the value and push it onto the stack
        let result = vm.build().known(
            instruction_pointer,
            KnownWord::from_le(instruction_pointer),
            Provenance::ProgramCounter,
        );
        let mut stack = vm.stack_handle()?;
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

/// Stores the return data from an external message call for `ret_size` at
/// `ret_offset`.
fn store_return_data(
    ret_size: &RuntimeBoxedVal,
    ret_offset: &RuntimeBoxedVal,
    vm: &mut VM,
) -> ExecuteResult {
    let instruction_pointer = vm.instruction_pointer()?;
    let ret_size = ret_size.constant_fold();

    if let RSVD::KnownData { value } = ret_size.data() {
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
                    left:  ret_offset.constant_fold(),
                    right: to_add_to_offset,
                },
            );
            // Offsets in the _return data_ start at zero.
            let src_offset = vm
                .build()
                .known_exec(instruction_pointer, KnownWord::from(internal_offset));
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
        let ret_value = vm.build().symbolic(
            instruction_pointer,
            RSVD::new_value(),
            Provenance::MessageCall,
        );
        vm.state()?.memory_mut().store(ret_offset.clone(), ret_value);
    }

    Ok(())
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

        // Read the input data out of memory
        let argument_data =
            vm.state()?
                .memory_mut()
                .load_slice(&arg_offset, &arg_size, instruction_pointer);

        // Create the return value and store it in memory
        store_return_data(&ret_size, &ret_offset, vm)?;

        // Create the value representing the call
        let call_return = vm.build().symbolic_exec(
            instruction_pointer,
            RSVD::CallWithValue {
                gas,
                address,
                value,
                argument_data,
                ret_offset,
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

        // Read the input data out of memory
        let argument_data =
            vm.state()?
                .memory_mut()
                .load_slice(&arg_offset, &arg_size, instruction_pointer);

        // Create the return value and store it in memory
        store_return_data(&ret_size, &ret_offset, vm)?;

        // Create the value representing the call
        let call_return = vm.build().symbolic_exec(
            instruction_pointer,
            RSVD::CallWithoutValue {
                gas,
                address,
                argument_data,
                ret_offset,
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
        let data = vm
            .state()?
            .memory_mut()
            .load_slice(&offset, &size, instruction_pointer);
        let return_val = vm.build().symbolic_exec(instruction_pointer, RSVD::Return { data });
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
        let data = vm
            .state()?
            .memory_mut()
            .load_slice(&offset, &size, instruction_pointer);
        let return_val = vm.build().symbolic_exec(instruction_pointer, RSVD::Revert { data });
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
        disassembly::InstructionStream,
        error::execution,
        opcode::{control, macros::bytecode, test_util as util, Opcode},
        vm::value::{known::KnownWord, Provenance, RSV, RSVD},
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
        let opcode = control::Invalid::default();
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
            control::Invalid::default(),
            control::Invalid::default(),
            control::JumpDest,
        ];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the VM
        let immediate = RSV::new_known_value(
            0,
            KnownWord::from_le(0x03u32), // Offset of JUMPDEST in the bytes above
            Provenance::Synthetic,
            None,
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
            control::Invalid::default(),
            control::Invalid::default(),
            control::JumpDest,
        ];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the VM
        let immediate = RSV::new_synthetic(0, RSVD::new_value());
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
            control::Invalid::default(),
            control::Invalid::default(),
            control::JumpDest,
        ];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the VM
        let immediate = RSV::new_known_value(
            0,
            KnownWord::from_le(0x04u32), // Out of bounds
            Provenance::Synthetic,
            None,
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
            control::Invalid::default(),
            control::Invalid::default(),
            control::Invalid::default(),
        ];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the VM
        let immediate = RSV::new_known_value(
            0,
            KnownWord::from_le(0x03u32), // The final INVALID in the bytes above
            Provenance::Synthetic,
            None,
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
        let bytes: Vec<u8> = bytecode![control::JumpI, control::PC, control::JumpDest, control::PC];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the VM
        let immediate = RSV::new_known_value(
            0,
            KnownWord::from_le(0x02u32), // Offset of JUMPDEST in the bytes above
            Provenance::Synthetic,
            None,
        );
        let cond = RSV::new_synthetic(1, RSVD::new_value());
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
        assert_eq!(vm.state()?.recorded_values()[0], cond);

        Ok(())
    }

    #[test]
    fn conditional_jump_with_oob_target_halts_execution() -> anyhow::Result<()> {
        // Prepare the instruction stream, as it actually does matter this time
        let bytes: Vec<u8> = bytecode![control::Jump, control::PC, control::JumpDest, control::PC];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the VM
        let immediate = RSV::new_known_value(
            0,
            KnownWord::from_le(0x04u32), // OOB target
            Provenance::Synthetic,
            None,
        );
        let cond = RSV::new_synthetic(1, RSVD::new_value());
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
        let bytes: Vec<u8> = bytecode![
            control::Jump,
            control::PC,
            control::Invalid::default(),
            control::PC
        ];
        let instructions = InstructionStream::try_from(bytes.as_slice())?;

        // Prepare the VM
        let immediate = RSV::new_known_value(
            0,
            KnownWord::from_le(0x02u32), // Invalid jump target
            Provenance::Synthetic,
            None,
        );
        let cond = RSV::new_synthetic(1, RSVD::new_value());
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
        match value.data() {
            RSVD::KnownData { value, .. } => {
                assert_eq!(value, &KnownWord::from_le(0x00u32));
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
        let input_gas = RSV::new_synthetic(0, RSVD::new_value());
        let input_address = RSV::new_synthetic(0, RSVD::new_value());
        let input_value = RSV::new_synthetic(0, RSVD::new_value());
        let input_arg_offset = RSV::new_synthetic(0, RSVD::new_value());
        let input_arg_size = RSV::new_synthetic(0, RSVD::new_value());
        let input_ret_offset = RSV::new_synthetic(0, RSVD::new_value());
        let input_ret_size = RSV::new_synthetic(0, RSVD::new_value());
        let input_data = RSV::new_synthetic(0, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![
            input_ret_size.clone(),
            input_ret_offset.clone(),
            input_arg_size,
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
        assert_eq!(value.provenance(), Provenance::Execution);
        match value.data() {
            RSVD::CallWithValue {
                gas,
                address,
                value,
                argument_data,
                ret_offset,
                ret_size,
            } => {
                assert_eq!(gas, &input_gas);
                assert_eq!(address, &input_address);
                assert_eq!(value, &input_value);
                assert_eq!(argument_data, &input_data);
                assert_eq!(ret_offset, &input_ret_offset);
                assert_eq!(ret_size, &input_ret_size);
            }
            _ => panic!("Invalid payload"),
        }

        // Inspect the memory state
        let memory = vm.state()?.memory_mut();
        let return_value = memory.load(&input_ret_offset);
        assert_eq!(return_value.provenance(), Provenance::MessageCall);
        let input_value = memory.load(&input_arg_offset);
        assert_eq!(input_value, input_data);

        Ok(())
    }

    #[test]
    fn delegate_call_manipulates_stack_and_memory() -> anyhow::Result<()> {
        // Prepare the vm
        let input_gas = RSV::new_synthetic(0, RSVD::new_value());
        let input_address = RSV::new_synthetic(0, RSVD::new_value());
        let input_arg_offset = RSV::new_synthetic(0, RSVD::new_value());
        let input_arg_size = RSV::new_synthetic(0, RSVD::new_value());
        let input_ret_offset = RSV::new_synthetic(0, RSVD::new_value());
        let input_ret_size = RSV::new_synthetic(0, RSVD::new_value());
        let input_data = RSV::new_synthetic(0, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![
            input_ret_size.clone(),
            input_ret_offset.clone(),
            input_arg_size,
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
        assert_eq!(value.provenance(), Provenance::Execution);
        match value.data() {
            RSVD::CallWithoutValue {
                gas,
                address,
                argument_data,
                ret_offset,
                ret_size,
            } => {
                assert_eq!(gas, &input_gas);
                assert_eq!(address, &input_address);
                assert_eq!(argument_data, &input_data);
                assert_eq!(ret_offset, &input_ret_offset);
                assert_eq!(ret_size, &input_ret_size);
            }
            _ => panic!("Invalid payload"),
        }

        // Inspect the memory state
        let memory = vm.state()?.memory_mut();
        let return_value = memory.load(&input_ret_offset);
        assert_eq!(return_value.provenance(), Provenance::MessageCall);
        let input_value = memory.load(&input_arg_offset);
        assert_eq!(input_value, input_data);

        Ok(())
    }

    #[test]
    fn return_stores_data_and_ends_execution() -> anyhow::Result<()> {
        // Prepare the vm
        let input_offset = RSV::new_synthetic(0, RSVD::new_value());
        let input_size = RSV::new_synthetic(1, RSVD::new_value());
        let revert_data = RSV::new_synthetic(2, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![input_size, input_offset.clone()])?;
        vm.state()?.memory_mut().store(input_offset, revert_data.clone());

        // Prepare and run the opcode
        let opcode = control::Return;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        assert!(vm.state()?.stack_mut().is_empty());

        // Ensure the value was stored
        let value = &vm.state()?.recorded_values()[0];
        assert_eq!(value.provenance(), Provenance::Execution);
        match value.data() {
            RSVD::Return { data } => {
                assert_eq!(data, &revert_data);
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }

    #[test]
    fn revert_stores_data_and_ends_execution() -> anyhow::Result<()> {
        // Prepare the vm
        let input_offset = RSV::new_synthetic(0, RSVD::new_value());
        let input_size = RSV::new_synthetic(1, RSVD::new_value());
        let revert_data = RSV::new_synthetic(2, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![input_size, input_offset.clone()])?;
        vm.state()?.memory_mut().store(input_offset, revert_data.clone());

        // Prepare and run the opcode
        let opcode = control::Revert;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        assert!(vm.state()?.stack_mut().is_empty());

        // Ensure the value was stored
        let value = &vm.state()?.recorded_values()[0];
        assert_eq!(value.provenance(), Provenance::Execution);
        match value.data() {
            RSVD::Revert { data } => {
                assert_eq!(data, &revert_data);
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
