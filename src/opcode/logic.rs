//! Opcodes that deal with performing boolean logic on the EVM.

use crate::{
    opcode::{ExecuteResult, Opcode},
    vm::{
        value::{known::KnownWord, Provenance, SymbolicValue, SymbolicValueData},
        VM,
    },
};

/// The `LT` opcode performs a less-than comparison.
///
/// # Semantics
///
/// | Stack Index | Input | Output  |
/// | :---------: | :---: | :-----: |
/// | 1           | `a`   | `a < b` |
/// | 2           | `b`   |         |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Lt;

impl Opcode for Lt {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Construct the result and push it to the stack
        let result = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::LessThan { left: a, right: b },
        );
        stack.push(result)?;

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
        "LT".into()
    }

    fn as_byte(&self) -> u8 {
        0x10
    }
}

/// The `GT` opcode performs a greater-than comparison.
///
/// # Semantics
///
/// | Stack Index | Input | Output  |
/// | :---------: | :---: | :-----: |
/// | 1           | `a`   | `a > b` |
/// | 2           | `b`   |         |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Gt;

impl Opcode for Gt {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Construct the result and push it to the stack
        let result = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::GreaterThan { left: a, right: b },
        );
        stack.push(result)?;

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
        "GT".into()
    }

    fn as_byte(&self) -> u8 {
        0x11
    }
}

/// The `SLT` opcode performs a less-than comparison, treating both operands as
/// signed two's complement integers.
///
/// # Semantics
///
/// | Stack Index | Input | Output  |
/// | :---------: | :---: | :-----: |
/// | 1           | `a`   | `a < b` |
/// | 2           | `b`   |         |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SLt;

impl Opcode for SLt {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Construct the result and push it to the stack
        let result = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::SignedLessThan { left: a, right: b },
        );
        stack.push(result)?;

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
        "SLT".into()
    }

    fn as_byte(&self) -> u8 {
        0x12
    }
}

/// The `SGT` opcode performs a greater-than comparison, treating both operands
/// as signed two's complement integers.
///
/// # Semantics
///
/// | Stack Index | Input | Output  |
/// | :---------: | :---: | :-----: |
/// | 1           | `a`   | `a > b` |
/// | 2           | `b`   |         |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SGt;

impl Opcode for SGt {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Construct the result and push it to the stack
        let result = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::SignedGreaterThan { left: a, right: b },
        );
        stack.push(result)?;

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
        "SAR".into()
    }

    fn as_byte(&self) -> u8 {
        0x13
    }
}

/// The `EQ` opcode performs an equality comparison.
///
/// # Semantics
///
/// | Stack Index | Input | Output   |
/// | :---------: | :---: | :------: |
/// | 1           | `a`   | `a == b` |
/// | 2           | `b`   |          |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Eq;

impl Opcode for Eq {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Construct the result and push it to the stack
        let result = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::Equals { left: a, right: b },
        );
        stack.push(result)?;

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
        "EQ".into()
    }

    fn as_byte(&self) -> u8 {
        0x14
    }
}

/// The `ISZERO` opcode checks if its operand is zero.
///
/// # Semantics
///
/// | Stack Index | Input | Output   |
/// | :---------: | :---: | :------: |
/// | 1           | `a`   | `a == 0` |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct IsZero;

impl Opcode for IsZero {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let number = stack.pop()?;

        // Construct the result and push it to the stack
        let result = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::IsZero { number },
        );
        stack.push(result)?;

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
        "ISZERO".into()
    }

    fn as_byte(&self) -> u8 {
        0x15
    }
}

/// The `AND` opcode performs a bitwise conjunction of its operands.
///
/// # Semantics
///
/// | Stack Index | Input | Output  |
/// | :---------: | :---: | :-----: |
/// | 1           | `a`   | `a & b` |
/// | 2           | `b`   |         |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct And;

impl Opcode for And {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Construct the result and push it to the stack
        let result = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::And { left: a, right: b },
        );
        stack.push(result)?;

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
        "AND".into()
    }

    fn as_byte(&self) -> u8 {
        0x16
    }
}

/// The `OR` opcode performs a bitwise disjunction of its operands.
///
/// # Semantics
///
/// | Stack Index | Input | Output  |
/// | :---------: | :---: | :-----: |
/// | 1           | `a`   | `a | b` |
/// | 2           | `b`   |         |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Or;

impl Opcode for Or {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Construct the result and push it to the stack
        let result = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::Or { left: a, right: b },
        );
        stack.push(result)?;

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
        "OR".into()
    }

    fn as_byte(&self) -> u8 {
        0x17
    }
}

/// The `XOR` opcode performs a bitwise exclusive disjunction of its operands
///
/// # Semantics
///
/// | Stack Index | Input | Output  |
/// | :---------: | :---: | :-----: |
/// | 1           | `a`   | `a ^ b` |
/// | 2           | `b`   |         |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Xor;

impl Opcode for Xor {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Construct the result and push it to the stack
        let result = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::Xor { left: a, right: b },
        );
        stack.push(result)?;

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
        "XOR".into()
    }

    fn as_byte(&self) -> u8 {
        0x18
    }
}

/// The `NOT` opcode performs a bitwise negation of its operand
///
/// # Semantics
///
/// | Stack Index | Input | Output |
/// | :---------: | :---: | :----: |
/// | 1           | `a`   | `~a`   |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Not;

impl Opcode for Not {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let value = stack.pop()?;

        // Construct the result and push it to the stack
        let result = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::Not { value },
        );
        stack.push(result)?;

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
        "NOT".into()
    }

    fn as_byte(&self) -> u8 {
        0x19
    }
}

/// The `BYTE` opcode retrieves a single byte from a word.
///
/// # Semantics
///
/// | Stack Index | Input    | Output                                 |
/// | :---------: | :------: | :------------------------------------: |
/// | 1           | `offset` | `(value >> (248 - offset * 8)) & 0xFF` |
/// | 2           | `value`  |                                        |
///
/// where:
///
/// - `offset` is the byte offset in `value` to retrieve, starting from the most
///   significant byte
/// - `value` is the word-sized (32 byte) value
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Byte;

impl Opcode for Byte {
    #[allow(clippy::similar_names)] // They are accurate names
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and the env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands
        let offset = stack.pop()?;
        let value = stack.pop()?;

        // Construct the constants
        let const_0x08 = SymbolicValue::new_known_value(
            instruction_pointer,
            KnownWord::from(0x08u8.to_le_bytes().to_vec()),
            Provenance::Bytecode,
        );
        let const_0xf8 = SymbolicValue::new_known_value(
            instruction_pointer,
            KnownWord::from(0xf8u8.to_le_bytes().to_vec()),
            Provenance::Bytecode,
        );
        let const_0xff = SymbolicValue::new_known_value(
            instruction_pointer,
            KnownWord::from(0xffu8.to_le_bytes().to_vec()),
            Provenance::Bytecode,
        );

        // Construct the intermediates
        let offset_times_0x08 = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::Multiply {
                left:  offset,
                right: const_0x08,
            },
        );
        let shift = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::Subtract {
                left:  const_0xf8,
                right: offset_times_0x08,
            },
        );
        let shifted = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::RightShift { value, shift },
        );
        let result = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::And {
                left:  shifted,
                right: const_0xff,
            },
        );

        // Push the result onto the stack
        stack.push(result)?;

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
        "BYTE".into()
    }

    fn as_byte(&self) -> u8 {
        0x1a
    }
}

/// The `SHL` opcode performs a left shift (toward the MSB).
///
/// The bits moved after the 256th one are discarded, the new bits are set to 0.
///
/// # Semantics
///
/// | Stack Index | Input   | Output           |
/// | :---------: | :-----: | :--------------: |
/// | 1           | `shift` | `value << shift` |
/// | 2           | `value` |                  |
///
/// where:
///
/// - `shift` is the number of bits shifted to the left
/// - `value` the 32-byte value to shift
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Shl;

impl Opcode for Shl {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let shift = stack.pop()?;
        let value = stack.pop()?;

        // Construct the result and push it to the stack
        let result = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::LeftShift { shift, value },
        );
        stack.push(result)?;

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
        "SHL".into()
    }

    fn as_byte(&self) -> u8 {
        0x1b
    }
}

/// The `SHR` opcode performs a right shift (toward the LSB).
///
/// The bits moved before the first one are discarded, the new bits are set to
/// 0.
///
/// # Semantics
///
/// | Stack Index | Input   | Output           |
/// | :---------: | :-----: | :--------------: |
/// | 1           | `shift` | `value >> shift` |
/// | 2           | `value` |                  |
///
/// where:
///
/// - `shift` is the number of bits shifted to the right
/// - `value` the 32-byte value to shift
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Shr;

impl Opcode for Shr {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let shift = stack.pop()?;
        let value = stack.pop()?;

        // Construct the result and push it to the stack
        let result = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::RightShift { shift, value },
        );
        stack.push(result)?;

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
        "SHR".into()
    }

    fn as_byte(&self) -> u8 {
        0x1c
    }
}

/// The `SAR` opcode performs a signed (arithmetic) right shift (toward the
/// LSB).
///
/// The bits moved before the first one are discarded, the new bits are set to 0
/// if the previous most significant bit was 0, otherwise the new bits are set
/// to 1.
///
/// # Semantics
///
/// | Stack Index | Input   | Output           |
/// | :---------: | :-----: | :--------------: |
/// | 1           | `shift` | `value >> shift` |
/// | 2           | `value` |                  |
///
/// where:
///
/// - `shift` is the number of bits shifted to the right
/// - `value` the 32-byte value to shift
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Sar;

impl Opcode for Sar {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let shift = stack.pop()?;
        let value = stack.pop()?;

        // Construct the result and push it to the stack
        let result = SymbolicValue::new_from_execution(
            instruction_pointer,
            SymbolicValueData::ArithmeticRightShift { shift, value },
        );
        stack.push(result)?;

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
        "SAR".into()
    }

    fn as_byte(&self) -> u8 {
        0x1d
    }
}

#[cfg(test)]
mod test {
    use crate::{
        opcode::{logic, test_util as util, Opcode},
        vm::value::{known::KnownWord, Provenance, SymbolicValue, SymbolicValueData},
    };

    #[test]
    fn lt_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_left = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_right = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = logic::Lt;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance, Provenance::Execution);
        match &result.data {
            SymbolicValueData::LessThan { left, right } => {
                assert_eq!(left, &input_left);
                assert_eq!(right, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn gt_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_left = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_right = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = logic::Gt;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance, Provenance::Execution);
        match &result.data {
            SymbolicValueData::GreaterThan { left, right } => {
                assert_eq!(left, &input_left);
                assert_eq!(right, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn s_lt_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_left = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_right = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = logic::SLt;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance, Provenance::Execution);
        match &result.data {
            SymbolicValueData::SignedLessThan { left, right } => {
                assert_eq!(left, &input_left);
                assert_eq!(right, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn s_gt_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_left = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_right = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = logic::SGt;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance, Provenance::Execution);
        match &result.data {
            SymbolicValueData::SignedGreaterThan { left, right } => {
                assert_eq!(left, &input_left);
                assert_eq!(right, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn eq_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_left = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_right = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = logic::Eq;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance, Provenance::Execution);
        match &result.data {
            SymbolicValueData::Equals { left, right } => {
                assert_eq!(left, &input_left);
                assert_eq!(right, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn is_zero_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let operand = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![operand.clone()])?;

        // Prepare and run the opcode
        let opcode = logic::IsZero;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance, Provenance::Execution);
        match &result.data {
            SymbolicValueData::IsZero { number } => {
                assert_eq!(number, &operand);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn and_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_left = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_right = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = logic::And;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance, Provenance::Execution);
        match &result.data {
            SymbolicValueData::And { left, right } => {
                assert_eq!(left, &input_left);
                assert_eq!(right, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn or_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_left = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_right = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = logic::Or;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance, Provenance::Execution);
        match &result.data {
            SymbolicValueData::Or { left, right } => {
                assert_eq!(left, &input_left);
                assert_eq!(right, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn xor_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_left = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_right = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = logic::Xor;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance, Provenance::Execution);
        match &result.data {
            SymbolicValueData::Xor { left, right } => {
                assert_eq!(left, &input_left);
                assert_eq!(right, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn not_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let operand = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![operand.clone()])?;

        // Prepare and run the opcode
        let opcode = logic::Not;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance, Provenance::Execution);
        match &result.data {
            SymbolicValueData::Not { value } => {
                assert_eq!(value, &operand);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn byte_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_offset = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_value = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_value.clone(), input_offset.clone()])?;

        // Prepare and run the opcode
        let opcode = logic::Byte;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance, Provenance::Execution);

        // At the top level the value should be a logical conjunction
        match &result.data {
            SymbolicValueData::And { left, right } => {
                assert_eq!(left.provenance, Provenance::Execution);
                assert_eq!(right.provenance, Provenance::Bytecode);

                // The right operand should be a constant 0xff
                match &right.data {
                    SymbolicValueData::KnownData { value, .. } => {
                        assert_eq!(value, &KnownWord::from(0xffu8.to_le_bytes().to_vec(),));
                    }
                    _ => panic!("Invalid payload"),
                }

                // The left operand should be an unsigned right shift
                match &left.data {
                    SymbolicValueData::RightShift { value, shift } => {
                        assert_eq!(shift.provenance, Provenance::Execution);

                        // The value should come from the inputs
                        assert_eq!(value, &input_value);

                        // The shift size is computed
                        match &shift.data {
                            SymbolicValueData::Subtract { left, right } => {
                                assert_eq!(left.provenance, Provenance::Bytecode);
                                assert_eq!(right.provenance, Provenance::Execution);

                                // The left operand is a constant 0xf8
                                match &left.data {
                                    SymbolicValueData::KnownData { value, .. } => {
                                        assert_eq!(
                                            value,
                                            &KnownWord::from(0xf8u8.to_le_bytes().to_vec(),)
                                        );
                                    }
                                    _ => panic!("Invalid payload"),
                                }

                                // The right operand is computed
                                match &right.data {
                                    SymbolicValueData::Multiply { left, right } => {
                                        assert_eq!(right.provenance, Provenance::Bytecode);

                                        // The left is the input offset
                                        assert_eq!(left, &input_offset);

                                        // The right is a constant 0x08
                                        match &right.data {
                                            SymbolicValueData::KnownData { value, .. } => {
                                                assert_eq!(
                                                    value,
                                                    &KnownWord::from(0x08u8.to_le_bytes().to_vec())
                                                );
                                            }
                                            _ => panic!("Invalid payload"),
                                        }
                                    }
                                    _ => panic!("Invalid payload"),
                                }
                            }
                            _ => panic!("Invalid payload"),
                        }
                    }
                    _ => panic!("Invalid payload"),
                }
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }

    #[test]
    fn shl_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_left = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_right = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = logic::Shl;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance, Provenance::Execution);
        match &result.data {
            SymbolicValueData::LeftShift { shift, value } => {
                assert_eq!(shift, &input_left);
                assert_eq!(value, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn shr_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_left = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_right = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = logic::Shr;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance, Provenance::Execution);
        match &result.data {
            SymbolicValueData::RightShift { shift, value } => {
                assert_eq!(shift, &input_left);
                assert_eq!(value, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn sar_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the vm
        let input_left = SymbolicValue::new_synthetic(0, SymbolicValueData::new_value());
        let input_right = SymbolicValue::new_synthetic(1, SymbolicValueData::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = logic::Sar;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let result = stack.read(0)?;
        assert_eq!(result.provenance, Provenance::Execution);
        match &result.data {
            SymbolicValueData::ArithmeticRightShift { shift, value } => {
                assert_eq!(shift, &input_left);
                assert_eq!(value, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }
}
