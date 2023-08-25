//! Opcodes that perform arithmetic operations on the EVM.

use crate::{
    opcode::{ExecuteResult, Opcode},
    vm::{value::RSVD, VM},
};

/// The `ADD` opcode performs addition.
///
/// # Semantics
///
/// | Stack Index | Input | Output             |
/// | :---------: | :---: | :----------------: |
/// | 1           | `a`   | `(a + b) % 2**256` |
/// | 2           | `b`   |                    |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Add;

impl Opcode for Add {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Create the new value
        let result = vm
            .build()
            .symbolic_exec(instruction_pointer, RSVD::Add { left: a, right: b });

        // Push it onto the stack
        let mut stack = vm.stack_handle()?;
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
        "ADD".into()
    }

    fn as_byte(&self) -> u8 {
        0x01
    }
}

/// The `MUL` opcode performs multiplication.
///
/// # Semantics
///
/// | Stack Index | Input | Output             |
/// | :---------: | :---: | :----------------: |
/// | 1           | `a`   | `(a * b) % 2**256` |
/// | 2           | `b`   |                    |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Mul;

impl Opcode for Mul {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Create the new value
        let result = vm
            .build()
            .symbolic_exec(instruction_pointer, RSVD::Multiply { left: a, right: b });

        // Push it onto the stack
        let mut stack = vm.stack_handle()?;
        stack.push(result)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        5
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "MUL".into()
    }

    fn as_byte(&self) -> u8 {
        0x02
    }
}

/// The `SUB` opcode performs subtraction.
///
/// # Semantics
///
/// | Stack Index | Input | Output             |
/// | :---------: | :---: | :----------------: |
/// | 1           | `a`   | `(a - b) % 2**256` |
/// | 2           | `b`   |                    |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Sub;

impl Opcode for Sub {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Create the new value
        let result = vm
            .build()
            .symbolic_exec(instruction_pointer, RSVD::Subtract { left: a, right: b });

        // Push it onto the stack
        let mut stack = vm.stack_handle()?;
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
        "SUB".into()
    }

    fn as_byte(&self) -> u8 {
        0x03
    }
}

/// The `DIV` opcode performs integer division.
///
/// # Semantics
///
/// | Stack Index | Input | Output                           |
/// | :---------: | :---: | :------------------------------: |
/// | 1           | `a`   | `if b == 0 then 0 else (a // b)` |
/// | 2           | `b`   |                                  |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Div;

impl Opcode for Div {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Create the new value
        let result = vm.build().symbolic_exec(
            instruction_pointer,
            RSVD::Divide {
                dividend: a,
                divisor:  b,
            },
        );

        // Push it onto the stack
        let mut stack = vm.stack_handle()?;
        stack.push(result)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        5
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "DIV".into()
    }

    fn as_byte(&self) -> u8 {
        0x04
    }
}

/// The `SDIV` opcode performs signed integer division.
///
/// Both operands and the result are treated as two's complement signed 256-bit
/// integers.
///
/// # Semantics
///
/// | Stack Index | Input | Output                           |
/// | :---------: | :---: | :------------------------------: |
/// | 1           | `a`   | `if b == 0 then 0 else (a // b)` |
/// | 2           | `b`   |                                  |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SDiv;

impl Opcode for SDiv {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Create the new value
        let result = vm.build().symbolic_exec(
            instruction_pointer,
            RSVD::SignedDivide {
                dividend: a,
                divisor:  b,
            },
        );

        // Push it onto the stack
        let mut stack = vm.stack_handle()?;
        stack.push(result)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        5
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "SDIV".into()
    }

    fn as_byte(&self) -> u8 {
        0x05
    }
}

/// The `MOD` opcode performs integer modulo.
///
/// # Semantics
///
/// | Stack Index | Input | Output                          |
/// | :---------: | :---: | :-----------------------------: |
/// | 1           | `a`   | `if b == 0 then 0 else (a % b)` |
/// | 2           | `b`   |                                 |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Mod;

impl Opcode for Mod {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Create the new value
        let result = vm.build().symbolic_exec(
            instruction_pointer,
            RSVD::Modulo {
                dividend: a,
                divisor:  b,
            },
        );

        // Push it onto the stack
        let mut stack = vm.stack_handle()?;
        stack.push(result)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        5
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "MOD".into()
    }

    fn as_byte(&self) -> u8 {
        0x06
    }
}

/// The `SMOD` opcode performs signed integer modulo.
///
/// Both operands and the result are treated as two's complement signed 256-bit
/// integers.
///
/// # Semantics
///
/// | Stack Index | Input | Output                          |
/// | :---------: | :---: | :-----------------------------: |
/// | 1           | `a`   | `if b == 0 then 0 else (a % b)` |
/// | 2           | `b`   |                                 |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SMod;

impl Opcode for SMod {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Create the new value
        let result = vm.build().symbolic_exec(
            instruction_pointer,
            RSVD::SignedModulo {
                dividend: a,
                divisor:  b,
            },
        );

        // Push it onto the stack
        let mut stack = vm.stack_handle()?;
        stack.push(result)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        5
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "SMOD".into()
    }

    fn as_byte(&self) -> u8 {
        0x07
    }
}

/// The `ADDMOD` opcode performs addition followed by modulo.
///
/// # Note
///
/// All intermediate values of this calculation **are not** computed modulo
/// 2**256.
///
/// # Semantics
///
/// | Stack Index | Input | Output                              |
/// | :---------: | :---: | :---------------------------------: |
/// | 1           | `a`   | `if N == 0 then 0 else (a + b) % N` |
/// | 2           | `b`   |                                     |
/// | 3           | `N`   |                                     |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct AddMod;

impl Opcode for AddMod {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;
        let n = stack.pop()?;

        // As they are semantically equivalent for the purposes of symbolic
        // execution, we simplify this into nested add and mod.
        let add = vm
            .build()
            .symbolic_exec(instruction_pointer, RSVD::Add { left: a, right: b });
        let modulo = vm.build().symbolic_exec(
            instruction_pointer,
            RSVD::Modulo {
                dividend: add,
                divisor:  n,
            },
        );

        // The result gets pushed onto the stack
        let mut stack = vm.stack_handle()?;
        stack.push(modulo)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        8
    }

    fn arg_count(&self) -> usize {
        3
    }

    fn as_text_code(&self) -> String {
        "ADDMOD".into()
    }

    fn as_byte(&self) -> u8 {
        0x08
    }
}

/// The `MULMOD` opcode performs multiplication followed by modulo.
///
/// # Note
///
/// All intermediate values of this calculation **are not** computed modulo
/// 2**256.
///
/// # Semantics
///
/// | Stack Index | Input | Output                              |
/// | :---------: | :---: | :---------------------------------: |
/// | 1           | `a`   | `if N == 0 then 0 else (a * b) % N` |
/// | 2           | `b`   |                                     |
/// | 3           | `N`   |                                     |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MulMod;

impl Opcode for MulMod {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;
        let n = stack.pop()?;

        // As they are semantically equivalent for the purposes of symbolic
        // execution, we simplify this into nested mul and mod.
        let mul = vm
            .build()
            .symbolic_exec(instruction_pointer, RSVD::Multiply { left: a, right: b });
        let modulo = vm.build().symbolic_exec(
            instruction_pointer,
            RSVD::Modulo {
                dividend: mul,
                divisor:  n,
            },
        );

        // The result gets pushed onto the stack
        let mut stack = vm.stack_handle()?;
        stack.push(modulo)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        8
    }

    fn arg_count(&self) -> usize {
        3
    }

    fn as_text_code(&self) -> String {
        "MULMOD".into()
    }

    fn as_byte(&self) -> u8 {
        0x09
    }
}

/// The `EXP` opcode performs exponentiation.
///
/// # Semantics
///
/// | Stack Index | Input | Output              |
/// | :---------: | :---: | :-----------------: |
/// | 1           | `a`   | `(a ** b) % 2**256` |
/// | 2           | `b`   |                     |
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Exp;

impl Opcode for Exp {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let b = stack.pop()?;

        // Create the new value
        let result = vm.build().symbolic_exec(
            instruction_pointer,
            RSVD::Exp {
                value:    a,
                exponent: b,
            },
        );

        // Push it onto the stack
        let mut stack = vm.stack_handle()?;
        stack.push(result)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        10
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "EXP".into()
    }

    fn as_byte(&self) -> u8 {
        0x0a
    }
}

/// The `SIGNEXTEND` opcode extends the length of a two's complement signed
/// integer.
///
/// # Semantics
///
/// | Stack Index | Input | Output             |
/// | :---------: | :---: | :----------------: |
/// | 1           | `a`   | `SIGNEXTEND(a, x)` |
/// | 2           | `x`   |                    |
///
/// where:
/// - `x` is the integer value to sign extend
/// - `a` is the size in bytes - 1 of the integer to sign extend
///
/// # Errors
///
/// Execution is reverted if there is not enough gas or if there are not enough
/// operands on the stack.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SignExtend;

impl Opcode for SignExtend {
    fn execute(&self, vm: &mut VM) -> ExecuteResult {
        // Get the stack and env data
        let instruction_pointer = vm.instruction_pointer()?;
        let mut stack = vm.stack_handle()?;

        // Get the operands from the stack
        let a = stack.pop()?;
        let x = stack.pop()?;

        // Create the new value
        let result = vm
            .build()
            .symbolic_exec(instruction_pointer, RSVD::SignExtend { value: a, size: x });

        // Push it onto the stack
        let mut stack = vm.stack_handle()?;
        stack.push(result)?;

        // Done, so return ok
        Ok(())
    }

    fn min_gas_cost(&self) -> usize {
        5
    }

    fn arg_count(&self) -> usize {
        2
    }

    fn as_text_code(&self) -> String {
        "SIGNEXTEND".into()
    }

    fn as_byte(&self) -> u8 {
        0x0b
    }
}

#[cfg(test)]
mod test {
    use crate::{
        opcode::{arithmetic, test_util as util, Opcode},
        vm::value::{Provenance, RSV, RSVD},
    };

    #[test]
    fn add_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the stack and vm
        let input_left = RSV::new_synthetic(0, RSVD::new_value());
        let input_right = RSV::new_synthetic(1, RSVD::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = arithmetic::Add;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let item = stack.read(0)?;
        assert_eq!(item.provenance(), Provenance::Execution);
        match item.data() {
            RSVD::Add { left, right } => {
                assert_eq!(left, &input_left);
                assert_eq!(right, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn mul_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the stack and vm
        let input_left = RSV::new_synthetic(0, RSVD::new_value());
        let input_right = RSV::new_synthetic(1, RSVD::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = arithmetic::Mul;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let item = stack.read(0)?;
        assert_eq!(item.provenance(), Provenance::Execution);
        match item.data() {
            RSVD::Multiply { left, right } => {
                assert_eq!(left, &input_left);
                assert_eq!(right, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn sub_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the stack and vm
        let input_left = RSV::new_synthetic(0, RSVD::new_value());
        let input_right = RSV::new_synthetic(1, RSVD::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = arithmetic::Sub;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let item = stack.read(0)?;
        assert_eq!(item.provenance(), Provenance::Execution);
        match item.data() {
            RSVD::Subtract { left, right } => {
                assert_eq!(left, &input_left);
                assert_eq!(right, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn div_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the stack and vm
        let input_left = RSV::new_synthetic(0, RSVD::new_value());
        let input_right = RSV::new_synthetic(1, RSVD::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = arithmetic::Div;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let item = stack.read(0)?;
        assert_eq!(item.provenance(), Provenance::Execution);
        match item.data() {
            RSVD::Divide { dividend, divisor } => {
                assert_eq!(dividend, &input_left);
                assert_eq!(divisor, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn s_div_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the stack and vm
        let input_left = RSV::new_synthetic(0, RSVD::new_value());
        let input_right = RSV::new_synthetic(1, RSVD::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = arithmetic::SDiv;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let item = stack.read(0)?;
        assert_eq!(item.provenance(), Provenance::Execution);
        match item.data() {
            RSVD::SignedDivide { dividend, divisor } => {
                assert_eq!(dividend, &input_left);
                assert_eq!(divisor, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn mod_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the stack and vm
        let input_left = RSV::new_synthetic(0, RSVD::new_value());
        let input_right = RSV::new_synthetic(1, RSVD::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = arithmetic::Mod;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let item = stack.read(0)?;
        assert_eq!(item.provenance(), Provenance::Execution);
        match item.data() {
            RSVD::Modulo { dividend, divisor } => {
                assert_eq!(dividend, &input_left);
                assert_eq!(divisor, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn s_mod_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the stack and vm
        let input_left = RSV::new_synthetic(0, RSVD::new_value());
        let input_right = RSV::new_synthetic(1, RSVD::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = arithmetic::SMod;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let item = stack.read(0)?;
        assert_eq!(item.provenance(), Provenance::Execution);
        match item.data() {
            RSVD::SignedModulo { dividend, divisor } => {
                assert_eq!(dividend, &input_left);
                assert_eq!(divisor, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn add_mod_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the stack and vm
        let input_left = RSV::new_synthetic(0, RSVD::new_value());
        let input_right = RSV::new_synthetic(1, RSVD::new_value());
        let input_n = RSV::new_synthetic(2, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![
            input_n.clone(),
            input_right.clone(),
            input_left.clone(),
        ])?;

        // Prepare and run the opcode
        let opcode = arithmetic::AddMod;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let item = stack.read(0)?;
        assert_eq!(item.provenance(), Provenance::Execution);
        match item.data() {
            RSVD::Modulo { dividend, divisor } => {
                assert_eq!(divisor, &input_n);
                assert_eq!(dividend.provenance(), Provenance::Execution);
                match dividend.data() {
                    RSVD::Add { left, right } => {
                        assert_eq!(left, &input_left);
                        assert_eq!(right, &input_right);
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn mul_mod_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the stack and vm
        let input_left = RSV::new_synthetic(0, RSVD::new_value());
        let input_right = RSV::new_synthetic(1, RSVD::new_value());
        let input_n = RSV::new_synthetic(2, RSVD::new_value());
        let mut vm = util::new_vm_with_values_on_stack(vec![
            input_n.clone(),
            input_right.clone(),
            input_left.clone(),
        ])?;

        // Prepare and run the opcode
        let opcode = arithmetic::MulMod;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let item = stack.read(0)?;
        assert_eq!(item.provenance(), Provenance::Execution);
        match item.data() {
            RSVD::Modulo { dividend, divisor } => {
                assert_eq!(divisor, &input_n);
                assert_eq!(dividend.provenance(), Provenance::Execution);
                match dividend.data() {
                    RSVD::Multiply { left, right } => {
                        assert_eq!(left, &input_left);
                        assert_eq!(right, &input_right);
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn exp_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the stack and vm
        let input_left = RSV::new_synthetic(0, RSVD::new_value());
        let input_right = RSV::new_synthetic(1, RSVD::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = arithmetic::Exp;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let item = stack.read(0)?;
        assert_eq!(item.provenance(), Provenance::Execution);
        match item.data() {
            RSVD::Exp { value, exponent } => {
                assert_eq!(value, &input_left);
                assert_eq!(exponent, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn sign_extend_manipulates_stack() -> anyhow::Result<()> {
        // Prepare the stack and vm
        let input_left = RSV::new_synthetic(0, RSVD::new_value());
        let input_right = RSV::new_synthetic(1, RSVD::new_value());
        let mut vm =
            util::new_vm_with_values_on_stack(vec![input_right.clone(), input_left.clone()])?;

        // Prepare and run the opcode
        let opcode = arithmetic::SignExtend;
        opcode.execute(&mut vm)?;

        // Inspect the stack
        let stack = vm.state()?.stack_mut();
        assert_eq!(stack.depth(), 1);
        let item = stack.read(0)?;
        assert_eq!(item.provenance(), Provenance::Execution);
        match item.data() {
            RSVD::SignExtend { value, size } => {
                assert_eq!(value, &input_left);
                assert_eq!(size, &input_right);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }
}
