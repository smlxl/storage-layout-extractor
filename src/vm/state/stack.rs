//! This module contains the implementation of the symbolic virtual machine's
//! stack.

use crate::{constant::MAXIMUM_STACK_DEPTH, error::VMError, vm::value::BoxedVal};

/// The representation of the symbolic virtual machine's stack.
///
/// # Indexing
///
/// Indexing into this stack is zero-based, where frame 0 is the top stack
/// frame.
///
/// # Depth
///
/// In a true EVM, it is a depth [`MAXIMUM_STACK_DEPTH`] stack, where each item
/// is word (256-bit) sized. Here, the symbolic virtual machine maintains the
/// same maximum depth, but instead stores [`crate::vm::value::SymbolicValue`]s
/// instead of words.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Stack {
    data: Vec<BoxedVal>,
}

impl Stack {
    /// Creates a new stack without any items on it.
    pub fn new() -> Self {
        let data = Vec::with_capacity(MAXIMUM_STACK_DEPTH);
        Self { data }
    }

    /// Pushes the provided value onto the top of the stack.
    ///
    /// # Errors
    ///
    /// If the stack cannot grow to accommodate the requested `data`.
    pub fn push(&mut self, data: BoxedVal) -> anyhow::Result<()> {
        if self.data.len() + 1 > MAXIMUM_STACK_DEPTH {
            return Err(VMError::StackDepthExceeded {
                requested: self.data.len() + 1,
            }
            .into());
        }
        self.data.push(data);
        Ok(())
    }

    /// Pops the top value from the stack.
    ///
    /// # Errors
    ///
    /// If the stack has no item to pop.
    pub fn pop(&mut self) -> anyhow::Result<BoxedVal> {
        self.data.pop().ok_or(VMError::NoSuchStackFrame { depth: 0 }.into())
    }

    /// Reads from the stack frame at the provided `depth`.
    ///
    /// # Errors
    ///
    /// If `depth` does not exist in the stack.
    pub fn read(&self, depth: u16) -> anyhow::Result<&BoxedVal> {
        self.check_frame_at(depth)?;

        // This is a safe unsigned subtraction as `check_frame_at will have returned
        // error if `depth` exceeds the current size.
        let index = self.top_frame_index()? - depth as usize;

        // This is safe as `check_frame_at` will have returned if no such stack depth
        // can be found.
        Ok(&self.data[index])
    }

    /// Duplicates the stack item at `frame` onto the top of the stack.
    ///
    /// This is a more general case of the `DUP` opcodes as it can duplicate any
    /// available stack frame.
    ///
    /// # Errors
    ///
    /// If `frame` doesn't exist.
    pub fn dup(&mut self, frame: u16) -> anyhow::Result<()> {
        self.check_frame_at(frame)?;
        let index = self.top_frame_index()? - frame as usize;

        // This is safe as the access is guarded by `check_frame_at`.
        let value = self.data[index].clone();

        self.push(value)
    }

    /// Swaps the first stack item with the item in `frame`.
    ///
    /// Note that this is a more general case of the `SWAP` opcodes as it can
    /// swap any two stack frames. It also swaps with the indicated frame
    /// directly, rather than the `n+1`th frame as for the `SWAP` opcodes.
    ///
    /// # Errors
    ///
    /// If either the source or target stack frame do not exist.
    pub fn swap(&mut self, frame: u16) -> anyhow::Result<()> {
        self.check_frame_at(0)?;
        self.check_frame_at(frame)?;
        let frame_index = self.top_frame_index()? - frame as usize;

        self.data.swap(0, frame_index);

        Ok(())
    }

    /// Gets the current size of the stack.
    pub fn size(&self) -> usize {
        self.data.len()
    }

    /// Checks if the stack is empty.
    pub fn is_empty(&self) -> bool {
        self.size() == 0
    }

    /// Checks if a frame exists at the provided `depth`.
    ///
    /// # Errors
    ///
    /// If there is no such stack frame.
    pub fn check_frame_at(&self, depth: u16) -> anyhow::Result<()> {
        let current_depth = self.data.len();

        if depth as usize >= current_depth {
            return Err(VMError::NoSuchStackFrame {
                depth: depth as i64,
            }
            .into());
        }

        Ok(())
    }

    /// Gets the index of the top frame.
    ///
    /// # Error
    ///
    /// If there are no frames on the stack.
    fn top_frame_index(&self) -> anyhow::Result<usize> {
        if self.data.is_empty() {
            return Err(VMError::NoSuchStackFrame { depth: -1 }.into());
        }

        Ok(self.data.len() - 1)
    }
}

#[cfg(test)]
mod test {
    use crate::{
        constant::MAXIMUM_STACK_DEPTH,
        vm::{
            state::stack::Stack,
            value::{BoxedVal, Provenance, SymbolicValue},
        },
    };

    /// Creates a new synthetic value for testing purposes.
    fn new_synthetic_value(instruction_pointer: u32) -> BoxedVal {
        SymbolicValue::new_value(instruction_pointer, Provenance::Synthetic)
    }

    /// Constructs a new stack with `item_count` unknown items pushed onto it.
    fn new_stack_with_items(item_count: usize) -> anyhow::Result<Stack> {
        let mut stack = Stack::new();
        for i in 0..item_count {
            stack.push(new_synthetic_value(i as u32))?
        }

        Ok(stack)
    }

    #[test]
    fn can_construct_new_stack() {
        let stack = Stack::new();
        assert_eq!(stack.size(), 0);
    }

    #[test]
    fn can_push_item_within_capacity() -> anyhow::Result<()> {
        let mut stack = Stack::new();
        stack.push(new_synthetic_value(0))?;

        Ok(())
    }

    #[test]
    fn cannot_push_outside_of_capacity() -> anyhow::Result<()> {
        let mut stack = new_stack_with_items(MAXIMUM_STACK_DEPTH)?;
        stack
            .push(new_synthetic_value(0))
            .expect_err("Pushing onto a full stack did not error");

        Ok(())
    }

    #[test]
    fn can_pop_item() -> anyhow::Result<()> {
        let mut stack = new_stack_with_items(1)?;
        stack.pop().expect("Unable to pop item that exists");

        Ok(())
    }

    #[test]
    fn cannot_pop_item_when_empty() -> anyhow::Result<()> {
        let mut stack = Stack::default();
        stack.pop().expect_err("Did not error when popping empty stack");
        Ok(())
    }

    #[test]
    fn can_read_item_at_depth() -> anyhow::Result<()> {
        let stack = new_stack_with_items(10)?;
        stack.read(7).expect("Did not read an item at depth 7");

        Ok(())
    }

    #[test]
    fn cannot_read_item_at_invalid_depth() -> anyhow::Result<()> {
        let stack = new_stack_with_items(10)?;
        stack
            .read(11)
            .expect_err("Read an item at a depth that doesn't exist");

        Ok(())
    }

    #[test]
    fn cannot_read_item_in_empty_stack() -> anyhow::Result<()> {
        let stack = Stack::default();
        stack.read(0).expect_err("Read a frame from an empty stack");

        Ok(())
    }

    #[test]
    fn can_dup_existing_item() -> anyhow::Result<()> {
        let mut stack = new_stack_with_items(10)?;
        assert_eq!(stack.size(), 10);
        stack.dup(3)?;
        assert_eq!(stack.size(), 11);

        Ok(())
    }

    #[test]
    fn cannot_dup_nonexistent_item() -> anyhow::Result<()> {
        let mut stack = new_stack_with_items(10)?;
        stack.dup(10).expect_err("Duplicated a nonexistent stack item");

        Ok(())
    }

    #[test]
    fn cannot_dup_item_when_empty() -> anyhow::Result<()> {
        let mut stack = Stack::default();
        stack
            .dup(0)
            .expect_err("Duplicated a stack item when stack was empty");

        Ok(())
    }

    #[test]
    fn can_swap_with_valid_item() -> anyhow::Result<()> {
        let mut stack = new_stack_with_items(100)?;
        stack.swap(83).expect("Unable to swap valid stack frames");

        Ok(())
    }

    #[test]
    fn cannot_swap_with_invalid_item() -> anyhow::Result<()> {
        let mut stack = new_stack_with_items(100)?;
        stack.swap(100).expect_err("Swapped with an invalid stack item");

        Ok(())
    }

    #[test]
    fn cannot_swap_while_empty() -> anyhow::Result<()> {
        let mut stack = Stack::default();
        stack.swap(0).expect_err("Swapped when the stack was empty");

        Ok(())
    }

    #[test]
    fn can_get_size_for_stack() -> anyhow::Result<()> {
        let empty = Stack::default();
        assert_eq!(empty.size(), 0);
        assert!(empty.is_empty());

        let non_empty = new_stack_with_items(100)?;
        assert_eq!(non_empty.size(), 100);
        assert!(!non_empty.is_empty());

        Ok(())
    }
}
