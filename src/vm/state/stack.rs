//! This module contains the implementation of the symbolic virtual machine's
//! stack.

use crate::{
    constant::MAXIMUM_STACK_DEPTH,
    error::{
        container::Locatable,
        execution::{Error, Result},
    },
    vm::value::RuntimeBoxedVal,
};

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
/// is of size [`crate::constant::WORD_SIZE_BITS`]. Here, the symbolic virtual
/// machine maintains the same maximum depth, but instead stores
/// [`crate::vm::value::SymbolicValue`]s instead of words, so the size limit is
/// implicitly and subtly different.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Stack {
    data: Vec<RuntimeBoxedVal>,
}

impl Stack {
    /// Creates a new stack without any items on it.
    #[must_use]
    pub fn new() -> Self {
        let data = Vec::with_capacity(MAXIMUM_STACK_DEPTH);
        Self { data }
    }

    /// Pushes the provided value onto the top of the stack.
    ///
    /// # Errors
    ///
    /// If the stack cannot grow to accommodate the requested `data`.
    pub fn push(&mut self, data: RuntimeBoxedVal) -> StackResult<()> {
        if self.data.len() + 1 > MAXIMUM_STACK_DEPTH {
            return Err(Error::StackDepthExceeded {
                requested: self.data.len() + 1,
            });
        }
        self.data.push(data);
        Ok(())
    }

    /// Pops the top value from the stack.
    ///
    /// # Errors
    ///
    /// If the stack has no item to pop.
    pub fn pop(&mut self) -> StackResult<RuntimeBoxedVal> {
        self.data.pop().ok_or(Error::NoSuchStackFrame { depth: 0 })
    }

    /// Reads from the stack frame at the provided `depth`.
    ///
    /// # Errors
    ///
    /// If `depth` does not exist in the stack.
    pub fn read(&self, depth: u32) -> StackResult<&RuntimeBoxedVal> {
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
    pub fn duplicate(&mut self, frame: u32) -> StackResult<()> {
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
    pub fn swap(&mut self, frame: u32) -> StackResult<()> {
        let top_frame = self.top_frame_index()?;
        self.check_frame_at(0)?;
        self.check_frame_at(frame)?;
        let frame_index = top_frame - frame as usize;

        self.data.swap(top_frame, frame_index);

        Ok(())
    }

    /// Gets the current depth of the stack.
    #[must_use]
    pub fn depth(&self) -> usize {
        self.data.len()
    }

    /// Checks if the stack is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.depth() == 0
    }

    /// Checks if a frame exists at the provided `depth`.
    ///
    /// # Errors
    ///
    /// If there is no such stack frame.
    fn check_frame_at(&self, depth: u32) -> StackResult<()> {
        let current_depth = self.data.len();

        if depth as usize >= current_depth {
            return Err(Error::NoSuchStackFrame {
                depth: i64::from(depth),
            });
        }

        Ok(())
    }

    /// Gets the index of the top frame.
    ///
    /// # Error
    ///
    /// If there are no frames on the stack.
    fn top_frame_index(&self) -> StackResult<usize> {
        if self.data.is_empty() {
            return Err(Error::NoSuchStackFrame { depth: -1 });
        }

        Ok(self.data.len() - 1)
    }

    /// Creates a new wrapper of the stack that knows about the instruction
    /// pointer location where its operations are taking place.
    #[must_use]
    pub fn new_located(&mut self, instruction_pointer: u32) -> LocatedStackHandle<'_> {
        LocatedStackHandle {
            instruction_pointer,
            stack: self,
        }
    }

    /// Consumes the virtual machine stack and returns all of the values that it
    /// knows about.
    #[must_use]
    pub fn all_values(self) -> Vec<RuntimeBoxedVal> {
        self.data
    }
}

impl From<Stack> for Vec<RuntimeBoxedVal> {
    fn from(value: Stack) -> Self {
        value.data
    }
}

/// The result type used for error handling in the stack implementation.
///
/// Specifically, this is a non-located counterpart to [`Result`] as it is not
/// the duty of the stack to know about where it is being used.
pub type StackResult<T> = std::result::Result<T, Error>;

/// A wrapper of the stack that knows the instruction pointer at which its
/// operations are performed, allowing the holder to perform mutable operations
/// that return located errors.
#[derive(Debug)]
pub struct LocatedStackHandle<'a> {
    instruction_pointer: u32,
    stack:               &'a mut Stack,
}

impl<'a> LocatedStackHandle<'a> {
    /// Pushes the provided value onto the top of the stack.
    ///
    /// # Errors
    ///
    /// If the stack cannot grow to accommodate the requested `data`.
    pub fn push(&mut self, data: RuntimeBoxedVal) -> Result<()> {
        self.stack.push(data).locate(self.instruction_pointer)
    }

    /// Pops the top value from the stack.
    ///
    /// # Errors
    ///
    /// If the stack has no item to pop.
    pub fn pop(&mut self) -> Result<RuntimeBoxedVal> {
        self.stack.pop().locate(self.instruction_pointer)
    }

    /// Reads from the stack frame at the provided `depth`.
    ///
    /// # Errors
    ///
    /// If `depth` does not exist in the stack.
    pub fn read(&self, depth: u32) -> Result<&RuntimeBoxedVal> {
        self.stack.read(depth).locate(self.instruction_pointer)
    }

    /// Duplicates the stack item at `frame` onto the top of the stack.
    ///
    /// This is a more general case of the `DUP` opcodes as it can duplicate any
    /// available stack frame.
    ///
    /// # Errors
    ///
    /// If `frame` doesn't exist.
    pub fn dup(&mut self, frame: u32) -> Result<()> {
        self.stack.duplicate(frame).locate(self.instruction_pointer)
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
    pub fn swap(&mut self, frame: u32) -> Result<()> {
        self.stack.swap(frame).locate(self.instruction_pointer)
    }
}

#[cfg(test)]
mod test {
    use crate::{
        constant::MAXIMUM_STACK_DEPTH,
        vm::{
            state::stack::Stack,
            value::{Provenance, RuntimeBoxedVal, RSV},
        },
    };

    /// Creates a new synthetic value for testing purposes.
    #[allow(clippy::unnecessary_box_returns)] // We use boxes everywhere during execution
    fn new_synthetic_value(instruction_pointer: u32) -> RuntimeBoxedVal {
        RSV::new_value(instruction_pointer, Provenance::Synthetic)
    }

    /// Constructs a new stack with `item_count` unknown items pushed onto it.
    fn new_stack_with_items(item_count: usize) -> anyhow::Result<Stack> {
        let mut stack = Stack::new();
        for i in (0..item_count).rev() {
            stack.push(new_synthetic_value(u32::try_from(i).expect(
                "We only deal with instruction streams up to length u32::MAX",
            )))?;
        }

        Ok(stack)
    }

    #[test]
    fn can_construct_new_stack() {
        let stack = Stack::new();
        assert_eq!(stack.depth(), 0);
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
    fn cannot_pop_item_when_empty() {
        let mut stack = Stack::default();
        stack.pop().expect_err("Did not error when popping empty stack");
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
    fn cannot_read_item_in_empty_stack() {
        let stack = Stack::default();
        stack.read(0).expect_err("Read a frame from an empty stack");
    }

    #[test]
    fn can_dup_existing_item() -> anyhow::Result<()> {
        let mut stack = new_stack_with_items(10)?;
        assert_eq!(stack.depth(), 10);
        stack.duplicate(3)?;
        assert_eq!(stack.depth(), 11);

        Ok(())
    }

    #[test]
    fn cannot_dup_nonexistent_item() -> anyhow::Result<()> {
        let mut stack = new_stack_with_items(10)?;
        stack.duplicate(10).expect_err("Duplicated a nonexistent stack item");

        Ok(())
    }

    #[test]
    fn cannot_dup_item_when_empty() {
        let mut stack = Stack::default();
        stack
            .duplicate(0)
            .expect_err("Duplicated a stack item when stack was empty");
    }

    #[test]
    fn can_swap_with_valid_item() -> anyhow::Result<()> {
        let mut stack = new_stack_with_items(100)?;
        let item_top = stack.read(0)?.clone();
        let item_to_swap = stack.read(83)?.clone();
        stack.swap(83).expect("Unable to swap valid stack frames");

        let new_top = stack.read(0)?.clone();
        let swapped_item = stack.read(83)?.clone();

        assert_eq!(swapped_item, item_top);
        assert_eq!(new_top, item_to_swap);

        Ok(())
    }

    #[test]
    fn cannot_swap_with_invalid_item() -> anyhow::Result<()> {
        let mut stack = new_stack_with_items(100)?;
        stack.swap(100).expect_err("Swapped with an invalid stack item");

        Ok(())
    }

    #[test]
    fn cannot_swap_while_empty() {
        let mut stack = Stack::default();
        stack.swap(0).expect_err("Swapped when the stack was empty");
    }

    #[test]
    fn can_get_size_for_stack() -> anyhow::Result<()> {
        let empty = Stack::default();
        assert_eq!(empty.depth(), 0);
        assert!(empty.is_empty());

        let non_empty = new_stack_with_items(100)?;
        assert_eq!(non_empty.depth(), 100);
        assert!(!non_empty.is_empty());

        Ok(())
    }
}
