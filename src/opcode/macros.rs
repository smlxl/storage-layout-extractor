//! This module contains useful macros for working with bytecode and opcodes.

/// Constructs a bytecode input from the input instructions as literal opcodes.
///
/// # Usage
///
/// ```
/// use storage_layout_extractor::{
///     bytecode,
///     opcode::{control, memory, Opcode},
/// };
///
/// let bytes = bytecode![
///     memory::PushN::new(1, vec![0x02]).unwrap(),
///     control::Jump,
///     control::JumpDest,
///     control::Stop,
/// ];
///
/// let mut expected: Vec<u8> = vec![];
/// expected.extend(memory::PushN::new(1, vec![0x02]).unwrap().encode());
/// expected.extend(control::Jump.encode());
/// expected.extend(control::JumpDest.encode());
/// expected.extend(control::Stop.encode());
///
/// assert_eq!(bytes, expected);
/// ```
#[macro_export]
macro_rules! bytecode {
    ($($path:expr),*$(,)?) => {{
        use $crate::opcode::Opcode;
        let mut vec: Vec<u8> = vec![];
        $(vec.extend($path.encode()));*;
        vec
    }};
}

// Export it scoped
pub use bytecode;
