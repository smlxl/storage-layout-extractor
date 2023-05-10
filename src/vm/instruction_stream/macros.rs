//! This module contains macro definitions for working with the instruction
//! stream.

/// A small piece of shorthand to make writing the parser simpler and cleaner.
#[macro_export]
macro_rules! add_op {
    ($name:ident, $val:expr) => {
        $name.push(Box::new($val))
    };
}
