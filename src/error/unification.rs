//! This module contains errors pertaining to the unification of typing evidence
//! gathered during symbolic execution of the bytecode.

use thiserror::Error;

use crate::{
    error::container,
    tc::{
        expression::{InferenceSet, TypeExpression},
        state::type_variable::TypeVariable,
    },
    vm::value::TCBoxedVal,
};

/// Errors that occur during type checking in the [`crate::tc::TypeChecker`].
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum Error {
    #[error("Invalid tree {value:?} encountered during unification: {reason}")]
    InvalidTree { value: TCBoxedVal, reason: String },

    #[error("Invalid typing expression {value:?} encountered during unification: {reason}")]
    InvalidInference { value: TypeExpression, reason: String },

    #[error("Unification is not complete for {var:?}, found multiple inferences: {inferences:?}")]
    UnificationIncomplete { var: TypeVariable, inferences: InferenceSet },

    #[error("Type variable {var:?} has no associated inferences")]
    UnificationFailure { var: TypeVariable },

    #[error("Tried to convert {value} to fit in size {width} but it was too large")]
    OverSizedNumber { value: i128, width: usize },

    #[error("Type checking was stopped by the watchdog")]
    StoppedByWatchdog,
}

/// A unification error with an associated location in the bytecode.
pub type LocatedError = container::Located<Error>;

/// A container of unification errors used for aggregation of errors during
/// unification.
pub type Errors = container::Errors<LocatedError>;

/// The result type for methods that may have unification errors.
pub type Result<T> = std::result::Result<T, Errors>;

/// Make it possible to attach locations to these errors.
impl container::Locatable for Error {
    type Located = LocatedError;

    fn locate(self, instruction_pointer: u32) -> Self::Located {
        container::Located {
            location: instruction_pointer,
            payload:  self,
        }
    }
}
