//! This module contains errors pertaining to the unification of typing evidence
//! gathered during symbolic execution of the bytecode.

use thiserror::Error;

use crate::{error::container, unifier::expression::TypeExpression, vm::value::BoxedVal};

/// Errors that occur during unification and type inference process in the
/// [`crate::unifier::Unifier`].
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum Error {
    #[error("Invalid tree {value:?} encountered during unification: {reason}")]
    InvalidTree { value: BoxedVal, reason: String },

    #[error("Invalid typing expression {value:?} encountered during unification: {reason}")]
    InvalidInference { value: TypeExpression, reason: String },
}

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

/// A unification error with an associated location in the bytecode.
pub type LocatedError = container::Located<Error>;

/// A container of unification errors used for aggregation of errors during
/// unification.
pub type Errors = container::Errors<LocatedError>;

/// The result type for methods that may have unification errors.
pub type Result<T> = std::result::Result<T, Errors>;
