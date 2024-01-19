//! This module contains the primary error type for the extractor's interface.
//! It also re-exports the more specific error types that are
//! subsystem-specific.

pub mod container;
pub mod disassembly;
pub mod execution;
pub mod unification;

use thiserror::Error;

/// The interface result type for the library.
///
/// # Usage
///
/// Any function considered to be part of the public interface of the library
/// should return this result type. Subsystems should return the more-specific
/// child error types as appropriate.
///
/// Note that _all_ of the library is public in order to facilitate use-cases
/// beyond the ones designed for.
pub type Result<T> = std::result::Result<T, Errors>;

/// The interface error type for the library.
///
/// All errors returned from the library interface (and hence encountered by the
/// clients of the library) should be members of this enum.
#[derive(Clone, Debug, Error)]
pub enum Error {
    /// Errors that come from the disassembly process.
    #[error(transparent)]
    Disassembly(#[from] disassembly::Error),

    /// Errors from the Virtual Machine subsystem of the library.
    #[error(transparent)]
    Execution(#[from] execution::Error),

    /// Errors from the unification subsystem of the library.
    #[error(transparent)]
    Unification(#[from] unification::Error),

    /// An unknown error, represented as a string.
    #[error("Unknown Error: {_0:?}")]
    Other(String),
}

impl Error {
    /// Constructs an unknown error with the provided `message`.
    pub fn other(message: impl Into<String>) -> Self {
        Self::Other(message.into())
    }
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

/// A library error with an associated bytecode location.
pub type LocatedError = container::Located<Error>;

/// A container of errors that may occur in the extractor.
pub type Errors = container::Errors<LocatedError>;

/// Allow simple conversions from located disassembly errors by re-wrapping the
/// located error around the more general payload.
impl From<disassembly::LocatedError> for LocatedError {
    fn from(value: disassembly::LocatedError) -> Self {
        let instruction_pointer = value.location;
        let payload = Error::from(value.payload);
        Self {
            location: instruction_pointer,
            payload,
        }
    }
}

/// Allow simple conversions from located disassembly errors by re-wrapping the
/// located error around the more general payload in the Errors container.
impl From<disassembly::LocatedError> for Errors {
    fn from(value: disassembly::LocatedError) -> Self {
        let re_wrapped: LocatedError = value.into();
        re_wrapped.into()
    }
}

/// Allow simple conversions from located execution errors by re-wrapping the
/// located error around the more general payload.
impl From<execution::LocatedError> for LocatedError {
    fn from(value: execution::LocatedError) -> Self {
        let instruction_pointer = value.location;
        let payload = Error::from(value.payload);
        Self {
            location: instruction_pointer,
            payload,
        }
    }
}

/// Allow simple conversions from located execution errors by re-wrapping the
/// located error around the more general payload in the Errors container.
impl From<execution::LocatedError> for Errors {
    fn from(value: execution::LocatedError) -> Self {
        let re_wrapped: LocatedError = value.into();
        re_wrapped.into()
    }
}

/// Allow simple conversions from located unification errors by re-wrapping the
/// located error around the more general payload.
impl From<unification::LocatedError> for LocatedError {
    fn from(value: unification::LocatedError) -> Self {
        let instruction_pointer = value.location;
        let payload = Error::from(value.payload);
        Self {
            location: instruction_pointer,
            payload,
        }
    }
}

/// Allow simple conversions from located unification errors by re-wrapping the
/// located error around the more general payload in the Errors container.
impl From<unification::LocatedError> for Errors {
    fn from(value: unification::LocatedError) -> Self {
        let re_wrapped: LocatedError = value.into();
        re_wrapped.into()
    }
}

/// Allow conversion from the execution errors container to the general errors
/// container.
impl From<execution::Errors> for Errors {
    fn from(value: execution::Errors) -> Self {
        let errs: Vec<execution::LocatedError> = value.into();
        let new_errs: Vec<LocatedError> = errs.into_iter().map(std::convert::Into::into).collect();

        new_errs.into()
    }
}

/// Allow conversion from the unification errors container to the general errors
/// container.
impl From<unification::Errors> for Errors {
    fn from(value: unification::Errors) -> Self {
        let errs: Vec<unification::LocatedError> = value.into();
        let new_errs: Vec<LocatedError> = errs.into_iter().map(std::convert::Into::into).collect();

        new_errs.into()
    }
}
