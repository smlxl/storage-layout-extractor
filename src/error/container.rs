use std::fmt::Formatter;

use thiserror::Error;

/// An error that is localised to a particular byte-offset location in the
/// bytecode.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub struct Located<E>
where
    E: Clone,
{
    /// The byte offset in the bytecode where the error occurred.
    pub location: u32,

    /// The error data
    pub payload: E,
}

/// Displays the error associated with the hexadecimal-encoded byte offset in
/// the bytecode where the error occurred.
impl<E> std::fmt::Display for Located<E>
where
    E: std::fmt::Display + Clone,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[0x{}]: {}",
            hex::encode(self.location.to_le_bytes()),
            self.payload
        )
    }
}

/// A trait for types that can have a byte-offset location attached to them.
pub trait Locatable
where
    Self: Sized,
{
    /// The return type with the attached byte-offset location.
    type Located;

    /// Attach the location described by `instruction_pointer` (a byte offset in
    /// the bytecode) to the error.
    fn locate(self, instruction_pointer: u32) -> Self::Located;
}

/// A blanket implementation that allows for attaching a location to any result.
impl<T, E> Locatable for Result<T, E>
where
    E: std::error::Error + Clone,
{
    type Located = Result<T, Located<E>>;

    fn locate(self, instruction_pointer: u32) -> Self::Located {
        self.map_err(|e| Located {
            location: instruction_pointer,
            payload:  e,
        })
    }
}

/// An error that is a collection of errors.
///
/// The order of the errors in the container is dependent on the contained type
/// `E`, but defaults to the order in which the errors were added to the
/// container.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub struct Errors<E> {
    payloads: Vec<E>,
}

impl<E> Errors<E> {
    /// Creates a new container for errors.
    #[must_use]
    pub fn new() -> Self {
        let payloads = vec![];
        Self { payloads }
    }

    /// Gets the errors contained within this error.
    #[must_use]
    pub fn payloads(&self) -> &[E] {
        self.payloads.as_slice()
    }

    /// Gets the length of the errors container.
    #[must_use]
    pub fn len(&self) -> usize {
        self.payloads.len()
    }

    /// Checks if the errors container is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<E> Errors<E>
where
    E: std::error::Error,
{
    /// Adds the provided `error` to the container.
    pub fn add(&mut self, error: E) {
        self.payloads.push(error);
    }

    /// Adds the multiple provided errors to the container.
    pub fn add_many(&mut self, errors: impl Into<Vec<E>>) {
        self.payloads.extend(errors.into());
    }
}

/// Where the locations are a known type, the container ensures that the errors
/// with locations are sorted in order of their occurrence in the bytecode.
impl<E> Errors<Located<E>>
where
    E: std::error::Error + Clone,
{
    /// Adds an error `payload` at the specific `instruction_pointer` location
    /// in the bytecode.
    pub fn add_located(&mut self, instruction_pointer: u32, payload: E) {
        let error = Located {
            location: instruction_pointer,
            payload,
        };
        self.payloads.push(error);
        self.sort();
    }

    /// Adds many errors to the container at once.
    pub fn add_many_located(&mut self, errors: impl Into<Vec<Located<E>>>) {
        self.payloads.extend(errors.into());
        self.sort();
    }

    /// Sorts the errors based on their bytecode location.
    fn sort(&mut self) {
        self.payloads.sort_by_key(|item| item.location);
    }
}

/// The default errors container is one containing no errors.
impl<E> Default for Errors<E> {
    fn default() -> Self {
        Self::new()
    }
}

/// Allow conversion from any error type to a container of errors.
impl<E> From<E> for Errors<E>
where
    E: std::error::Error,
{
    fn from(value: E) -> Self {
        let mut errors = Self::default();
        errors.add(value);
        errors
    }
}

/// Allow conversion from the errors container to a vector of errors.
impl<E> From<Errors<E>> for Vec<E>
where
    E: std::error::Error,
{
    fn from(value: Errors<E>) -> Self {
        value.payloads
    }
}

/// Allow conversion from a vector of errors to the errors container.
impl<E> From<Vec<E>> for Errors<E>
where
    E: std::error::Error,
{
    fn from(value: Vec<E>) -> Self {
        Self { payloads: value }
    }
}

/// Displays the errors in the sequence in which they occur in the container.
///
/// It has a header specifying how many errors occurred, and then prints one
/// error per line after that. This means that in the case where errors did
/// occur, the output of `fmt` is multi-line.
impl<E> std::fmt::Display for Errors<E>
where
    E: std::fmt::Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.payloads.is_empty() {
            write!(f, "Encountered no errors")?;
        } else {
            writeln!(f, "Encountered {} errors:", self.payloads.len())?;
            for error in &self.payloads {
                writeln!(f, "{error}")?;
            }
        }

        Ok(())
    }
}
