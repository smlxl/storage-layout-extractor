//! This module defines the type variable type and the source of type variables
//! within the type checker.

use std::{
    fmt::{Display, Formatter},
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

use crate::data::vector_map::{FromUniqueIndex, ToUniqueIndex};

/// A source of new, unique, type variables.
///
/// It is guaranteed that no matter how many times you clone the source, they
/// all use the same underlying pool and hence cannot allocate duplicate
/// variables.
///
/// # Type Variable Pools
///
/// Care must be taken not to mix type variables from independent pools, as
/// these _could_ produce duplicates.
///
/// It is currently possible to perform such mixing due to the lack of
/// type-level exclusion of type variables from different domains. This could be
/// enforced at the type level in the future. Look at the following potential
/// crates if this is of interest:
///
/// - [`deptypes`](https://docs.rs/crate/deptypes/latest)
/// - [`generativity`](https://docs.rs/crate/generativity/latest)
/// - [`unique_type`](https://docs.rs/crate/unique-type/latest)
#[derive(Clone, Debug)]
pub struct TypeVariableSource {
    last_var: Arc<AtomicUsize>,
}

impl TypeVariableSource {
    /// Creates a new source of unique type variables.
    #[must_use]
    pub fn new() -> Self {
        let last_var = Arc::new(AtomicUsize::from(0));
        Self { last_var }
    }

    /// Requests a new unique type variable from the source.
    #[must_use]
    pub fn fresh(&mut self) -> TypeVariable {
        let source = self.last_var.fetch_add(1, Ordering::Relaxed);
        unsafe { TypeVariable::wrapping(source) }
    }

    /// Gets the number of type variables that have been allocated by this
    /// source.
    #[must_use]
    pub fn allocated_count(&self) -> usize {
        self.last_var.load(Ordering::Relaxed)
    }
}

impl Default for TypeVariableSource {
    fn default() -> Self {
        Self::new()
    }
}

/// A type variable represents the possibly-unbound type of an expression.
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TypeVariable {
    id: usize,
}

impl TypeVariable {
    /// Creates a new type variable wrapping the provided `id`.
    ///
    /// This function is not public as it is intended to only be accessible in
    /// the current module so that the [`TypeVariableSource`] is the only
    /// source of type variables for a program.
    ///
    /// # Safety
    ///
    /// Calling this function allows uncontrolled creation of type variables, so
    /// care must be taken even when accounting for its only being accessible in
    /// this module.
    #[must_use]
    unsafe fn wrapping(id: usize) -> Self {
        TypeVariable { id }
    }
}

impl Display for TypeVariable {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "V[{}]", &self.id)
    }
}

impl From<&TypeVariable> for TypeVariable {
    fn from(value: &TypeVariable) -> Self {
        *value
    }
}

impl ToUniqueIndex for TypeVariable {
    fn index(&self) -> usize {
        self.id
    }
}

impl FromUniqueIndex for TypeVariable {
    fn from_index(index: usize) -> Self {
        let id = index;
        Self { id }
    }
}

#[cfg(test)]
mod test {
    use crate::tc::state::type_variable::TypeVariableSource;

    #[test]
    fn can_create_fresh_type_variable() {
        let mut factory = TypeVariableSource::new();
        let _ = factory.fresh();
    }
}
