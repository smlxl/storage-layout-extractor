//! This module contains the definition of the `Lift` trait that provides the
//! unifier with the ability to add higher-level value constructors based on
//! lower-level patterns.

pub mod dynamic_array_access;
pub mod mapping_access;
pub mod mask_word;
pub mod recognise_hashed_slots;
pub mod storage_slots;

use std::{
    any::{Any, TypeId},
    fmt::Debug,
};

use downcast_rs::Downcast;

use crate::{
    error::unification::Result,
    unifier::{
        lift::{
            dynamic_array_access::DynamicArrayAccess,
            mapping_access::MappingAccess,
            mask_word::MaskWord,
            recognise_hashed_slots::StorageSlotHashes,
            storage_slots::StorageSlots,
        },
        state::TypingState,
    },
    vm::value::BoxedVal,
};

/// A trait representing processes for _introducing_ higher-level constructs
/// into the symbolic value representation.
pub trait Lift
where
    Self: Any + Debug + Downcast,
{
    /// Executes the pass on the provided `value`, with access to the pass state
    /// in `self` and the unifier state in `state`, returning a
    /// potentially-transformed `value`.
    ///
    /// Implementations of `run` can assume that the input `value` has had
    /// [`crate::vm::value::SymbolicValueData::constant_fold`] called on it.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if something goes wrong with the lifting process.
    fn run(&mut self, value: BoxedVal, state: &TypingState) -> Result<BoxedVal>;
}

/// A container for an ordered set of lifting passes that will be run in
/// order.
#[derive(Debug)]
pub struct LiftingPasses {
    /// The ordered list of passes that will be executed in order.
    passes: Vec<Box<dyn Lift>>,
}

impl LiftingPasses {
    /// Adds the `pass` to the end of the pass ordering.
    ///
    /// If a pass of the given type already exists in the ordering, it will not
    /// be added.
    pub fn add<P: Lift>(&mut self, pass: P) {
        let ids: Vec<TypeId> = self.passes.iter().map(|p| p.as_ref().type_id()).collect();
        let pass_id = pass.type_id();

        if ids.contains(&pass_id) {
            return;
        }

        let alloc = Box::new(pass);
        self.passes.push(alloc);
    }

    /// Gets a reference to the pass of the given type, if it exists in the
    /// passes container.
    pub fn get<P: Lift>(&self) -> Option<&P> {
        self.passes
            .iter()
            .find(|p| p.as_ref().as_any().is::<P>())
            .and_then(|p| p.as_ref().as_any().downcast_ref::<P>())
    }

    /// Gets a reference to the pass of the given type, if it exists in the
    /// passes container.
    pub fn get_mut<P: Lift>(&mut self) -> Option<&mut P> {
        self.passes
            .iter_mut()
            .find(|p| p.as_ref().as_any().is::<P>())
            .and_then(|p| p.as_mut().as_any_mut().downcast_mut::<P>())
    }

    /// Runs all of the contained passes in order on the provided `value`, with
    /// access to modify the unifier `state`, returning the potentially-modified
    /// value.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if any of the passes error.
    pub fn run(&mut self, mut value: BoxedVal, state: &TypingState) -> Result<BoxedVal> {
        for pass in self.passes.iter_mut() {
            value = pass.run(value, state)?;
        }

        Ok(value)
    }
}

impl Default for LiftingPasses {
    fn default() -> Self {
        Self {
            passes: vec![
                StorageSlotHashes::new(),
                MaskWord::new(),
                MappingAccess::new(),
                DynamicArrayAccess::new(),
                StorageSlots::new(),
            ],
        }
    }
}
