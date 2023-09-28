//! This module contains the definition of the `Lift` trait that provides the
//! type checker with the ability to add higher-level value constructors based
//! on lower-level patterns.

pub mod dynamic_array_access;
pub mod mapping_index;
pub mod mapping_offset;
pub mod mul_shifted;
pub mod packed_encoding;
pub mod proxy_slots;
pub mod recognise_hashed_slots;
pub mod storage_slots;
pub mod sub_word;

use std::{
    any::{Any, TypeId},
    fmt::Debug,
};

use downcast_rs::Downcast;

use crate::{
    error::unification::Result,
    tc::{
        lift::{
            dynamic_array_access::DynamicArrayIndex,
            mapping_index::MappingIndex,
            mapping_offset::MappingOffset,
            mul_shifted::MulShiftedValue,
            packed_encoding::PackedEncoding,
            proxy_slots::ProxySlots,
            recognise_hashed_slots::StorageSlotHashes,
            storage_slots::StorageSlots,
            sub_word::SubWordValue,
        },
        state::TypeCheckerState,
    },
    vm::value::RuntimeBoxedVal,
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
    /// # Errors
    ///
    /// Returns [`Err`] if something goes wrong with the lifting process.
    fn run(&mut self, value: RuntimeBoxedVal, state: &TypeCheckerState) -> Result<RuntimeBoxedVal>;
}

/// A container for an ordered set of lifting passes that will be run in
/// order.
#[derive(Debug)]
pub struct LiftingPasses {
    /// The ordered list of passes that will be executed in order.
    passes: Vec<Box<dyn Lift>>,
}

impl LiftingPasses {
    /// Creates a new instance of the lifting pass with the provided `passes`
    #[must_use]
    pub fn new(passes: impl Into<Vec<Box<dyn Lift>>>) -> Self {
        Self {
            passes: passes.into(),
        }
    }

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
    #[must_use]
    pub fn get<P: Lift>(&self) -> Option<&P> {
        self.passes
            .iter()
            .find(|p| p.as_ref().as_any().is::<P>())
            .and_then(|p| p.as_ref().as_any().downcast_ref::<P>())
    }

    /// Gets a reference to the pass of the given type, if it exists in the
    /// passes container.
    ///
    /// # Safety
    ///
    /// This function allows modifying pass state, and hence can violate
    /// invariants of the pass. Only use this function if you carefully
    /// understand the implications of doing so.
    pub unsafe fn get_mut<P: Lift>(&mut self) -> Option<&mut P> {
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
    pub fn run(
        &mut self,
        mut value: RuntimeBoxedVal,
        state: &TypeCheckerState,
    ) -> Result<RuntimeBoxedVal> {
        for pass in &mut self.passes {
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
                ProxySlots::new(),
                MappingIndex::new(),
                SubWordValue::new(),
                MulShiftedValue::new(),
                PackedEncoding::new(),
                DynamicArrayIndex::new(),
                StorageSlots::new(),
                MappingOffset::new(),
            ],
        }
    }
}
