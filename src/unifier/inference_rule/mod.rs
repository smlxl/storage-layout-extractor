//! This module contains the definition of the `InferenceRule` trait that
//! provides the unifier with the ability to make inferences based on the
//! structure of the symbolic values.

mod dynamic_array_write;
pub mod mapping_access;
pub mod storage_write;

use std::{
    any::{Any, TypeId},
    collections::HashSet,
    fmt::Debug,
    ops::Deref,
};

use derivative::Derivative;
use downcast_rs::Downcast;

use crate::{
    error::unification::Result,
    unifier::{
        inference_rule::{
            dynamic_array_write::DynamicArrayWriteRule,
            mapping_access::MappingAccessRule,
            storage_write::StorageWriteRule,
        },
        state::{TypeVariable, TypingState},
    },
    vm::value::BoxedVal,
};

/// A trait representing processes for
pub trait InferenceRule
where
    Self: Any + Debug + Downcast,
{
    /// Runs the analysis on the provided `value` and its associated
    /// `type_variable` with access to the unifier state in `state` into which
    /// it can write typing judgements.
    ///
    /// # Modifying the Unifier State
    ///
    /// These rules are explicitly allowed to modify the [`TypingState`] of the
    /// unifier as part of their execution, and indeed this is the only way for
    /// it to return results.
    ///
    /// # Tree-Based Values
    ///
    /// While the `value` handed to this rule is often a tree of values, the
    /// inference rule can assume that it will be passed _every node_ in this
    /// tree at some point.
    ///
    /// It is recommended to only make inferences about the current level of the
    /// tree unless explicitly necessary to do so otherwise. This will be more
    /// efficient as it prevents re-doing work.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if something goes wrong with the heuristic analysis.
    fn infer(&self, value: &BoxedVal, ty_var: TypeVariable, state: &mut TypingState) -> Result<()>;
}

/// A container for a set of inference rules that will be run in an arbitrary
/// order.
#[derive(Debug)]
pub struct InferenceRules {
    /// The inference rules.
    rules: HashSet<RulesItem>,
}

impl InferenceRules {
    /// Constructs a new container for inference rules.
    #[must_use]
    pub fn new() -> Self {
        let rules = HashSet::new();
        Self { rules }
    }

    /// Adds the `rule` to the list of rules.
    ///
    /// If a pass of the given type already exists in the ordering, it will not
    /// be added.
    pub fn add<R: InferenceRule>(&mut self, rule: R) {
        self.rules.insert(RulesItem::new(rule));
    }

    /// Runs all of the contained passes on the provided `value`  in an
    /// arbitrary order, with access to modify the unifier `state`,
    /// returning the any value.
    ///
    /// See [`InferenceRule::infer`] for more information on this process and
    /// what it can do.
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if any of the passes error.
    pub fn infer(
        &mut self,
        value: &BoxedVal,
        ty_var: TypeVariable,
        state: &mut TypingState,
    ) -> Result<()> {
        for rule in &self.rules {
            rule.infer(value, ty_var, state)?;
        }

        Ok(())
    }
}

impl Default for InferenceRules {
    fn default() -> Self {
        let mut rules = Self::new();
        rules.add(StorageWriteRule);
        rules.add(MappingAccessRule);
        rules.add(DynamicArrayWriteRule);

        rules
    }
}

/// An internal type to make it possible to base the rules container around a
/// set.
#[derive(Debug, Derivative)]
#[derivative(Hash, Eq, PartialEq)]
struct RulesItem {
    /// A field used to hash the inference rule.
    pub hash_key: TypeId,

    /// The inference rule itself.
    #[derivative(PartialEq = "ignore", Hash = "ignore")]
    pub rule: Box<dyn InferenceRule>,
}

impl RulesItem {
    /// Constructs a new inference rules item.
    pub fn new<R: InferenceRule>(rule: R) -> Self {
        let hash_key = TypeId::of::<R>();
        let rule = Box::new(rule);

        Self { hash_key, rule }
    }
}

/// Allow deref-coercions from the rules item to the rule it contains for ease
/// of use internally.
impl Deref for RulesItem {
    type Target = Box<dyn InferenceRule>;

    fn deref(&self) -> &Self::Target {
        &self.rule
    }
}
