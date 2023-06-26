//! This module contains the inference rule definition for equating the types of
//! storage slots to the types of their contained values.

use crate::{
    error::unification::Result,
    unifier::{expression::TE, inference_rule::InferenceRule, state::TypingState},
    vm::value::{BoxedVal, SVD},
};

/// This rule creates equations such that for `s_store(slot, value)`,
/// `type(slot)` == `type(value)`.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct StorageWriteRule;

impl InferenceRule for StorageWriteRule {
    fn infer(&self, value: &BoxedVal, state: &mut TypingState) -> Result<()> {
        match &value.data {
            SVD::StorageWrite { key, value } => {
                // An equality for the key's type
                let key_tv = state.var_unchecked(key);
                let key_type = TE::eq(key_tv);

                // An equality for the value's type
                let value_tv = state.var_unchecked(value);
                let value_type = TE::eq(value_tv);

                // Add the equalities as needed
                state.infer(key_tv, value_type);
                state.infer(value_tv, key_type);

                Ok(())
            }
            _ => Ok(()),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{
        unifier::{
            expression::TE,
            inference_rule::{storage_write::StorageWriteRule, InferenceRule},
            state::TypingState,
        },
        vm::value::{Provenance, SV, SVD},
    };

    #[test]
    fn equates_slot_type_and_value_type() -> anyhow::Result<()> {
        // Create a value of the relevant kind
        let input_key = SV::new_value(0, Provenance::Synthetic);
        let input_value = SV::new_value(1, Provenance::Synthetic);
        let write = SV::new(
            2,
            SVD::StorageWrite {
                key:   input_key.clone(),
                value: input_value.clone(),
            },
            Provenance::Synthetic,
        );

        // Set up the unifier state
        let mut state = TypingState::empty();
        let key_tv = state.register(input_key);
        let value_tv = state.register(input_value);
        let write_tv = state.register(write.clone());

        // Run the inference rule
        StorageWriteRule.infer(&write, &mut state)?;

        // Check that the equalities hold and that we only get the judgements we expect
        assert_eq!(state.inferences(key_tv).len(), 1);
        assert!(state.inferences(key_tv).contains(&TE::eq(value_tv)));
        assert_eq!(state.inferences(value_tv).len(), 1);
        assert!(state.inferences(value_tv).contains(&TE::eq(key_tv)));
        assert!(state.inferences(write_tv).is_empty());

        Ok(())
    }
}
