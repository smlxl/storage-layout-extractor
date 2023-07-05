//! This module contains an inference rule that says that the key used for a
//! storage slot must be an unsigned integer.

use crate::{
    unifier::{expression::TE, inference_rule::InferenceRule, state::TypingState},
    vm::value::{BoxedVal, SVD},
};

/// This inference rule creates the equation `b = unsigned` for expressions of
/// the following form.
///
/// ```text
/// slot<key>
///   a   b
/// ```
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct StorageKeyRule;

impl InferenceRule for StorageKeyRule {
    fn infer(
        &self,
        value: &BoxedVal,
        state: &mut TypingState,
    ) -> crate::error::unification::Result<()> {
        let SVD::StorageSlot { key } = &value.data else { return Ok(()) };
        state.infer_for(key, TE::unsigned_word(None));

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        unifier::{
            expression::TE,
            inference_rule::{storage_key::StorageKeyRule, InferenceRule},
            state::TypingState,
        },
        vm::value::{Provenance, SV, SVD},
    };

    #[test]
    fn storage_keys_get_correct_equation() -> anyhow::Result<()> {
        // Create some values
        let key = SV::new_value(0, Provenance::Synthetic);
        let slot = SV::new_synthetic(1, SVD::StorageSlot { key: key.clone() });

        // Create the state and run inference
        let mut state = TypingState::empty();
        let [key_tv, slot_tv] = state.register_many([key, slot.clone()]);
        StorageKeyRule.infer(&slot, &mut state)?;

        // Check we get the equations
        assert!(state.inferences(key_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(slot_tv).is_empty());

        Ok(())
    }
}
