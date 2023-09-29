//! This module contains an inference rule that says that the key used for a
//! storage slot must be an unsigned integer.

use crate::{
    error::unification::Result,
    tc::{expression::TE, rule::InferenceRule, state::TypeCheckerState},
    vm::value::{TCBoxedVal, TCSVD},
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
    fn infer(&self, value: &TCBoxedVal, state: &mut TypeCheckerState) -> Result<()> {
        let TCSVD::StorageSlot { key } = value.data() else {
            return Ok(());
        };
        state.infer_for(key, TE::unsigned_word(None));

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        tc::{
            expression::TE,
            rule::{storage_key::StorageKeyRule, InferenceRule},
            state::TypeCheckerState,
        },
        vm::value::{Provenance, RSV, RSVD, TCSVD},
    };

    #[test]
    fn storage_keys_get_correct_equation() -> anyhow::Result<()> {
        // Create some values
        let key = RSV::new_value(0, Provenance::Synthetic);
        let slot = RSV::new_synthetic(1, RSVD::StorageSlot { key: key.clone() });

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let slot_tv = state.register(slot);
        let tc_input = state.value_unchecked(slot_tv).clone();
        let key_tv = match tc_input.data() {
            TCSVD::StorageSlot { key } => key.type_var(),
            _ => panic!("Incorrect payload"),
        };
        StorageKeyRule.infer(&tc_input, &mut state)?;

        // Check we get the equations
        assert!(state.inferences(key_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(slot_tv).is_empty());

        Ok(())
    }
}
