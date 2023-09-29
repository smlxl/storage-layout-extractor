//! This module contains the inference rule definition for equating the types of
//! storage slots to the types of their contained values.

use crate::{
    error::unification::Result,
    tc::{expression::TE, rule::InferenceRule, state::TypeCheckerState},
    vm::value::{TCBoxedVal, TCSVD},
};

/// This rule creates the following equations in the typing state for equations
/// of the following form:
///
/// ```text
/// s_store(slot, value)
///    a     b      c
/// ```
///
/// equating:
///
/// - `b = c`
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct StorageWriteRule;

impl InferenceRule for StorageWriteRule {
    fn infer(&self, value: &TCBoxedVal, state: &mut TypeCheckerState) -> Result<()> {
        match value.data() {
            TCSVD::StorageWrite { key, value } => {
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
        tc::{
            expression::TE,
            rule::{storage_write::StorageWriteRule, InferenceRule},
            state::TypeCheckerState,
        },
        vm::value::{Provenance, RSV, RSVD, TCSVD},
    };

    #[test]
    fn equates_slot_type_and_value_type() -> anyhow::Result<()> {
        // Create a value of the relevant kind
        let input_key = RSV::new_value(0, Provenance::Synthetic);
        let input_value = RSV::new_value(1, Provenance::Synthetic);
        let write = RSV::new_synthetic(
            2,
            RSVD::StorageWrite {
                key:   input_key.clone(),
                value: input_value.clone(),
            },
        );

        // Set up the unifier state
        let mut state = TypeCheckerState::empty();
        let write_tv = state.register(write);
        let tc_input = state.value_unchecked(write_tv).clone();
        let [key_tv, value_tv] = match tc_input.data() {
            TCSVD::StorageWrite { key, value } => [key.type_var(), value.type_var()],
            _ => panic!("Invalid payload"),
        };
        StorageWriteRule.infer(&tc_input, &mut state)?;

        // Check that the equalities hold and that we only get the judgements we expect
        assert_eq!(state.inferences(key_tv).len(), 1);
        assert!(state.inferences(key_tv).contains(&TE::eq(value_tv)));
        assert_eq!(state.inferences(value_tv).len(), 1);
        assert!(state.inferences(value_tv).contains(&TE::eq(key_tv)));
        assert!(state.inferences(write_tv).is_empty());

        Ok(())
    }
}
