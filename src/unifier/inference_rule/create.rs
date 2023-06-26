//! This module contains inference rules for dealing with the arguments and
//! return values when creating new contracts.

use crate::{
    constant::WORD_SIZE,
    unifier::{expression::TE, inference_rule::InferenceRule, state::TypingState},
    vm::value::{BoxedVal, SVD},
};

/// This inference rule states that the result of calling either `CREATE` or
/// `CREATE2` is an address, and that the provided `value` upon creation is some
/// unsigned integer.
///
/// We know nothing about the data from this usage site.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct CreateContractRule;

impl InferenceRule for CreateContractRule {
    fn infer(
        &self,
        value: &BoxedVal,
        state: &mut TypingState,
    ) -> crate::error::unification::Result<()> {
        match &value.data {
            SVD::Create {
                value: create_val, ..
            } => {
                state.infer_for(value, TE::address());
                state.infer_for(create_val, TE::unsigned_word(None));
            }
            SVD::Create2 {
                value: create_val,
                salt,
                ..
            } => {
                state.infer_for(value, TE::address());
                state.infer_for(create_val, TE::unsigned_word(None));
                state.infer_for(salt, TE::bytes(Some(WORD_SIZE)));
            }
            _ => (),
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        constant::WORD_SIZE,
        unifier::{
            expression::TE,
            inference_rule::{create::CreateContractRule, InferenceRule},
            state::TypingState,
        },
        vm::value::{Provenance, SV, SVD},
    };

    #[test]
    fn creates_correct_equations_for_create() -> anyhow::Result<()> {
        // Create some values
        let value = SV::new_value(0, Provenance::Synthetic);
        let data = SV::new_value(1, Provenance::Synthetic);
        let create = SV::new_synthetic(
            2,
            SVD::Create {
                value: value.clone(),
                data:  data.clone(),
            },
        );

        // Create the state and run inference
        let mut state = TypingState::empty();
        let [value_tv, data_tv, create_tv] = state.register_many([value, data, create.clone()]);
        CreateContractRule.infer(&create, &mut state)?;

        // Check that the equations are right
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(data_tv).is_empty());
        assert!(state.inferences(create_tv).contains(&TE::address()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_create2() -> anyhow::Result<()> {
        // Create some values
        let value = SV::new_value(0, Provenance::Synthetic);
        let data = SV::new_value(1, Provenance::Synthetic);
        let salt = SV::new_value(2, Provenance::Synthetic);
        let create = SV::new_synthetic(
            3,
            SVD::Create2 {
                value: value.clone(),
                salt:  salt.clone(),
                data:  data.clone(),
            },
        );

        // Create the state and run inference
        let mut state = TypingState::empty();
        let [value_tv, salt_tv, data_tv, create_tv] =
            state.register_many([value, salt, data, create.clone()]);
        CreateContractRule.infer(&create, &mut state)?;

        // Check that the equations are right
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(salt_tv).contains(&TE::bytes(Some(WORD_SIZE))));
        assert!(state.inferences(data_tv).is_empty());
        assert!(state.inferences(create_tv).contains(&TE::address()));

        Ok(())
    }
}
