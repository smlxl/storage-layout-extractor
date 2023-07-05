//! This module contains inference rules related to encountering the `hash`
//! opcodes.

use crate::{
    constant::WORD_SIZE,
    unifier::{expression::TE, inference_rule::InferenceRule, state::TypingState},
    vm::value::{BoxedVal, SVD},
};

/// This rule states that the output of the `SHA3` opcode is a `bytes32`, which
/// is always true.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct HashRule;

impl InferenceRule for HashRule {
    fn infer(
        &self,
        value: &BoxedVal,
        state: &mut TypingState,
    ) -> crate::error::unification::Result<()> {
        match &value.data {
            SVD::Sha3 { .. } => {
                state.infer_for(value, TE::bytes(Some(WORD_SIZE)));
            }
            SVD::ExtCodeHash { address } => {
                state.infer_for(address, TE::address());
                state.infer_for(value, TE::bytes(Some(WORD_SIZE)));
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
            inference_rule::{sha3::HashRule, InferenceRule},
            state::TypingState,
        },
        vm::value::{Provenance, SV, SVD},
    };

    #[test]
    fn creates_correct_equations_for_sha3() -> anyhow::Result<()> {
        // Create some values
        let value = SV::new_value(0, Provenance::Synthetic);
        let hash = SV::new(
            1,
            SVD::Sha3 {
                data: value.clone(),
            },
            Provenance::Synthetic,
        );

        // Create the state and run the inference
        let mut state = TypingState::empty();
        let [value_tv, hash_tv] = state.register_many([value, hash.clone()]);
        HashRule.infer(&hash, &mut state)?;

        // Check we get the correct equations
        assert!(state.inferences(value_tv).is_empty());
        assert!(state.inferences(hash_tv).contains(&TE::bytes(Some(WORD_SIZE))));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_ext_code_hash() -> anyhow::Result<()> {
        // Create some values
        let value = SV::new_value(0, Provenance::Synthetic);
        let hash = SV::new(
            1,
            SVD::ExtCodeHash {
                address: value.clone(),
            },
            Provenance::Synthetic,
        );

        // Create the state and run the inference
        let mut state = TypingState::empty();
        let [value_tv, hash_tv] = state.register_many([value, hash.clone()]);
        HashRule.infer(&hash, &mut state)?;

        // Check we get the correct equations
        assert!(state.inferences(value_tv).contains(&TE::address()));
        assert!(state.inferences(hash_tv).contains(&TE::bytes(Some(WORD_SIZE))));

        Ok(())
    }
}
