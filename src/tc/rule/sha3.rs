//! This module contains inference rules related to encountering the `hash`
//! opcodes.

use crate::{
    constant::WORD_SIZE_BITS,
    error::unification::Result,
    tc::{expression::TE, rule::InferenceRule, state::TypeCheckerState},
    vm::value::{TCBoxedVal, TCSVD},
};

/// This rule states that the output of the `SHA3` opcode is a `bytes32`, which
/// is always true.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct HashRule;

impl InferenceRule for HashRule {
    fn infer(&self, value: &TCBoxedVal, state: &mut TypeCheckerState) -> Result<()> {
        match value.data() {
            TCSVD::Sha3 { .. } => {
                state.infer_for(value, TE::bytes(Some(WORD_SIZE_BITS)));
            }
            TCSVD::ExtCodeHash { address } => {
                state.infer_for(address, TE::address());
                state.infer_for(value, TE::bytes(Some(WORD_SIZE_BITS)));
            }
            _ => (),
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        constant::WORD_SIZE_BITS,
        tc::{
            expression::TE,
            rule::{sha3::HashRule, InferenceRule},
            state::TypeCheckerState,
        },
        vm::value::{Provenance, RSV, RSVD, TCSVD},
    };

    #[test]
    fn creates_correct_equations_for_sha3() -> anyhow::Result<()> {
        // Create some values
        let value = RSV::new_value(0, Provenance::Synthetic);
        let hash = RSV::new_synthetic(
            1,
            RSVD::Sha3 {
                data: value.clone(),
            },
        );

        // Create the state and run the tc
        let mut state = TypeCheckerState::empty();
        let hash_tv = state.register(hash);
        let tc_input = state.value_unchecked(hash_tv).clone();
        let value_tv = match tc_input.data() {
            TCSVD::Sha3 { data } => data.type_var(),
            _ => panic!("Incorrect payload"),
        };
        HashRule.infer(&tc_input, &mut state)?;

        // Check we get the correct equations
        assert!(state.inferences(value_tv).is_empty());
        assert!(state.inferences(hash_tv).contains(&TE::bytes(Some(WORD_SIZE_BITS))));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_ext_code_hash() -> anyhow::Result<()> {
        // Create some values
        let value = RSV::new_value(0, Provenance::Synthetic);
        let hash = RSV::new_synthetic(
            1,
            RSVD::ExtCodeHash {
                address: value.clone(),
            },
        );

        // Create the state and run the tc
        let mut state = TypeCheckerState::empty();
        let hash_tv = state.register(hash);
        let tc_input = state.value_unchecked(hash_tv).clone();
        let value_tv = match tc_input.data() {
            TCSVD::ExtCodeHash { address } => address.type_var(),
            _ => panic!("Incorrect payload"),
        };
        HashRule.infer(&tc_input, &mut state)?;

        // Check we get the correct equations
        assert!(state.inferences(value_tv).contains(&TE::address()));
        assert!(state.inferences(hash_tv).contains(&TE::bytes(Some(WORD_SIZE_BITS))));

        Ok(())
    }
}
