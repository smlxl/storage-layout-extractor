//! This module contains inference rules for dealing with the arguments and
//! return values when creating new contracts.

use crate::{
    constant::WORD_SIZE_BITS,
    error::unification::Result,
    tc::{expression::TE, rule::InferenceRule, state::TypeCheckerState},
    vm::value::{TCBoxedVal, TCSVD},
};

/// This inference rule states that the result of calling either `CREATE` or
/// `CREATE2` is an address, and that the provided `value` upon creation is some
/// unsigned integer.
///
/// We know nothing about the data from this usage site.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct CreateContractRule;

impl InferenceRule for CreateContractRule {
    fn infer(&self, value: &TCBoxedVal, state: &mut TypeCheckerState) -> Result<()> {
        match value.data() {
            TCSVD::Create {
                value: create_val, ..
            } => {
                state.infer_for(value, TE::address());
                state.infer_for(create_val, TE::unsigned_word(None));
            }
            TCSVD::Create2 {
                value: create_val,
                salt,
                ..
            } => {
                state.infer_for(value, TE::address());
                state.infer_for(create_val, TE::unsigned_word(None));
                state.infer_for(salt, TE::bytes(Some(WORD_SIZE_BITS)));
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
            rule::{create::CreateContractRule, InferenceRule},
            state::TypeCheckerState,
        },
        vm::value::{Provenance, RSV, RSVD, TCSVD},
    };

    #[test]
    fn creates_correct_equations_for_create() -> anyhow::Result<()> {
        // Create some values
        let value = RSV::new_value(0, Provenance::Synthetic);
        let data = RSV::new_value(1, Provenance::Synthetic);
        let create = RSV::new_synthetic(
            2,
            RSVD::Create {
                value: value.clone(),
                data:  data.clone(),
            },
        );

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let create_tv = state.register(create);
        let tc_input = state.value_unchecked(create_tv).clone();
        let [value_tv, data_tv] = match tc_input.data() {
            TCSVD::Create { value, data } => [value.type_var(), data.type_var()],
            _ => panic!("Incorrect payload"),
        };
        CreateContractRule.infer(&tc_input, &mut state)?;

        // Check that the equations are right
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(data_tv).is_empty());
        assert!(state.inferences(create_tv).contains(&TE::address()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_create2() -> anyhow::Result<()> {
        // Create some values
        let value = RSV::new_value(0, Provenance::Synthetic);
        let data = RSV::new_value(1, Provenance::Synthetic);
        let salt = RSV::new_value(2, Provenance::Synthetic);
        let create = RSV::new_synthetic(
            3,
            RSVD::Create2 {
                value: value.clone(),
                salt:  salt.clone(),
                data:  data.clone(),
            },
        );

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let create_tv = state.register(create);
        let tc_input = state.value_unchecked(create_tv).clone();
        let [value_tv, data_tv, salt_tv] = match tc_input.data() {
            TCSVD::Create2 { value, data, salt } => {
                [value.type_var(), data.type_var(), salt.type_var()]
            }
            _ => panic!("Incorrect payload"),
        };
        CreateContractRule.infer(&tc_input, &mut state)?;

        // Check that the equations are right
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(salt_tv).contains(&TE::bytes(Some(WORD_SIZE_BITS))));
        assert!(state.inferences(data_tv).is_empty());
        assert!(state.inferences(create_tv).contains(&TE::address()));

        Ok(())
    }
}
