//! This module contains an inference rule that deals with the basic types for a
//! variety of symbolic values that result from interactions with the
//! environment.

use crate::{
    error::unification::Result,
    tc::{expression::TE, rule::InferenceRule, state::TypeCheckerState},
    vm::value::{TCBoxedVal, TCSVD},
};

/// This inference rule deals with a number of symbolic expressions that occur
/// from interactions with the environment. Many of them are terminals, in that
/// they do not change depending on the course of execution, but all have fixed
/// return types.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct EnvironmentCodesRule;

impl InferenceRule for EnvironmentCodesRule {
    fn infer(&self, value: &TCBoxedVal, state: &mut TypeCheckerState) -> Result<()> {
        match value.data() {
            TCSVD::Address | TCSVD::Origin | TCSVD::Caller | TCSVD::CoinBase => {
                state.infer_for(value, TE::address());
            }
            TCSVD::Balance { address } => {
                state.infer_for(address, TE::address());
                state.infer_for(value, TE::unsigned_word(None));
            }
            TCSVD::CallValue
            | TCSVD::GasPrice
            | TCSVD::BlockTimestamp
            | TCSVD::BlockNumber
            | TCSVD::Prevrandao
            | TCSVD::GasLimit
            | TCSVD::ChainId
            | TCSVD::SelfBalance
            | TCSVD::BaseFee
            | TCSVD::Gas
            | TCSVD::CallDataSize => {
                state.infer_for(value, TE::unsigned_word(None));
            }
            TCSVD::SelfDestruct { target } => {
                state.infer_for(target, TE::address());
            }
            _ => (),
        };

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        tc::{
            expression::TE,
            rule::{environment_opcodes::EnvironmentCodesRule, InferenceRule},
            state::TypeCheckerState,
        },
        vm::value::{Provenance, RSV, RSVD, TCSVD},
    };

    #[test]
    fn creates_correct_equations_for_address() -> anyhow::Result<()> {
        // Create a value
        let value = RSV::new_synthetic(0, RSVD::Address);

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value.clone());
        let tc_input = state.value_unchecked(value_tv).clone();
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::address()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_origin() -> anyhow::Result<()> {
        // Create a value
        let value = RSV::new_synthetic(0, RSVD::Origin);

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value.clone());
        let tc_input = state.value_unchecked(value_tv).clone();
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::address()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_caller() -> anyhow::Result<()> {
        // Create a value
        let value = RSV::new_synthetic(0, RSVD::Caller);

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value.clone());
        let tc_input = state.value_unchecked(value_tv).clone();
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::address()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_coin_base() -> anyhow::Result<()> {
        // Create a value
        let value = RSV::new_synthetic(0, RSVD::CoinBase);

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value.clone());
        let tc_input = state.value_unchecked(value_tv).clone();
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::address()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_balance() -> anyhow::Result<()> {
        // Create a value
        let address = RSV::new_value(0, Provenance::Synthetic);
        let value = RSV::new_synthetic(
            1,
            RSVD::Balance {
                address: address.clone(),
            },
        );

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value);
        let tc_input = state.value_unchecked(value_tv).clone();
        let address_tv = match tc_input.data() {
            TCSVD::Balance { address } => address.type_var(),
            _ => panic!("Incorrect payload"),
        };
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(address_tv).contains(&TE::address()));
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_call_value() -> anyhow::Result<()> {
        // Create a value
        let value = RSV::new_synthetic(0, RSVD::CallValue);

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value.clone());
        let tc_input = state.value_unchecked(value_tv).clone();
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_gas_price() -> anyhow::Result<()> {
        // Create a value
        let value = RSV::new_synthetic(0, RSVD::GasPrice);

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value.clone());
        let tc_input = state.value_unchecked(value_tv).clone();
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_block_timestamp() -> anyhow::Result<()> {
        // Create a value
        let value = RSV::new_synthetic(0, RSVD::BlockTimestamp);

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value.clone());
        let tc_input = state.value_unchecked(value_tv).clone();
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_block_number() -> anyhow::Result<()> {
        // Create a value
        let value = RSV::new_synthetic(0, RSVD::BlockNumber);

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value.clone());
        let tc_input = state.value_unchecked(value_tv).clone();
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_prevrandao() -> anyhow::Result<()> {
        // Create a value
        let value = RSV::new_synthetic(0, RSVD::Prevrandao);

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value.clone());
        let tc_input = state.value_unchecked(value_tv).clone();
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_gas_limit() -> anyhow::Result<()> {
        // Create a value
        let value = RSV::new_synthetic(0, RSVD::GasLimit);

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value.clone());
        let tc_input = state.value_unchecked(value_tv).clone();
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_chain_id() -> anyhow::Result<()> {
        // Create a value
        let value = RSV::new_synthetic(0, RSVD::ChainId);

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value.clone());
        let tc_input = state.value_unchecked(value_tv).clone();
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_self_balance() -> anyhow::Result<()> {
        // Create a value
        let value = RSV::new_synthetic(0, RSVD::SelfBalance);

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value.clone());
        let tc_input = state.value_unchecked(value_tv).clone();
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_base_fee() -> anyhow::Result<()> {
        // Create a value
        let value = RSV::new_synthetic(0, RSVD::BaseFee);

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value.clone());
        let tc_input = state.value_unchecked(value_tv).clone();
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_gas() -> anyhow::Result<()> {
        // Create a value
        let value = RSV::new_synthetic(0, RSVD::Gas);

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value.clone());
        let tc_input = state.value_unchecked(value_tv).clone();
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_call_data_size() -> anyhow::Result<()> {
        // Create a value
        let value = RSV::new_synthetic(0, RSVD::CallDataSize);

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value.clone());
        let tc_input = state.value_unchecked(value_tv).clone();
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_self_destruct() -> anyhow::Result<()> {
        // Create a value
        let address = RSV::new_value(0, Provenance::Synthetic);
        let value = RSV::new_synthetic(
            1,
            RSVD::SelfDestruct {
                target: address.clone(),
            },
        );

        // Create the state and run tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value);
        let tc_input = state.value_unchecked(value_tv).clone();
        let address_tv = match tc_input.data() {
            TCSVD::SelfDestruct { target } => target.type_var(),
            _ => panic!("Incorrect payload"),
        };
        EnvironmentCodesRule.infer(&tc_input, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(address_tv).contains(&TE::address()));
        assert!(state.inferences(value_tv).is_empty());

        Ok(())
    }
}
