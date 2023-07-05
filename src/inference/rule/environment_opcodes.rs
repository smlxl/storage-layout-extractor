//! This module contains an inference rule that deals with the basic types for a
//! variety of symbolic values that result from interactions with the
//! environment.

use crate::{
    inference::{expression::TE, rule::InferenceRule, state::InferenceState},
    vm::value::{BoxedVal, SVD},
};

/// This inference rule deals with a number of symbolic expressions that occur
/// from interactions with the environment. Many of them are terminals, in that
/// they do not change depending on the course of execution, but all have fixed
/// return types.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct EnvironmentCodesRule;

impl InferenceRule for EnvironmentCodesRule {
    fn infer(
        &self,
        value: &BoxedVal,
        state: &mut InferenceState,
    ) -> crate::error::unification::Result<()> {
        match &value.data {
            SVD::Address | SVD::Origin | SVD::Caller | SVD::CoinBase => {
                state.infer_for(value, TE::address());
            }
            SVD::Balance { address } => {
                state.infer_for(address, TE::address());
                state.infer_for(value, TE::unsigned_word(None));
            }
            SVD::CallValue
            | SVD::GasPrice
            | SVD::BlockTimestamp
            | SVD::BlockNumber
            | SVD::Prevrandao
            | SVD::GasLimit
            | SVD::ChainId
            | SVD::SelfBalance
            | SVD::BaseFee
            | SVD::Gas
            | SVD::CallDataSize => {
                state.infer_for(value, TE::unsigned_word(None));
            }
            SVD::SelfDestruct { target } => {
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
        inference::{
            expression::TE,
            rule::{environment_opcodes::EnvironmentCodesRule, InferenceRule},
            state::InferenceState,
        },
        vm::value::{Provenance, SV, SVD},
    };

    #[test]
    fn creates_correct_equations_for_address() -> anyhow::Result<()> {
        // Create a value
        let value = SV::new_synthetic(0, SVD::Address);

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let value_tv = state.register(value.clone());
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::address()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_origin() -> anyhow::Result<()> {
        // Create a value
        let value = SV::new_synthetic(0, SVD::Origin);

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let value_tv = state.register(value.clone());
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::address()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_caller() -> anyhow::Result<()> {
        // Create a value
        let value = SV::new_synthetic(0, SVD::Caller);

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let value_tv = state.register(value.clone());
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::address()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_coin_base() -> anyhow::Result<()> {
        // Create a value
        let value = SV::new_synthetic(0, SVD::CoinBase);

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let value_tv = state.register(value.clone());
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::address()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_balance() -> anyhow::Result<()> {
        // Create a value
        let address = SV::new_value(0, Provenance::Synthetic);
        let value = SV::new_synthetic(
            1,
            SVD::Balance {
                address: address.clone(),
            },
        );

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let [value_tv, address_tv] = state.register_many([value.clone(), address]);
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(address_tv).contains(&TE::address()));
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_call_value() -> anyhow::Result<()> {
        // Create a value
        let value = SV::new_synthetic(0, SVD::CallValue);

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let value_tv = state.register(value.clone());
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_gas_price() -> anyhow::Result<()> {
        // Create a value
        let value = SV::new_synthetic(0, SVD::GasPrice);

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let value_tv = state.register(value.clone());
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_block_timestamp() -> anyhow::Result<()> {
        // Create a value
        let value = SV::new_synthetic(0, SVD::BlockTimestamp);

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let value_tv = state.register(value.clone());
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_block_number() -> anyhow::Result<()> {
        // Create a value
        let value = SV::new_synthetic(0, SVD::BlockNumber);

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let value_tv = state.register(value.clone());
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_prevrandao() -> anyhow::Result<()> {
        // Create a value
        let value = SV::new_synthetic(0, SVD::Prevrandao);

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let value_tv = state.register(value.clone());
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_gas_limit() -> anyhow::Result<()> {
        // Create a value
        let value = SV::new_synthetic(0, SVD::GasLimit);

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let value_tv = state.register(value.clone());
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_chain_id() -> anyhow::Result<()> {
        // Create a value
        let value = SV::new_synthetic(0, SVD::ChainId);

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let value_tv = state.register(value.clone());
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_self_balance() -> anyhow::Result<()> {
        // Create a value
        let value = SV::new_synthetic(0, SVD::SelfBalance);

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let value_tv = state.register(value.clone());
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_base_fee() -> anyhow::Result<()> {
        // Create a value
        let value = SV::new_synthetic(0, SVD::BaseFee);

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let value_tv = state.register(value.clone());
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_gas() -> anyhow::Result<()> {
        // Create a value
        let value = SV::new_synthetic(0, SVD::Gas);

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let value_tv = state.register(value.clone());
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_call_data_size() -> anyhow::Result<()> {
        // Create a value
        let value = SV::new_synthetic(0, SVD::CallDataSize);

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let value_tv = state.register(value.clone());
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_self_destruct() -> anyhow::Result<()> {
        // Create a value
        let address = SV::new_value(0, Provenance::Synthetic);
        let value = SV::new_synthetic(
            1,
            SVD::SelfDestruct {
                target: address.clone(),
            },
        );

        // Create the state and run inference
        let mut state = InferenceState::empty();
        let [value_tv, address_tv] = state.register_many([value.clone(), address]);
        EnvironmentCodesRule.infer(&value, &mut state)?;

        // Check that we get the right equations
        assert!(state.inferences(address_tv).contains(&TE::address()));
        assert!(state.inferences(value_tv).is_empty());

        Ok(())
    }
}
