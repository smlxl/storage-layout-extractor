//! This module contains an inference rule for dealing with values that relate
//! to external code.

use crate::{
    inference::{expression::TE, rule::InferenceRule, state::InferenceState},
    vm::value::{BoxedVal, SVD},
};

/// This rule creates inferences for dealing with external code.
///
/// For expressions of the form:
///
/// ```text
/// ext_code_size(address)
///       a          b
/// ```
///
/// - `a = unsigned`
/// - `b = address`
///
/// For expressions of the form:
///
/// ```text
/// ext_code_copy(address, offset, size)
///       a          b        c      d
/// ```
///
/// - `b = address`
/// - `c = unsigned`
/// - `d = unsigned`
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct ExtCodeRule;

impl InferenceRule for ExtCodeRule {
    fn infer(
        &self,
        value: &BoxedVal,
        state: &mut InferenceState,
    ) -> crate::error::unification::Result<()> {
        match &value.data {
            SVD::ExtCodeSize { address } => {
                state.infer_for(address, TE::address());
                state.infer_for(value, TE::unsigned_word(None));
            }
            SVD::ExtCodeCopy {
                address,
                offset,
                size,
            } => {
                state.infer_for_many([offset, size], TE::unsigned_word(None));
                state.infer_for(address, TE::address());
            }
            _ => (),
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        inference::{
            expression::TE,
            rule::{ext_code::ExtCodeRule, InferenceRule},
            state::InferenceState,
        },
        vm::value::{Provenance, SV, SVD},
    };

    #[test]
    fn creates_correct_equations_for_ext_code_size() -> anyhow::Result<()> {
        // Create some values
        let address = SV::new_value(0, Provenance::Synthetic);
        let operator = SV::new_synthetic(
            1,
            SVD::ExtCodeSize {
                address: address.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = InferenceState::empty();
        let [address_tv, operator_tv] = state.register_many([address, operator.clone()]);
        ExtCodeRule.infer(&operator, &mut state)?;

        // Check we get the equations we want
        assert!(state.inferences(address_tv).contains(&TE::address()));
        assert!(state.inferences(operator_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_ext_code_copy() -> anyhow::Result<()> {
        // Create some values
        let address = SV::new_value(0, Provenance::Synthetic);
        let offset = SV::new_value(1, Provenance::Synthetic);
        let size = SV::new_value(2, Provenance::Synthetic);
        let operator = SV::new_synthetic(
            3,
            SVD::ExtCodeCopy {
                address: address.clone(),
                offset:  offset.clone(),
                size:    size.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = InferenceState::empty();
        let [address_tv, offset_tv, size_tv, operator_tv] =
            state.register_many([address, offset, size, operator.clone()]);
        ExtCodeRule.infer(&operator, &mut state)?;

        // Check we get the equations we want
        assert!(state.inferences(address_tv).contains(&TE::address()));
        assert!(state.inferences(offset_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(size_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(operator_tv).is_empty());

        Ok(())
    }
}
