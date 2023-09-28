//! This module contains an inference rule for dealing with values that relate
//! to external code.

use crate::{
    error::unification::Result,
    tc::{expression::TE, rule::InferenceRule, state::TypeCheckerState},
    vm::value::{TCBoxedVal, TCSVD},
};

/// This rule creates inferences for dealing with operations on and with
/// external code.
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
    fn infer(&self, value: &TCBoxedVal, state: &mut TypeCheckerState) -> Result<()> {
        match value.data() {
            TCSVD::ExtCodeSize { address } => {
                state.infer_for(address, TE::address());
                state.infer_for(value, TE::unsigned_word(None));
            }
            TCSVD::ExtCodeCopy {
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
        tc::{
            expression::TE,
            rule::{ext_code::ExtCodeRule, InferenceRule},
            state::TypeCheckerState,
        },
        vm::value::{Provenance, RSV, RSVD, TCSVD},
    };

    #[test]
    fn creates_correct_equations_for_ext_code_size() -> anyhow::Result<()> {
        // Create some values
        let address = RSV::new_value(0, Provenance::Synthetic);
        let operator = RSV::new_synthetic(
            1,
            RSVD::ExtCodeSize {
                address: address.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = TypeCheckerState::empty();
        let operator_tv = state.register(operator);
        let tc_input = state.value_unchecked(operator_tv).clone();
        let address_tv = match tc_input.data() {
            TCSVD::ExtCodeSize { address } => address.type_var(),
            _ => panic!("Incorrect payload"),
        };
        ExtCodeRule.infer(&tc_input, &mut state)?;

        // Check we get the equations we want
        assert!(state.inferences(address_tv).contains(&TE::address()));
        assert!(state.inferences(operator_tv).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_ext_code_copy() -> anyhow::Result<()> {
        // Create some values
        let address = RSV::new_value(0, Provenance::Synthetic);
        let offset = RSV::new_value(1, Provenance::Synthetic);
        let size = RSV::new_value(2, Provenance::Synthetic);
        let operator = RSV::new_synthetic(
            3,
            RSVD::ExtCodeCopy {
                address: address.clone(),
                offset:  offset.clone(),
                size:    size.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = TypeCheckerState::empty();
        let operator_tv = state.register(operator);
        let tc_input = state.value_unchecked(operator_tv).clone();
        let [address_tv, offset_tv, size_tv] = match tc_input.data() {
            TCSVD::ExtCodeCopy {
                address,
                offset,
                size,
            } => [address.type_var(), offset.type_var(), size.type_var()],
            _ => panic!("Incorrect payload"),
        };
        ExtCodeRule.infer(&tc_input, &mut state)?;

        // Check we get the equations we want
        assert!(state.inferences(address_tv).contains(&TE::address()));
        assert!(state.inferences(offset_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(size_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(operator_tv).is_empty());

        Ok(())
    }
}
