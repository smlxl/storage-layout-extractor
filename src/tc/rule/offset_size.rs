//! This module contains an inference rule for dealing with data that is built
//! from an offset into memory and a size.

use crate::{
    error::unification::Result,
    tc::{expression::TE, rule::InferenceRule, state::TypeCheckerState},
    vm::value::{TCBoxedVal, TCSVD},
};

/// This rule creates the following equations for any expressions of the
/// following form:
///
/// ```text
///   call_data(id, offset, size)
///   code_copy(    offset, size)
/// return_data(    offset, size)
///                    a      b
/// ```
///
/// - `a = unsigned`
/// - `b = unsigned`
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct OffsetSizeRule;

impl InferenceRule for OffsetSizeRule {
    fn infer(&self, value: &TCBoxedVal, state: &mut TypeCheckerState) -> Result<()> {
        match value.data() {
            TCSVD::CallData { offset, size, .. }
            | TCSVD::CodeCopy { offset, size }
            | TCSVD::ReturnData { offset, size } => {
                state.infer_for_many([offset, size], TE::unsigned_word(None));
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
            rule::{offset_size::OffsetSizeRule, InferenceRule},
            state::TypeCheckerState,
        },
        vm::value::{Provenance, RSV, RSVD, TCSVD},
    };

    #[test]
    fn creates_correct_equations_for_call_data() -> anyhow::Result<()> {
        // Create some values
        let offset = RSV::new_value(0, Provenance::Synthetic);
        let size = RSV::new_value(1, Provenance::Synthetic);
        let value = RSV::new_synthetic(2, RSVD::call_data(offset.clone(), size.clone()));

        // Create the state and run the tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value);
        let tc_input = state.value_unchecked(value_tv).clone();
        let [offset_tv, size_tv] = match tc_input.data() {
            TCSVD::CallData { offset, size, .. } => [offset.type_var(), size.type_var()],
            _ => panic!("Incorrect payload"),
        };
        OffsetSizeRule.infer(&tc_input, &mut state)?;

        // Check that we get the correct equations
        assert!(state.inferences(offset_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(size_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(value_tv).is_empty());

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_code_copy() -> anyhow::Result<()> {
        // Create some values
        let offset = RSV::new_value(0, Provenance::Synthetic);
        let size = RSV::new_value(1, Provenance::Synthetic);
        let value = RSV::new_synthetic(
            2,
            RSVD::CodeCopy {
                offset: offset.clone(),
                size:   size.clone(),
            },
        );

        // Create the state and run the tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value);
        let tc_input = state.value_unchecked(value_tv).clone();
        let [offset_tv, size_tv] = match tc_input.data() {
            TCSVD::CodeCopy { offset, size } => [offset.type_var(), size.type_var()],
            _ => panic!("Incorrect payload"),
        };
        OffsetSizeRule.infer(&tc_input, &mut state)?;

        // Check that we get the correct equations
        assert!(state.inferences(offset_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(size_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(value_tv).is_empty());

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_return_data() -> anyhow::Result<()> {
        // Create some values
        let offset = RSV::new_value(0, Provenance::Synthetic);
        let size = RSV::new_value(1, Provenance::Synthetic);
        let value = RSV::new_synthetic(
            2,
            RSVD::ReturnData {
                offset: offset.clone(),
                size:   size.clone(),
            },
        );

        // Create the state and run the tc
        let mut state = TypeCheckerState::empty();
        let value_tv = state.register(value);
        let tc_input = state.value_unchecked(value_tv).clone();
        let [offset_tv, size_tv] = match tc_input.data() {
            TCSVD::ReturnData { offset, size } => [offset.type_var(), size.type_var()],
            _ => panic!("Incorrect payload"),
        };
        OffsetSizeRule.infer(&tc_input, &mut state)?;

        // Check that we get the correct equations
        assert!(state.inferences(offset_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(size_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(value_tv).is_empty());

        Ok(())
    }
}
