//! This module contains an inference rule for dealing with data that is built
//! from an offset into memory and a size.

use crate::{
    inference::{expression::TE, rule::InferenceRule, state::InferenceState},
    vm::value::{BoxedVal, SVD},
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
    fn infer(
        &self,
        value: &BoxedVal,
        state: &mut InferenceState,
    ) -> crate::error::unification::Result<()> {
        match &value.data {
            SVD::CallData { offset, size, .. }
            | SVD::CodeCopy { offset, size }
            | SVD::ReturnData { offset, size } => {
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
        inference::{
            expression::TE,
            rule::{offset_size::OffsetSizeRule, InferenceRule},
            state::InferenceState,
        },
        vm::value::{Provenance, SV, SVD},
    };

    #[test]
    fn creates_correct_equations_for_call_data() -> anyhow::Result<()> {
        // Create some values
        let offset = SV::new_value(0, Provenance::Synthetic);
        let size = SV::new_value(1, Provenance::Synthetic);
        let value = SV::new_synthetic(2, SVD::call_data(offset.clone(), size.clone()));

        // Create the state and run the inference
        let mut state = InferenceState::empty();
        let [offset_tv, size_tv, value_tv] = state.register_many([offset, size, value.clone()]);
        OffsetSizeRule.infer(&value, &mut state)?;

        // Check that we get the correct equations
        assert!(state.inferences(offset_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(size_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(value_tv).is_empty());

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_code_copy() -> anyhow::Result<()> {
        // Create some values
        let offset = SV::new_value(0, Provenance::Synthetic);
        let size = SV::new_value(1, Provenance::Synthetic);
        let value = SV::new_synthetic(
            2,
            SVD::CodeCopy {
                offset: offset.clone(),
                size:   size.clone(),
            },
        );

        // Create the state and run the inference
        let mut state = InferenceState::empty();
        let [offset_tv, size_tv, value_tv] = state.register_many([offset, size, value.clone()]);
        OffsetSizeRule.infer(&value, &mut state)?;

        // Check that we get the correct equations
        assert!(state.inferences(offset_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(size_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(value_tv).is_empty());

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_return_data() -> anyhow::Result<()> {
        // Create some values
        let offset = SV::new_value(0, Provenance::Synthetic);
        let size = SV::new_value(1, Provenance::Synthetic);
        let value = SV::new_synthetic(
            2,
            SVD::ReturnData {
                offset: offset.clone(),
                size:   size.clone(),
            },
        );

        // Create the state and run the inference
        let mut state = InferenceState::empty();
        let [offset_tv, size_tv, value_tv] = state.register_many([offset, size, value.clone()]);
        OffsetSizeRule.infer(&value, &mut state)?;

        // Check that we get the correct equations
        assert!(state.inferences(offset_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(size_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(value_tv).is_empty());

        Ok(())
    }
}
