//! This module contains a rule that states that a Shifted has the type of the
//! value that it shifts.

use crate::{
    inference::{expression::TE, rule::InferenceRule, state::InferenceState},
    vm::value::{BoxedVal, SVD},
};

/// This rule creates the following equations in the typing state for
/// expressions of the following form.
///
/// ```text
/// shifted(offset, value)
///    a              b
/// ```
///
/// equating
///
/// - `a = b`
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct ShiftedHasElementTypeRule;

impl InferenceRule for ShiftedHasElementTypeRule {
    fn infer(
        &self,
        value: &BoxedVal,
        state: &mut InferenceState,
    ) -> crate::error::unification::Result<()> {
        let SVD::Shifted {
            value: shifted_value,
            ..
        } = &value.data
        else {
            return Ok(());
        };

        let shifted_value_tv = state.var_unchecked(shifted_value);
        state.infer_for(value, TE::eq(shifted_value_tv));

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        inference::{
            expression::TE,
            rule::{shifted_has_element_type::ShiftedHasElementTypeRule, InferenceRule},
            state::InferenceState,
        },
        vm::value::{Provenance, SV, SVD},
    };

    #[test]
    fn creates_correct_equations_in_typing_state() -> anyhow::Result<()> {
        // Create some values to operate on
        let value = SV::new_value(0, Provenance::Synthetic);
        let shifted = SV::new_synthetic(
            1,
            SVD::Shifted {
                offset: 64,
                value:  value.clone(),
            },
        );

        // Register these in the state
        let mut state = InferenceState::empty();
        let [value_tv, shifted_tv] = state.register_many([value, shifted.clone()]);

        // Run the pass and check the results
        ShiftedHasElementTypeRule.infer(&shifted, &mut state)?;

        assert!(state.inferences(value_tv).contains(&TE::eq(shifted_tv)));
        assert!(state.inferences(shifted_tv).contains(&TE::eq(value_tv)));

        Ok(())
    }
}