//! This module contains an inference rule that equates every `SLoad` with the
//! type of its element.

use crate::{
    inference::{expression::TE, rule::InferenceRule, state::InferenceState},
    vm::value::{BoxedVal, SVD},
};

/// This rule creates the following equations in the typing state for
/// expressions of the following form.
///
/// ```text
/// s_load(key, value)
///    a    b     c
/// ```
///
/// equating
///
/// - `a = c`
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct SLoadIsElementTypeRule;

impl InferenceRule for SLoadIsElementTypeRule {
    fn infer(
        &self,
        value: &BoxedVal,
        state: &mut InferenceState,
    ) -> crate::error::unification::Result<()> {
        let SVD::SLoad {
            value: inner_value, ..
        } = &value.data
        else {
            return Ok(());
        };

        let inner_value_tv = state.var_unchecked(inner_value);
        state.infer_for(value, TE::eq(inner_value_tv));

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        inference::{
            expression::TE,
            rule::{s_load_is_element_type::SLoadIsElementTypeRule, InferenceRule},
            state::InferenceState,
        },
        vm::value::{Provenance, SV, SVD},
    };

    #[test]
    fn creates_correct_equations_in_state() -> anyhow::Result<()> {
        // Create the expressions to be typed
        let key = SV::new_value(0, Provenance::Synthetic);
        let value = SV::new_value(1, Provenance::Synthetic);
        let s_load = SV::new_synthetic(
            2,
            SVD::SLoad {
                key:   key.clone(),
                value: value.clone(),
            },
        );

        // Register these in the state
        let mut state = InferenceState::empty();
        let [key_ty, value_ty, s_load_ty] = state.register_many([key, value, s_load.clone()]);

        // Run the inference rule and check things make sense
        SLoadIsElementTypeRule.infer(&s_load, &mut state)?;

        assert!(state.inferences(key_ty).is_empty());

        assert_eq!(state.inferences(value_ty).len(), 1);
        assert!(state.inferences(value_ty).contains(&TE::eq(s_load_ty)));

        assert_eq!(state.inferences(s_load_ty).len(), 1);
        assert!(state.inferences(s_load_ty).contains(&TE::eq(value_ty)));

        Ok(())
    }
}
