//! This module contains an inference rule for dealing with values explicitly
//! used as conditions.

use crate::{
    unifier::{expression::TE, inference_rule::InferenceRule, state::TypingState},
    vm::value::{BoxedVal, SVD},
};

/// This rule creates the equation `a = bool` for expressions of the following
/// form.
///
/// ```text
/// cond(value)
///   a    b
/// ```
///
/// - `a = bool`
/// - `b = bool`
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct ConditionRule;

impl InferenceRule for ConditionRule {
    fn infer(
        &self,
        value: &BoxedVal,
        state: &mut TypingState,
    ) -> crate::error::unification::Result<()> {
        let SVD::Condition { value: cond_val } = &value.data else { return Ok(()) };
        state.infer_for_many([value, cond_val], TE::bool());

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        unifier::{
            expression::TE,
            inference_rule::{condition::ConditionRule, InferenceRule},
            state::TypingState,
        },
        vm::value::{Provenance, SV, SVD},
    };

    #[test]
    fn creates_correct_equations_for_conditions() -> anyhow::Result<()> {
        // Create the values
        let value = SV::new_value(0, Provenance::Synthetic);
        let cond = SV::new_synthetic(
            1,
            SVD::Condition {
                value: value.clone(),
            },
        );

        // Create the state and run the inference
        let mut state = TypingState::empty();
        let [value_tv, cond_tv] = state.register_many([value, cond.clone()]);
        ConditionRule.infer(&cond, &mut state)?;

        // Check we get the equations
        assert!(state.inferences(value_tv).contains(&TE::bool()));
        assert!(state.inferences(cond_tv).contains(&TE::bool()));

        Ok(())
    }
}
