//! This module defines basic inferences for the set of boolean operations that
//! can be performed on the EVM.

use crate::{
    inference::{expression::TE, rule::InferenceRule, state::InferenceState},
    vm::value::{BoxedVal, SVD},
};

/// This rule is responsible for making inferences based on the presence of
/// boolean operations.
///
/// Unfortunately, many boolean operations do not tell us much as they operate
/// bitwise, but we can usually say that the operands are some kind of word.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct BooleanOpsRule;

impl InferenceRule for BooleanOpsRule {
    fn infer(
        &self,
        value: &BoxedVal,
        state: &mut InferenceState,
    ) -> crate::error::unification::Result<()> {
        match &value.data {
            // LT and GT are numeric comparisons, so we know that the operands are numeric, and not
            // treated as signed
            SVD::LessThan { left, right } | SVD::GreaterThan { left, right } => {
                state.infer_for_many([left, right], TE::unsigned_word(None));
                state.infer_for(value, TE::bool());
            }
            // SLT and SGT are numeric and signed, so they are signed numeric
            SVD::SignedLessThan { left, right } | SVD::SignedGreaterThan { left, right } => {
                state.infer_for_many([left, right], TE::signed_word(None));
                state.infer_for(value, TE::bool());
            }
            // Equality can operate over arbitrary words, of any width
            SVD::Equals { left, right } => {
                state.infer_for_many([left, right], TE::bytes(None));
                state.infer_for(value, TE::bool());
            }
            // This is a numeric comparison to zero
            SVD::IsZero { number } => {
                state.infer_for(number, TE::numeric(None));
                state.infer_for(value, TE::bool());
            }
            // These operate over arbitrary words as well
            SVD::And { left, right } | SVD::Or { left, right } | SVD::Xor { left, right } => {
                state.infer_for_many([left, right, value], TE::bytes(None));
            }
            SVD::Not { value: not_val } => {
                state.infer_for_many([value, not_val], TE::bytes(None));
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
            rule::{boolean_operations::BooleanOpsRule, InferenceRule},
            state::InferenceState,
        },
        vm::value::{Provenance, SV, SVD},
    };

    #[test]
    fn creates_correct_equations_for_lt() -> anyhow::Result<()> {
        // Create some values
        let left = SV::new_value(0, Provenance::Synthetic);
        let right = SV::new_value(1, Provenance::Synthetic);
        let operator = SV::new_synthetic(
            2,
            SVD::LessThan {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = InferenceState::empty();
        let [left_tv, right_tv, operator_tv] = state.register_many([left, right, operator.clone()]);
        BooleanOpsRule.infer(&operator, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(right_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bool()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_gt() -> anyhow::Result<()> {
        // Create some values
        let left = SV::new_value(0, Provenance::Synthetic);
        let right = SV::new_value(1, Provenance::Synthetic);
        let operator = SV::new_synthetic(
            2,
            SVD::GreaterThan {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = InferenceState::empty();
        let [left_tv, right_tv, operator_tv] = state.register_many([left, right, operator.clone()]);
        BooleanOpsRule.infer(&operator, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(right_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bool()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_slt() -> anyhow::Result<()> {
        // Create some values
        let left = SV::new_value(0, Provenance::Synthetic);
        let right = SV::new_value(1, Provenance::Synthetic);
        let operator = SV::new_synthetic(
            2,
            SVD::SignedLessThan {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = InferenceState::empty();
        let [left_tv, right_tv, operator_tv] = state.register_many([left, right, operator.clone()]);
        BooleanOpsRule.infer(&operator, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::signed_word(None)));
        assert!(state.inferences(right_tv).contains(&TE::signed_word(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bool()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_sgt() -> anyhow::Result<()> {
        // Create some values
        let left = SV::new_value(0, Provenance::Synthetic);
        let right = SV::new_value(1, Provenance::Synthetic);
        let operator = SV::new_synthetic(
            2,
            SVD::SignedGreaterThan {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = InferenceState::empty();
        let [left_tv, right_tv, operator_tv] = state.register_many([left, right, operator.clone()]);
        BooleanOpsRule.infer(&operator, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::signed_word(None)));
        assert!(state.inferences(right_tv).contains(&TE::signed_word(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bool()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_eq() -> anyhow::Result<()> {
        // Create some values
        let left = SV::new_value(0, Provenance::Synthetic);
        let right = SV::new_value(1, Provenance::Synthetic);
        let operator = SV::new_synthetic(
            2,
            SVD::Equals {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = InferenceState::empty();
        let [left_tv, right_tv, operator_tv] = state.register_many([left, right, operator.clone()]);
        BooleanOpsRule.infer(&operator, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(right_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bool()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_is_zero() -> anyhow::Result<()> {
        // Create some values
        let value = SV::new_value(0, Provenance::Synthetic);
        let operator = SV::new_synthetic(
            2,
            SVD::IsZero {
                number: value.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = InferenceState::empty();
        let [value_tv, operator_tv] = state.register_many([value, operator.clone()]);
        BooleanOpsRule.infer(&operator, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::numeric(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bool()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_and() -> anyhow::Result<()> {
        // Create some values
        let left = SV::new_value(0, Provenance::Synthetic);
        let right = SV::new_value(1, Provenance::Synthetic);
        let operator = SV::new_synthetic(
            2,
            SVD::And {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = InferenceState::empty();
        let [left_tv, right_tv, operator_tv] = state.register_many([left, right, operator.clone()]);
        BooleanOpsRule.infer(&operator, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(right_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bytes(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_or() -> anyhow::Result<()> {
        // Create some values
        let left = SV::new_value(0, Provenance::Synthetic);
        let right = SV::new_value(1, Provenance::Synthetic);
        let operator = SV::new_synthetic(
            2,
            SVD::Or {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = InferenceState::empty();
        let [left_tv, right_tv, operator_tv] = state.register_many([left, right, operator.clone()]);
        BooleanOpsRule.infer(&operator, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(right_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bytes(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_xor() -> anyhow::Result<()> {
        // Create some values
        let left = SV::new_value(0, Provenance::Synthetic);
        let right = SV::new_value(1, Provenance::Synthetic);
        let operator = SV::new_synthetic(
            2,
            SVD::Xor {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = InferenceState::empty();
        let [left_tv, right_tv, operator_tv] = state.register_many([left, right, operator.clone()]);
        BooleanOpsRule.infer(&operator, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(right_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bytes(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_not() -> anyhow::Result<()> {
        // Create some values
        let value = SV::new_value(0, Provenance::Synthetic);
        let operator = SV::new_synthetic(
            2,
            SVD::Not {
                value: value.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = InferenceState::empty();
        let [value_tv, operator_tv] = state.register_many([value, operator.clone()]);
        BooleanOpsRule.infer(&operator, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bytes(None)));

        Ok(())
    }
}
