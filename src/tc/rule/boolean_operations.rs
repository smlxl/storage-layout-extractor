//! This module defines basic inferences for the set of boolean operations that
//! can be performed on the EVM.

use crate::{
    error::unification::Result,
    tc::{expression::TE, rule::InferenceRule, state::TypeCheckerState},
    vm::value::{TCBoxedVal, TCSVD},
};

/// This rule is responsible for making inferences based on the presence of
/// boolean operations.
///
/// Unfortunately, many boolean operations do not tell us much as they operate
/// bitwise, but we can usually say that the operands are some kind of word.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct BooleanOpsRule;

impl InferenceRule for BooleanOpsRule {
    fn infer(&self, value: &TCBoxedVal, state: &mut TypeCheckerState) -> Result<()> {
        match value.data() {
            // LT and GT are numeric comparisons, so we know that the operands are numeric, and not
            // treated as signed
            TCSVD::LessThan { left, right } | TCSVD::GreaterThan { left, right } => {
                state.infer_for_many([left, right], TE::unsigned_word(None));
                state.infer_for(value, TE::bool());
            }
            // SLT and SGT are numeric and signed, so they are signed numeric
            TCSVD::SignedLessThan { left, right } | TCSVD::SignedGreaterThan { left, right } => {
                state.infer_for_many([left, right], TE::signed_word(None));
                state.infer_for(value, TE::bool());
            }
            // Equality can operate over arbitrary words, of any width
            TCSVD::Equals { left, right } => {
                state.infer_for_many([left, right], TE::bytes(None));
                state.infer_for(value, TE::bool());
            }
            // This is a numeric comparison to zero
            TCSVD::IsZero { number } => {
                state.infer_for(number, TE::numeric(None));
                state.infer_for(value, TE::bool());
            }
            // These operate over arbitrary words as well
            TCSVD::And { left, right } | TCSVD::Or { left, right } | TCSVD::Xor { left, right } => {
                state.infer_for_many([left, right, value], TE::bytes(None));
            }
            TCSVD::Not { value: not_val } => {
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
        tc::{
            expression::TE,
            rule::{boolean_operations::BooleanOpsRule, InferenceRule},
            state::TypeCheckerState,
        },
        vm::value::{Provenance, RSV, RSVD, TCSVD},
    };

    #[test]
    fn creates_correct_equations_for_lt() -> anyhow::Result<()> {
        // Create some values
        let left = RSV::new_value(0, Provenance::Synthetic);
        let right = RSV::new_value(1, Provenance::Synthetic);
        let operator = RSV::new_synthetic(
            2,
            RSVD::LessThan {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = TypeCheckerState::empty();
        let operator_tv = state.register(operator);
        let tc_input = state.value_unchecked(operator_tv).clone();
        let [left_tv, right_tv] = match tc_input.data() {
            TCSVD::LessThan { left, right } => [left.type_var(), right.type_var()],
            _ => panic!("Incorrect payload"),
        };
        BooleanOpsRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(right_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bool()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_gt() -> anyhow::Result<()> {
        // Create some values
        let left = RSV::new_value(0, Provenance::Synthetic);
        let right = RSV::new_value(1, Provenance::Synthetic);
        let operator = RSV::new_synthetic(
            2,
            RSVD::GreaterThan {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = TypeCheckerState::empty();
        let operator_tv = state.register(operator);
        let tc_input = state.value_unchecked(operator_tv).clone();
        let [left_tv, right_tv] = match tc_input.data() {
            TCSVD::GreaterThan { left, right } => [left.type_var(), right.type_var()],
            _ => panic!("Incorrect payload"),
        };
        BooleanOpsRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(right_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bool()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_slt() -> anyhow::Result<()> {
        // Create some values
        let left = RSV::new_value(0, Provenance::Synthetic);
        let right = RSV::new_value(1, Provenance::Synthetic);
        let operator = RSV::new_synthetic(
            2,
            RSVD::SignedLessThan {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = TypeCheckerState::empty();
        let operator_tv = state.register(operator);
        let tc_input = state.value_unchecked(operator_tv).clone();
        let [left_tv, right_tv] = match tc_input.data() {
            TCSVD::SignedLessThan { left, right } => [left.type_var(), right.type_var()],
            _ => panic!("Incorrect payload"),
        };
        BooleanOpsRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::signed_word(None)));
        assert!(state.inferences(right_tv).contains(&TE::signed_word(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bool()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_sgt() -> anyhow::Result<()> {
        // Create some values
        let left = RSV::new_value(0, Provenance::Synthetic);
        let right = RSV::new_value(1, Provenance::Synthetic);
        let operator = RSV::new_synthetic(
            2,
            RSVD::SignedGreaterThan {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = TypeCheckerState::empty();
        let operator_tv = state.register(operator);
        let tc_input = state.value_unchecked(operator_tv).clone();
        let [left_tv, right_tv] = match tc_input.data() {
            TCSVD::SignedGreaterThan { left, right } => [left.type_var(), right.type_var()],
            _ => panic!("Incorrect payload"),
        };
        BooleanOpsRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::signed_word(None)));
        assert!(state.inferences(right_tv).contains(&TE::signed_word(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bool()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_eq() -> anyhow::Result<()> {
        // Create some values
        let left = RSV::new_value(0, Provenance::Synthetic);
        let right = RSV::new_value(1, Provenance::Synthetic);
        let operator = RSV::new_synthetic(
            2,
            RSVD::Equals {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = TypeCheckerState::empty();
        let operator_tv = state.register(operator);
        let tc_input = state.value_unchecked(operator_tv).clone();
        let [left_tv, right_tv] = match tc_input.data() {
            TCSVD::Equals { left, right } => [left.type_var(), right.type_var()],
            _ => panic!("Incorrect payload"),
        };
        BooleanOpsRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(right_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bool()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_is_zero() -> anyhow::Result<()> {
        // Create some values
        let value = RSV::new_value(0, Provenance::Synthetic);
        let operator = RSV::new_synthetic(
            2,
            RSVD::IsZero {
                number: value.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = TypeCheckerState::empty();
        let operator_tv = state.register(operator);
        let tc_input = state.value_unchecked(operator_tv).clone();
        let value_tv = match tc_input.data() {
            TCSVD::IsZero { number } => number.type_var(),
            _ => panic!("Incorrect payload"),
        };
        BooleanOpsRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::numeric(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bool()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_and() -> anyhow::Result<()> {
        // Create some values
        let left = RSV::new_value(0, Provenance::Synthetic);
        let right = RSV::new_value(1, Provenance::Synthetic);
        let operator = RSV::new_synthetic(
            2,
            RSVD::And {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = TypeCheckerState::empty();
        let operator_tv = state.register(operator);
        let tc_input = state.value_unchecked(operator_tv).clone();
        let [left_tv, right_tv] = match tc_input.data() {
            TCSVD::And { left, right } => [left.type_var(), right.type_var()],
            _ => panic!("Incorrect payload"),
        };
        BooleanOpsRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(right_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bytes(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_or() -> anyhow::Result<()> {
        // Create some values
        let left = RSV::new_value(0, Provenance::Synthetic);
        let right = RSV::new_value(1, Provenance::Synthetic);
        let operator = RSV::new_synthetic(
            2,
            RSVD::Or {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = TypeCheckerState::empty();
        let operator_tv = state.register(operator);
        let tc_input = state.value_unchecked(operator_tv).clone();
        let [left_tv, right_tv] = match tc_input.data() {
            TCSVD::Or { left, right } => [left.type_var(), right.type_var()],
            _ => panic!("Incorrect payload"),
        };
        BooleanOpsRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(right_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bytes(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_xor() -> anyhow::Result<()> {
        // Create some values
        let left = RSV::new_value(0, Provenance::Synthetic);
        let right = RSV::new_value(1, Provenance::Synthetic);
        let operator = RSV::new_synthetic(
            2,
            RSVD::Xor {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = TypeCheckerState::empty();
        let operator_tv = state.register(operator);
        let tc_input = state.value_unchecked(operator_tv).clone();
        let [left_tv, right_tv] = match tc_input.data() {
            TCSVD::Xor { left, right } => [left.type_var(), right.type_var()],
            _ => panic!("Incorrect payload"),
        };
        BooleanOpsRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(right_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bytes(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_not() -> anyhow::Result<()> {
        // Create some values
        let value = RSV::new_value(0, Provenance::Synthetic);
        let operator = RSV::new_synthetic(
            2,
            RSVD::Not {
                value: value.clone(),
            },
        );

        // Create the state and run the rule
        let mut state = TypeCheckerState::empty();
        let operator_tv = state.register(operator);
        let tc_input = state.value_unchecked(operator_tv).clone();
        let value_tv = match tc_input.data() {
            TCSVD::Not { value } => value.type_var(),
            _ => panic!("Incorrect payload"),
        };
        BooleanOpsRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(value_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(operator_tv).contains(&TE::bytes(None)));

        Ok(())
    }
}
