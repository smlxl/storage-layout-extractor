//! This module contains inference rules that deal with basic arithmetic
//! operations.

use crate::{
    constant::WORD_SIZE_BITS,
    error::unification::Result,
    tc::{expression::TE, rule::InferenceRule, state::TypeCheckerState},
    vm::value::{TCBoxedVal, TCSVD},
};

/// This rule marks the operands and result of the arithmetic operations as
/// being the appropriate type of word.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct ArithmeticOperationRule;

impl InferenceRule for ArithmeticOperationRule {
    fn infer(&self, value: &TCBoxedVal, state: &mut TypeCheckerState) -> Result<()> {
        match value.data() {
            TCSVD::Add { left, right }
            | TCSVD::Multiply { left, right }
            | TCSVD::Subtract { left, right } => {
                state.infer_for_many([value, left, right], TE::numeric(None));
            }
            TCSVD::Divide { dividend, divisor } | TCSVD::Modulo { dividend, divisor } => {
                state.infer_for_many([value, dividend, divisor], TE::unsigned_word(None));
            }
            TCSVD::SignedDivide { dividend, divisor }
            | TCSVD::SignedModulo { dividend, divisor } => {
                state.infer_for_many([value, dividend, divisor], TE::signed_word(None));
            }
            TCSVD::Exp {
                value: exp_val,
                exponent,
            } => {
                state.infer_for_many([value, exp_val, exponent], TE::numeric(None));
            }
            TCSVD::SignExtend {
                value: extend_val,
                size,
            } => {
                state.infer_for(extend_val, TE::signed_word(None));
                state.infer_for(size, TE::unsigned_word(None));

                // If we can unpick the size itself to a known value, we can get a width
                let width = if let TCSVD::KnownData { value } = size.data() {
                    let width: usize = value.into();

                    if width <= WORD_SIZE_BITS {
                        Some(width)
                    } else {
                        None
                    }
                } else {
                    None
                };

                state.infer_for(value, TE::signed_word(width));
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
            rule::{arithmetic_operations::ArithmeticOperationRule, InferenceRule},
            state::TypeCheckerState,
        },
        vm::value::{known::KnownWord, Provenance, RSV, RSVD, TCSVD},
    };

    #[test]
    fn creates_correct_equations_for_add() -> anyhow::Result<()> {
        // Create some values
        let left = RSV::new_value(0, Provenance::Synthetic);
        let right = RSV::new_value(1, Provenance::Synthetic);
        let add = RSV::new_synthetic(
            2,
            RSVD::Add {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Register them with the state and run tc
        let mut state = TypeCheckerState::empty();
        let add_ty = state.register(add);
        let tc_input = state.value_unchecked(add_ty).clone();
        let [left_ty, right_ty] = match tc_input.data() {
            TCSVD::Add { left, right } => [left.type_var(), right.type_var()],
            _ => panic!("Incorrect payload"),
        };
        ArithmeticOperationRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(right_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(add_ty).contains(&TE::numeric(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_multiply() -> anyhow::Result<()> {
        // Create some values
        let left = RSV::new_value(0, Provenance::Synthetic);
        let right = RSV::new_value(1, Provenance::Synthetic);
        let mul = RSV::new_synthetic(
            2,
            RSVD::Multiply {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Register them with the state and run tc
        let mut state = TypeCheckerState::empty();
        let mul_ty = state.register(mul);
        let tc_input = state.value_unchecked(mul_ty).clone();
        let [left_ty, right_ty] = match tc_input.data() {
            TCSVD::Multiply { left, right } => [left.type_var(), right.type_var()],
            _ => panic!("Incorrect payload"),
        };
        ArithmeticOperationRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(right_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(mul_ty).contains(&TE::numeric(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_subtract() -> anyhow::Result<()> {
        // Create some values
        let left = RSV::new_value(0, Provenance::Synthetic);
        let right = RSV::new_value(1, Provenance::Synthetic);
        let sub = RSV::new_synthetic(
            2,
            RSVD::Subtract {
                left:  left.clone(),
                right: right.clone(),
            },
        );

        // Register them with the state and run tc
        let mut state = TypeCheckerState::empty();
        let sub_ty = state.register(sub);
        let tc_input = state.value_unchecked(sub_ty).clone();
        let [left_ty, right_ty] = match tc_input.data() {
            TCSVD::Subtract { left, right } => [left.type_var(), right.type_var()],
            _ => panic!("Incorrect payload"),
        };
        ArithmeticOperationRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(right_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(sub_ty).contains(&TE::numeric(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_divide() -> anyhow::Result<()> {
        // Create some values
        let dividend = RSV::new_value(0, Provenance::Synthetic);
        let divisor = RSV::new_value(1, Provenance::Synthetic);
        let div = RSV::new_synthetic(
            2,
            RSVD::Divide {
                dividend: dividend.clone(),
                divisor:  divisor.clone(),
            },
        );

        // Register them with the state and run tc
        let mut state = TypeCheckerState::empty();
        let div_ty = state.register(div);
        let tc_input = state.value_unchecked(div_ty).clone();
        let [dividend_ty, divisor_ty] = match tc_input.data() {
            TCSVD::Divide { dividend, divisor } => [dividend.type_var(), divisor.type_var()],
            _ => panic!("Incorrect payload"),
        };
        ArithmeticOperationRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(dividend_ty).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(divisor_ty).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(div_ty).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_signed_divide() -> anyhow::Result<()> {
        // Create some values
        let dividend = RSV::new_value(0, Provenance::Synthetic);
        let divisor = RSV::new_value(1, Provenance::Synthetic);
        let div = RSV::new_synthetic(
            2,
            RSVD::SignedDivide {
                dividend: dividend.clone(),
                divisor:  divisor.clone(),
            },
        );

        // Register them with the state and run tc
        let mut state = TypeCheckerState::empty();
        let div_ty = state.register(div);
        let tc_input = state.value_unchecked(div_ty).clone();
        let [dividend_ty, divisor_ty] = match tc_input.data() {
            TCSVD::SignedDivide { dividend, divisor } => [dividend.type_var(), divisor.type_var()],
            _ => panic!("Incorrect payload"),
        };
        ArithmeticOperationRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(dividend_ty).contains(&TE::signed_word(None)));
        assert!(state.inferences(divisor_ty).contains(&TE::signed_word(None)));
        assert!(state.inferences(div_ty).contains(&TE::signed_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_modulo() -> anyhow::Result<()> {
        // Create some values
        let dividend = RSV::new_value(0, Provenance::Synthetic);
        let divisor = RSV::new_value(1, Provenance::Synthetic);
        let modulo = RSV::new_synthetic(
            2,
            RSVD::Modulo {
                dividend: dividend.clone(),
                divisor:  divisor.clone(),
            },
        );

        // Register them with the state and run tc
        let mut state = TypeCheckerState::empty();
        let div_ty = state.register(modulo);
        let tc_input = state.value_unchecked(div_ty).clone();
        let [dividend_ty, divisor_ty] = match tc_input.data() {
            TCSVD::Modulo { dividend, divisor } => [dividend.type_var(), divisor.type_var()],
            _ => panic!("Incorrect payload"),
        };
        ArithmeticOperationRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(dividend_ty).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(divisor_ty).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(div_ty).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_signed_modulo() -> anyhow::Result<()> {
        // Create some values
        let dividend = RSV::new_value(0, Provenance::Synthetic);
        let divisor = RSV::new_value(1, Provenance::Synthetic);
        let modulo = RSV::new_synthetic(
            2,
            RSVD::SignedModulo {
                dividend: dividend.clone(),
                divisor:  divisor.clone(),
            },
        );

        // Register them with the state and run tc
        let mut state = TypeCheckerState::empty();
        let div_ty = state.register(modulo);
        let tc_input = state.value_unchecked(div_ty).clone();
        let [dividend_ty, divisor_ty] = match tc_input.data() {
            TCSVD::SignedModulo { dividend, divisor } => [dividend.type_var(), divisor.type_var()],
            _ => panic!("Incorrect payload"),
        };
        ArithmeticOperationRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(dividend_ty).contains(&TE::signed_word(None)));
        assert!(state.inferences(divisor_ty).contains(&TE::signed_word(None)));
        assert!(state.inferences(div_ty).contains(&TE::signed_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_exp() -> anyhow::Result<()> {
        // Create some values
        let value = RSV::new_value(0, Provenance::Synthetic);
        let exponent = RSV::new_value(1, Provenance::Synthetic);
        let exp = RSV::new_synthetic(
            2,
            RSVD::Exp {
                value:    value.clone(),
                exponent: exponent.clone(),
            },
        );

        // Register them with the state and run tc
        let mut state = TypeCheckerState::empty();
        let exp_ty = state.register(exp);
        let tc_input = state.value_unchecked(exp_ty).clone();
        let [value_ty, exponent_ty] = match tc_input.data() {
            TCSVD::Exp { value, exponent } => [value.type_var(), exponent.type_var()],
            _ => panic!("Incorrect payload"),
        };
        ArithmeticOperationRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(value_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(exponent_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(exp_ty).contains(&TE::numeric(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_sign_extend_with_known_size() -> anyhow::Result<()> {
        // Create some values
        let value = RSV::new_value(0, Provenance::Synthetic);
        let size = RSV::new_known_value(1, KnownWord::from(128), Provenance::Synthetic, None);
        let ext = RSV::new_synthetic(
            2,
            RSVD::SignExtend {
                value: value.clone(),
                size:  size.clone(),
            },
        );

        // Register them with the state and run tc
        let mut state = TypeCheckerState::empty();
        let ext_ty = state.register(ext.clone());
        let tc_input = state.value_unchecked(ext_ty).clone();
        let [value_ty, size_ty] = match tc_input.data() {
            TCSVD::SignExtend { value, size } => [value.type_var(), size.type_var()],
            _ => panic!("Incorrect payload"),
        };
        ArithmeticOperationRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(value_ty).contains(&TE::signed_word(None)));
        assert!(state.inferences(size_ty).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(ext_ty).contains(&TE::signed_word(Some(128))));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_sign_extend_with_unknown_size() -> anyhow::Result<()> {
        // Create some values
        let value = RSV::new_value(0, Provenance::Synthetic);
        let size = RSV::new_value(1, Provenance::Synthetic);
        let ext = RSV::new_synthetic(
            2,
            RSVD::SignExtend {
                value: value.clone(),
                size:  size.clone(),
            },
        );

        // Register them with the state and run tc
        let mut state = TypeCheckerState::empty();
        let ext_ty = state.register(ext.clone());
        let tc_input = state.value_unchecked(ext_ty).clone();
        let [value_ty, size_ty] = match tc_input.data() {
            TCSVD::SignExtend { value, size } => [value.type_var(), size.type_var()],
            _ => panic!("Incorrect payload"),
        };
        ArithmeticOperationRule.infer(&tc_input, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(value_ty).contains(&TE::signed_word(None)));
        assert!(state.inferences(size_ty).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(ext_ty).contains(&TE::signed_word(None)));

        Ok(())
    }
}
