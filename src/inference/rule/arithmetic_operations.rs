//! This module contains inference rules that deal with basic arithmetic
//! operations.

use crate::{
    constant::WORD_SIZE_BITS,
    error::unification::Result,
    inference::{expression::TE, rule::InferenceRule, state::InferenceState},
    vm::value::{BoxedVal, SVD},
};

/// This rule marks the operands and result of the arithmetic operations as
/// being the appropriate type of word.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct ArithmeticOperationRule;

impl InferenceRule for ArithmeticOperationRule {
    fn infer(&self, value: &BoxedVal, state: &mut InferenceState) -> Result<()> {
        match &value.data {
            SVD::Add { left, right }
            | SVD::Multiply { left, right }
            | SVD::Subtract { left, right } => {
                state.infer_for_many([value, left, right], TE::numeric(None));
            }
            SVD::Divide { dividend, divisor } | SVD::Modulo { dividend, divisor } => {
                state.infer_for_many([value, dividend, divisor], TE::unsigned_word(None));
            }
            SVD::SignedDivide { dividend, divisor } | SVD::SignedModulo { dividend, divisor } => {
                state.infer_for_many([value, dividend, divisor], TE::signed_word(None));
            }
            SVD::Exp {
                value: exp_val,
                exponent,
            } => {
                state.infer_for_many([value, exp_val, exponent], TE::numeric(None));
            }
            SVD::SignExtend {
                value: extend_val,
                size,
            } => {
                state.infer_for(extend_val, TE::signed_word(None));
                state.infer_for(size, TE::unsigned_word(None));

                // If we can unpick the size itself to a known value, we can get a width
                let width = if let SVD::KnownData { value } = &size.data {
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
        inference::{
            expression::TE,
            rule::{arithmetic_operations::ArithmeticOperationRule, InferenceRule},
            state::InferenceState,
        },
        vm::value::{known::KnownWord, Provenance, SV, SVD},
    };

    #[test]
    fn creates_correct_equations_for_add() -> anyhow::Result<()> {
        // Create some values
        let left = SV::new_value(0, Provenance::Synthetic);
        let right = SV::new_value(1, Provenance::Synthetic);
        let add = SV::new(
            2,
            SVD::Add {
                left:  left.clone(),
                right: right.clone(),
            },
            Provenance::Synthetic,
        );

        // Register them with the state and run inference
        let mut state = InferenceState::empty();
        let [left_ty, right_ty, add_ty] = state.register_many([left, right, add.clone()]);
        ArithmeticOperationRule.infer(&add, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(right_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(add_ty).contains(&TE::numeric(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_multiply() -> anyhow::Result<()> {
        // Create some values
        let left = SV::new_value(0, Provenance::Synthetic);
        let right = SV::new_value(1, Provenance::Synthetic);
        let mul = SV::new(
            2,
            SVD::Add {
                left:  left.clone(),
                right: right.clone(),
            },
            Provenance::Synthetic,
        );

        // Register them with the state and run inference
        let mut state = InferenceState::empty();
        let [left_ty, right_ty, mul_ty] = state.register_many([left, right, mul.clone()]);
        ArithmeticOperationRule.infer(&mul, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(right_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(mul_ty).contains(&TE::numeric(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_subtract() -> anyhow::Result<()> {
        // Create some values
        let left = SV::new_value(0, Provenance::Synthetic);
        let right = SV::new_value(1, Provenance::Synthetic);
        let sub = SV::new(
            2,
            SVD::Add {
                left:  left.clone(),
                right: right.clone(),
            },
            Provenance::Synthetic,
        );

        // Register them with the state and run inference
        let mut state = InferenceState::empty();
        let [left_ty, right_ty, sub_ty] = state.register_many([left, right, sub.clone()]);
        ArithmeticOperationRule.infer(&sub, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(left_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(right_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(sub_ty).contains(&TE::numeric(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_divide() -> anyhow::Result<()> {
        // Create some values
        let dividend = SV::new_value(0, Provenance::Synthetic);
        let divisor = SV::new_value(1, Provenance::Synthetic);
        let div = SV::new(
            2,
            SVD::Divide {
                dividend: dividend.clone(),
                divisor:  divisor.clone(),
            },
            Provenance::Synthetic,
        );

        // Register them with the state and run inference
        let mut state = InferenceState::empty();
        let [dividend_ty, divisor_ty, div_ty] =
            state.register_many([dividend, divisor, div.clone()]);
        ArithmeticOperationRule.infer(&div, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(dividend_ty).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(divisor_ty).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(div_ty).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_signed_divide() -> anyhow::Result<()> {
        // Create some values
        let dividend = SV::new_value(0, Provenance::Synthetic);
        let divisor = SV::new_value(1, Provenance::Synthetic);
        let div = SV::new(
            2,
            SVD::SignedDivide {
                dividend: dividend.clone(),
                divisor:  divisor.clone(),
            },
            Provenance::Synthetic,
        );

        // Register them with the state and run inference
        let mut state = InferenceState::empty();
        let [dividend_ty, divisor_ty, div_ty] =
            state.register_many([dividend, divisor, div.clone()]);
        ArithmeticOperationRule.infer(&div, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(dividend_ty).contains(&TE::signed_word(None)));
        assert!(state.inferences(divisor_ty).contains(&TE::signed_word(None)));
        assert!(state.inferences(div_ty).contains(&TE::signed_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_modulo() -> anyhow::Result<()> {
        // Create some values
        let dividend = SV::new_value(0, Provenance::Synthetic);
        let divisor = SV::new_value(1, Provenance::Synthetic);
        let modulo = SV::new(
            2,
            SVD::Modulo {
                dividend: dividend.clone(),
                divisor:  divisor.clone(),
            },
            Provenance::Synthetic,
        );

        // Register them with the state and run inference
        let mut state = InferenceState::empty();
        let [dividend_ty, divisor_ty, div_ty] =
            state.register_many([dividend, divisor, modulo.clone()]);
        ArithmeticOperationRule.infer(&modulo, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(dividend_ty).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(divisor_ty).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(div_ty).contains(&TE::unsigned_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_signed_modulo() -> anyhow::Result<()> {
        // Create some values
        let dividend = SV::new_value(0, Provenance::Synthetic);
        let divisor = SV::new_value(1, Provenance::Synthetic);
        let modulo = SV::new(
            2,
            SVD::SignedModulo {
                dividend: dividend.clone(),
                divisor:  divisor.clone(),
            },
            Provenance::Synthetic,
        );

        // Register them with the state and run inference
        let mut state = InferenceState::empty();
        let [dividend_ty, divisor_ty, div_ty] =
            state.register_many([dividend, divisor, modulo.clone()]);
        ArithmeticOperationRule.infer(&modulo, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(dividend_ty).contains(&TE::signed_word(None)));
        assert!(state.inferences(divisor_ty).contains(&TE::signed_word(None)));
        assert!(state.inferences(div_ty).contains(&TE::signed_word(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_exp() -> anyhow::Result<()> {
        // Create some values
        let value = SV::new_value(0, Provenance::Synthetic);
        let exponent = SV::new_value(1, Provenance::Synthetic);
        let exp = SV::new(
            2,
            SVD::Exp {
                value:    value.clone(),
                exponent: exponent.clone(),
            },
            Provenance::Synthetic,
        );

        // Register them with the state and run inference
        let mut state = InferenceState::empty();
        let [value_ty, exponent_ty, exp_ty] = state.register_many([value, exponent, exp.clone()]);
        ArithmeticOperationRule.infer(&exp, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(value_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(exponent_ty).contains(&TE::numeric(None)));
        assert!(state.inferences(exp_ty).contains(&TE::numeric(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_sign_extend_with_known_size() -> anyhow::Result<()> {
        // Create some values
        let value = SV::new_value(0, Provenance::Synthetic);
        let size = SV::new_known_value(1, KnownWord::from(128), Provenance::Synthetic);
        let ext = SV::new(
            2,
            SVD::SignExtend {
                value: value.clone(),
                size:  size.clone(),
            },
            Provenance::Synthetic,
        );

        // Register them with the state and run inference
        let mut state = InferenceState::empty();
        let [value_ty, size_ty, ext_ty] = state.register_many([value, size, ext.clone()]);
        ArithmeticOperationRule.infer(&ext, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(value_ty).contains(&TE::signed_word(None)));
        assert!(state.inferences(size_ty).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(ext_ty).contains(&TE::signed_word(Some(128))));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_sign_extend_with_unknown_size() -> anyhow::Result<()> {
        // Create some values
        let value = SV::new_value(0, Provenance::Synthetic);
        let size = SV::new_value(1, Provenance::Synthetic);
        let ext = SV::new(
            2,
            SVD::SignExtend {
                value: value.clone(),
                size:  size.clone(),
            },
            Provenance::Synthetic,
        );

        // Register them with the state and run inference
        let mut state = InferenceState::empty();
        let [value_ty, size_ty, ext_ty] = state.register_many([value, size, ext.clone()]);
        ArithmeticOperationRule.infer(&ext, &mut state)?;

        // Check we get the right equations
        assert!(state.inferences(value_ty).contains(&TE::signed_word(None)));
        assert!(state.inferences(size_ty).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(ext_ty).contains(&TE::signed_word(None)));

        Ok(())
    }
}
