//! This module contains an inference rule for dealing with the bit shift
//! operations.

use crate::{
    unifier::{expression::TE, inference_rule::InferenceRule, state::TypingState},
    vm::value::{BoxedVal, SVD},
};

/// This inference rule is able to say that the shift amount is always unsigned,
/// and depending on the kind of shift we may know that the value being shifted
/// is signed or not.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct BitShiftRule;

impl InferenceRule for BitShiftRule {
    fn infer(
        &self,
        value: &BoxedVal,
        state: &mut TypingState,
    ) -> crate::error::unification::Result<()> {
        match &value.data {
            SVD::LeftShift {
                shift,
                value: shift_val,
            }
            | SVD::RightShift {
                shift,
                value: shift_val,
            } => {
                // The shift amount is always interpreted as unsigned
                state.infer_for(shift, TE::unsigned_word(None));

                // We know nothing about the result of a normal bit shift or the value
                state.infer_for_many([value, shift_val], TE::default_word());
            }
            SVD::ArithmeticRightShift {
                shift,
                value: shift_val,
            } => {
                // The shift amount is always interpreted as unsigned
                state.infer_for(shift, TE::unsigned_word(None));

                // But here as it is an arithmetic shift, the value being shifted is being
                // treated as signed, and hence so is the result
                state.infer_for_many([value, shift_val], TE::signed_word(None));
            }
            _ => (),
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        unifier::{
            expression::TE,
            inference_rule::{bit_shifts::BitShiftRule, InferenceRule},
            state::TypingState,
        },
        vm::value::{Provenance, SV, SVD},
    };

    #[test]
    fn creates_correct_equations_for_left_shift() -> anyhow::Result<()> {
        // Create some values
        let value = SV::new_value(0, Provenance::Synthetic);
        let shift_amount = SV::new_value(1, Provenance::Synthetic);
        let shift = SV::new_synthetic(
            2,
            SVD::LeftShift {
                shift: shift_amount.clone(),
                value: value.clone(),
            },
        );

        // Create the state and run the inference rule
        let mut state = TypingState::empty();
        let [value_tv, shift_amount_tv, shift_tv] =
            state.register_many([value, shift_amount, shift.clone()]);
        BitShiftRule.infer(&shift, &mut state)?;

        // Check we get the expected equations
        assert!(state.inferences(value_tv).contains(&TE::default_word()));
        assert!(state.inferences(shift_amount_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(shift_tv).contains(&TE::default_word()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_right_shift() -> anyhow::Result<()> {
        // Create some values
        let value = SV::new_value(0, Provenance::Synthetic);
        let shift_amount = SV::new_value(1, Provenance::Synthetic);
        let shift = SV::new_synthetic(
            2,
            SVD::RightShift {
                shift: shift_amount.clone(),
                value: value.clone(),
            },
        );

        // Create the state and run the inference rule
        let mut state = TypingState::empty();
        let [value_tv, shift_amount_tv, shift_tv] =
            state.register_many([value, shift_amount, shift.clone()]);
        BitShiftRule.infer(&shift, &mut state)?;

        // Check we get the expected equations
        assert!(state.inferences(value_tv).contains(&TE::default_word()));
        assert!(state.inferences(shift_amount_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(shift_tv).contains(&TE::default_word()));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_arithmetic_right_shift() -> anyhow::Result<()> {
        // Create some values
        let value = SV::new_value(0, Provenance::Synthetic);
        let shift_amount = SV::new_value(1, Provenance::Synthetic);
        let shift = SV::new_synthetic(
            2,
            SVD::ArithmeticRightShift {
                shift: shift_amount.clone(),
                value: value.clone(),
            },
        );

        // Create the state and run the inference rule
        let mut state = TypingState::empty();
        let [value_tv, shift_amount_tv, shift_tv] =
            state.register_many([value, shift_amount, shift.clone()]);
        BitShiftRule.infer(&shift, &mut state)?;

        // Check we get the expected equations
        assert!(state.inferences(value_tv).contains(&TE::signed_word(None)));
        assert!(state.inferences(shift_amount_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(shift_tv).contains(&TE::signed_word(None)));

        Ok(())
    }
}
