//! This module contains an inference rule for dealing with the bit shift
//! operations.

use crate::{
    error::unification::Result,
    tc::{expression::TE, rule::InferenceRule, state::TypeCheckerState},
    vm::value::{TCBoxedVal, TCSVD},
};

/// This inference rule is able to say that the shift amount is always unsigned,
/// and depending on the kind of shift we may know that the value being shifted
/// is signed or not.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct BitShiftRule;

impl InferenceRule for BitShiftRule {
    fn infer(&self, value: &TCBoxedVal, state: &mut TypeCheckerState) -> Result<()> {
        match value.data() {
            TCSVD::LeftShift {
                shift,
                value: shift_val,
            }
            | TCSVD::RightShift {
                shift,
                value: shift_val,
            } => {
                // The shift amount is always interpreted as unsigned
                state.infer_for(shift, TE::unsigned_word(None));

                // We know little about the result of a normal bit shift or the value
                state.infer_for_many([value, shift_val], TE::bytes(None));
            }
            TCSVD::ArithmeticRightShift {
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
        tc::{
            expression::TE,
            rule::{bit_shifts::BitShiftRule, InferenceRule},
            state::TypeCheckerState,
        },
        vm::value::{Provenance, RSV, RSVD, TCSVD},
    };

    #[test]
    fn creates_correct_equations_for_left_shift() -> anyhow::Result<()> {
        // Create some values
        let value = RSV::new_value(0, Provenance::Synthetic);
        let shift_amount = RSV::new_value(1, Provenance::Synthetic);
        let shift = RSV::new_synthetic(
            2,
            RSVD::LeftShift {
                shift: shift_amount.clone(),
                value: value.clone(),
            },
        );

        // Create the state and run the inference rule
        let mut state = TypeCheckerState::empty();
        let shift_tv = state.register(shift);
        let tc_input = state.value_unchecked(shift_tv).clone();
        let [value_tv, shift_amount_tv] = match tc_input.data() {
            TCSVD::LeftShift { value, shift } => [value.type_var(), shift.type_var()],
            _ => panic!("Incorrect payload"),
        };
        BitShiftRule.infer(&tc_input, &mut state)?;

        // Check we get the expected equations
        assert!(state.inferences(value_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(shift_amount_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(shift_tv).contains(&TE::bytes(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_right_shift() -> anyhow::Result<()> {
        // Create some values
        let value = RSV::new_value(0, Provenance::Synthetic);
        let shift_amount = RSV::new_value(1, Provenance::Synthetic);
        let shift = RSV::new_synthetic(
            2,
            RSVD::RightShift {
                shift: shift_amount.clone(),
                value: value.clone(),
            },
        );

        // Create the state and run the inference rule
        let mut state = TypeCheckerState::empty();
        let shift_tv = state.register(shift);
        let tc_input = state.value_unchecked(shift_tv).clone();
        let [value_tv, shift_amount_tv] = match tc_input.data() {
            TCSVD::RightShift { value, shift } => [value.type_var(), shift.type_var()],
            _ => panic!("Incorrect payload"),
        };
        BitShiftRule.infer(&tc_input, &mut state)?;

        // Check we get the expected equations
        assert!(state.inferences(value_tv).contains(&TE::bytes(None)));
        assert!(state.inferences(shift_amount_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(shift_tv).contains(&TE::bytes(None)));

        Ok(())
    }

    #[test]
    fn creates_correct_equations_for_arithmetic_right_shift() -> anyhow::Result<()> {
        // Create some values
        let value = RSV::new_value(0, Provenance::Synthetic);
        let shift_amount = RSV::new_value(1, Provenance::Synthetic);
        let shift = RSV::new_synthetic(
            2,
            RSVD::ArithmeticRightShift {
                shift: shift_amount.clone(),
                value: value.clone(),
            },
        );

        // Create the state and run the inference rule
        let mut state = TypeCheckerState::empty();
        let shift_tv = state.register(shift);
        let tc_input = state.value_unchecked(shift_tv).clone();
        let [value_tv, shift_amount_tv] = match tc_input.data() {
            TCSVD::ArithmeticRightShift { value, shift } => [value.type_var(), shift.type_var()],
            _ => panic!("Incorrect payload"),
        };
        BitShiftRule.infer(&tc_input, &mut state)?;

        // Check we get the expected equations
        assert!(state.inferences(value_tv).contains(&TE::signed_word(None)));
        assert!(state.inferences(shift_amount_tv).contains(&TE::unsigned_word(None)));
        assert!(state.inferences(shift_tv).contains(&TE::signed_word(None)));

        Ok(())
    }
}
