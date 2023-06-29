//! This lifting pass looks for operations that mask values to a well-defined
//! length or sub-values, as these can be used to infer the width of a value.

use crate::{
    inference::{lift::Lift, state::InferenceState},
    vm::value::{BoxedVal, SVD},
};

/// This pass detects and folds expressions that mask word-size values.
///
/// These have a form as follows:
///
/// ```code
/// value & ((1 << shift) - 1)
///
/// becomes
///
/// mask(value, mask)
/// ```
///
/// where:
/// - The operands to `&` may be flipped as the operator is symmetric.
/// - The `((1 << shift) - 1)` mask may be constant-folded.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MaskWord;

impl MaskWord {
    /// Constructs a new instance of the word mask lifting pass.
    #[must_use]
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }
}

impl Lift for MaskWord {
    fn run(
        &mut self,
        value: BoxedVal,
        _state: &InferenceState,
    ) -> crate::error::unification::Result<BoxedVal> {
        fn mask_arg(data: &SVD) -> Option<usize> {
            // If there is a known data as the operand, and it hasn't been constant folded,
            // we know that the mask itself _has_ been, so we just return it.
            if let SVD::KnownData { value } = data {
                return Some(usize::from(value));
            }

            let SVD::Subtract { left, right } = data else {
                return None;
            };
            let SVD::LeftShift { shift, value } = &left.data else {
                return None;
            };
            let SVD::KnownData {
                value: subtracted_value,
            } = &right.data
            else {
                return None;
            };
            let SVD::KnownData {
                value: shift_amount,
            } = &shift.data
            else {
                return None;
            };
            let SVD::KnownData {
                value: shifted_value,
            } = &value.data
            else {
                return None;
            };

            if usize::from(subtracted_value) == 1 && usize::from(shifted_value) == 1 {
                Some(usize::from(shift_amount))
            } else {
                None
            }
        }

        fn insert_masks(data: &SVD) -> Option<SVD> {
            let SVD::And { left, right } = data else {
                return None;
            };

            if let Some(mask_size) = mask_arg(&left.data) {
                Some(SVD::WordMask {
                    value: right.clone().transform_data(insert_masks),
                    mask:  mask_size,
                })
            } else {
                mask_arg(&right.data).map(|mask_size| SVD::WordMask {
                    value: left.clone().transform_data(insert_masks),
                    mask:  mask_size,
                })
            }
        }

        Ok(value.transform_data(insert_masks))
    }
}

#[cfg(test)]
mod test {
    use crate::{
        inference::{
            lift::{mask_word::MaskWord, Lift},
            state::InferenceState,
        },
        vm::value::{known::KnownWord, Provenance, SymbolicValue, SymbolicValueData, SVD},
    };

    #[test]
    fn resolves_word_masks_at_top_level() -> anyhow::Result<()> {
        let one = SymbolicValue::new_known_value(0, KnownWord::from(1), Provenance::Synthetic);
        let shift_amount =
            SymbolicValue::new_known_value(1, KnownWord::from(12), Provenance::Synthetic);
        let shift = SymbolicValue::new(
            2,
            SymbolicValueData::LeftShift {
                value: one.clone(),
                shift: shift_amount,
            },
            Provenance::Synthetic,
        );
        let subtract = SymbolicValue::new(
            3,
            SymbolicValueData::Subtract {
                left:  shift,
                right: one,
            },
            Provenance::Synthetic,
        );
        let input_value = SymbolicValue::new_value(4, Provenance::Synthetic);
        let and = SymbolicValue::new(
            4,
            SymbolicValueData::And {
                left:  input_value.clone(),
                right: subtract,
            },
            Provenance::Synthetic,
        );

        let state = InferenceState::empty();
        let result = MaskWord.run(and, &state)?;

        match &result.data {
            SVD::WordMask { value, mask } => {
                assert_eq!(value, &input_value);
                assert_eq!(*mask, 12usize);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn resolves_word_masks_with_constant_masks() -> anyhow::Result<()> {
        let input_value = SymbolicValue::new_value(4, Provenance::Synthetic);
        let input_mask = SymbolicValue::new_known_value(
            0,
            KnownWord::from(0x0000_ffff_0000),
            Provenance::Synthetic,
        );
        let and = SymbolicValue::new(
            4,
            SymbolicValueData::And {
                left:  input_mask,
                right: input_value.clone(),
            },
            Provenance::Synthetic,
        );

        let state = InferenceState::empty();
        let result = MaskWord.run(and, &state)?;

        match &result.data {
            SVD::WordMask { value, mask } => {
                assert_eq!(value, &input_value);
                assert_eq!(*mask, 0x0000_ffff_0000);
            }
            _ => panic!("Incorrect payload"),
        };

        Ok(())
    }
}
