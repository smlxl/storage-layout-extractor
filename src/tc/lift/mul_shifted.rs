//! This module contains the definition of a lifting pass that looks for
//! multiplication-based shifting of bits around within a word.

use crate::{
    constant::WORD_SIZE_BITS,
    tc::{lift::Lift, state::TypeCheckerState},
    vm::value::{known::KnownWord, RuntimeBoxedVal, RSVD},
};

/// This pass detects and lifts expressions that move values around inside a
/// word through multiplicative shifts.
///
/// These have a form as follows:
///
/// ```text
/// constant * sub_word(value, offset, size)
///
/// becomes
///
/// shifted(constant, sub_word(value, offset, size))
/// ```
///
/// where:
///
/// - The `constant` is some power of 2.
/// - The operands to the multiplication (`*`) may be either way around.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct MulShiftedValue;

impl MulShiftedValue {
    /// Constructs a new instance of the multiplicative shifted value lifting
    /// pass.
    #[must_use]
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }

    /// Calculates which power of 2 `number` is, or returns [`None`] if `number`
    /// is not a power of 2.
    #[must_use]
    pub fn which_power_of_2(mut number: KnownWord) -> Option<usize> {
        let two = KnownWord::from_le(2u8);
        if number == KnownWord::from_le(1u8) {
            Some(0)
        } else if number == KnownWord::zero() {
            None
        } else if number % two == KnownWord::zero() {
            let mut counter = 1;
            while number != two {
                counter += 1;
                number = number / two;

                if counter > WORD_SIZE_BITS {
                    return None;
                }
            }

            Some(counter)
        } else {
            None
        }
    }
}

impl Lift for MulShiftedValue {
    fn run(
        &mut self,
        value: RuntimeBoxedVal,
        _state: &TypeCheckerState,
    ) -> crate::error::unification::Result<RuntimeBoxedVal> {
        fn insert_multiplicative_shifts(data: &RSVD) -> Option<RSVD> {
            let RSVD::Multiply { left, right } = data else {
                return None;
            };

            // We need to pull out the expected structure while accounting for the fact that
            // the operands may be either way around.
            let (constant, value) =
                match (left.data().constant_fold(), right.data().constant_fold()) {
                    (RSVD::KnownData { value }, RSVD::SubWord { .. }) => (
                        value,
                        right.clone().transform_data(insert_multiplicative_shifts),
                    ),
                    (RSVD::SubWord { .. }, RSVD::KnownData { value }) => (
                        value,
                        left.clone().transform_data(insert_multiplicative_shifts),
                    ),
                    _ => return None,
                };

            let Some(offset) = MulShiftedValue::which_power_of_2(constant) else {
                return None;
            };

            Some(RSVD::Shifted { offset, value })
        }

        Ok(value.transform_data(insert_multiplicative_shifts))
    }
}

#[cfg(test)]
mod test {
    use crate::{
        tc::{
            lift::{mul_shifted::MulShiftedValue, Lift},
            state::TypeCheckerState,
        },
        vm::value::{known::KnownWord, Provenance, SV, SVD},
    };

    #[test]
    fn can_calculate_power_of_two_correctly() {
        let two = KnownWord::from_le(2u8);
        for i in 0..256u32 {
            let power = KnownWord::from_le(i);
            let input = two.exp(power);

            let calculated_power = MulShiftedValue::which_power_of_2(input);
            assert_eq!(calculated_power, Some(i as usize));
        }
    }

    #[test]
    fn can_lift_basic_multiplicative_shifts() -> anyhow::Result<()> {
        // Create the input data
        let value = SV::new_value(0, Provenance::Synthetic);
        let sub_word = SV::new_synthetic(
            1,
            SVD::SubWord {
                value,
                offset: 0,
                size: 64,
            },
        );
        let constant = SV::new_known_value(
            2,
            KnownWord::from_le(2u32.pow(16)),
            Provenance::Synthetic,
            None,
        );
        let mul_const_on_left = SV::new_synthetic(
            3,
            SVD::Multiply {
                left:  constant.clone(),
                right: sub_word.clone(),
            },
        );
        let mul_const_on_right = SV::new_synthetic(
            4,
            SVD::Multiply {
                left:  sub_word.clone(),
                right: constant,
            },
        );

        // Run the pass
        let state = TypeCheckerState::empty();
        let result_left = MulShiftedValue.run(mul_const_on_left, &state)?;
        let result_right = MulShiftedValue.run(mul_const_on_right, &state)?;

        // Check that the results are sane
        match result_left.data() {
            SVD::Shifted { offset, value } => {
                assert_eq!(offset, &16);
                assert_eq!(value, &sub_word);
            }
            _ => panic!("Incorrect payload"),
        }
        match result_right.data() {
            SVD::Shifted { offset, value } => {
                assert_eq!(offset, &16);
                assert_eq!(value, &sub_word);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn can_lift_nested_multiplicative_shifts() -> anyhow::Result<()> {
        // Create the input data
        let inner_value = SV::new_value(0, Provenance::Synthetic);
        let inner_sub_word = SV::new_synthetic(
            1,
            SVD::SubWord {
                value:  inner_value,
                offset: 0,
                size:   128,
            },
        );
        let constant = SV::new_known_value(
            2,
            KnownWord::from_le(2u32.pow(16)),
            Provenance::Synthetic,
            None,
        );
        let inner_mul = SV::new_synthetic(
            3,
            SVD::Multiply {
                left:  constant.clone(),
                right: inner_sub_word.clone(),
            },
        );
        let outer_sub_word = SV::new_synthetic(
            4,
            SVD::SubWord {
                value:  inner_mul,
                offset: 0,
                size:   192,
            },
        );
        let outer_mul = SV::new_synthetic(
            5,
            SVD::Multiply {
                left:  outer_sub_word,
                right: constant,
            },
        );

        // Run the pass
        let state = TypeCheckerState::empty();
        let result = MulShiftedValue.run(outer_mul, &state)?;

        // Check that the result is correct
        match result.data() {
            SVD::Shifted { offset, value } => {
                assert_eq!(offset, &16);

                match value.data() {
                    SVD::SubWord {
                        value,
                        offset,
                        size,
                    } => {
                        assert_eq!(offset, &0);
                        assert_eq!(size, &192);

                        match value.data() {
                            SVD::Shifted { offset, value } => {
                                assert_eq!(offset, &16);
                                assert_eq!(value, &inner_sub_word);
                            }
                            _ => panic!("Incorrect payload"),
                        }
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn does_not_lift_if_operand_is_non_constant() -> anyhow::Result<()> {
        // Create the input data
        let value = SV::new_value(0, Provenance::Synthetic);
        let sub_word = SV::new_synthetic(
            1,
            SVD::SubWord {
                value,
                offset: 0,
                size: 64,
            },
        );
        let constant = SV::new_value(2, Provenance::Synthetic);
        let mul = SV::new_synthetic(
            3,
            SVD::Multiply {
                left:  constant,
                right: sub_word,
            },
        );

        // Run the pass
        let state = TypeCheckerState::empty();
        let result = MulShiftedValue.run(mul.clone(), &state)?;

        // Check that nothing was changed
        assert_eq!(result, mul);

        Ok(())
    }

    #[test]
    fn does_not_lift_if_operand_is_non_sub_word() -> anyhow::Result<()> {
        // Create the input data
        let value = SV::new_value(0, Provenance::Synthetic);
        let constant = SV::new_known_value(
            2,
            KnownWord::from_le(2u32.pow(16)),
            Provenance::Synthetic,
            None,
        );
        let mul = SV::new_synthetic(
            3,
            SVD::Multiply {
                left:  constant,
                right: value,
            },
        );

        // Run the pass
        let state = TypeCheckerState::empty();
        let result = MulShiftedValue.run(mul.clone(), &state)?;

        // Check that nothing was changed
        assert_eq!(result, mul);

        Ok(())
    }

    #[test]
    fn does_not_lift_if_operand_is_not_power_of_two() -> anyhow::Result<()> {
        // Create the input data
        let value = SV::new_value(0, Provenance::Synthetic);
        let sub_word = SV::new_synthetic(
            1,
            SVD::SubWord {
                value,
                offset: 0,
                size: 64,
            },
        );
        let constant =
            SV::new_known_value(2, KnownWord::from_le(31u32), Provenance::Synthetic, None);
        let mul = SV::new_synthetic(
            3,
            SVD::Multiply {
                left:  constant,
                right: sub_word,
            },
        );

        // Run the pass
        let state = TypeCheckerState::empty();
        let result = MulShiftedValue.run(mul.clone(), &state)?;

        // Check that nothing was changed
        assert_eq!(result, mul);

        Ok(())
    }
}
