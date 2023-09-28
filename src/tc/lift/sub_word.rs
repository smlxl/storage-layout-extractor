//! This lifting pass looks for operations that mask values to create
//! sub-values, as these can be used to infer the width of a value.

use itertools::Itertools;

use crate::{
    constant::WORD_SIZE_BITS,
    tc::{
        lift::{mul_shifted::MulShiftedValue, Lift},
        state::TypeCheckerState,
    },
    vm::value::{RuntimeBoxedVal, RSVD, SVD},
};

/// This pass detects and folds expressions that mask word-size values where the
/// masks are recursively constant.
///
/// These have a form as follows:
///
/// ```code
/// value & mask
///
/// becomes
///
/// sub_word(value, offset, length)
/// ```
///
/// where:
/// - The operands to `&` may be flipped as the operator is symmetric.
/// - `mask` is some recursively constant value (e.g. `((1 << shift) - 1)` where
///   `shift` is recursively constant). Recursively constant means that the
///   expression is either encoded as a constant in the bytecode, or composed of
///   operations that can be constant folded on constants in the bytecode). In
///   essence, that the expression can be _turned into_ a constant.
/// - `offset` is computed from the value of the `mask`, and is the 0-based
///   offset in bits from the start of the word.
/// - `length` is the size of the sub-word value, also computed from the `mask`
///
/// It works on the assumption that the solidity compiler only ever generates
/// masks that are recursively constant. This seems to bear out in practice, and
/// means that if the mask cannot be resolved to a constant we do not have a
/// valid masking operation.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct SubWordValue;

impl SubWordValue {
    /// Constructs a new instance of the sub-word value lifting pass.
    #[must_use]
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }

    /// Gets the `offset` and `length` of the sub-word if it exists, returning
    /// [`None`] otherwise.
    ///
    /// This function assumes that `data` is the potential mask to inspect.
    #[must_use]
    pub fn get_region(data: &RSVD) -> Option<SubWord> {
        // The word to pull the mask details out of
        let SVD::KnownData { value } = data.constant_fold() else {
            // If it does not fold to a constant we cannot actually work out the details of
            // the mask here, so we fail out
            return None;
        };

        // To work out the details of the mask we need to inspect the bit pattern; this
        // can be done using bit ops, but using a bitvec is clearer and easier to
        // understand
        let word_bits = value.bits_le();

        // Finding the first 1 bit tells us where the mask starts
        let Some((offset, _)) = word_bits.iter().find_position(|bit| bit == &true) else {
            // If we never see a 1 bit the mask is all zeroes
            return None;
        };

        // Finding the first 0 bit after the offset tells us the size of the mask, but
        // if we don't find a zero bit afterward, the mask is the rest of the word
        let size = word_bits
            .iter()
            .skip(offset)
            .find_position(|bit| bit == &false)
            .map_or(WORD_SIZE_BITS - offset, |(offset, _)| offset);

        Some(SubWord::new(offset, size))
    }

    #[must_use]
    pub fn get_shift(value: &RuntimeBoxedVal) -> (&RuntimeBoxedVal, usize) {
        match &value.data() {
            RSVD::RightShift { value, shift } => match shift.constant_fold().data() {
                RSVD::KnownData { value: shift } => (value, shift.into()),
                _ => (value, 0),
            },
            RSVD::Divide { dividend, divisor } => match divisor.data() {
                RSVD::Exp {
                    value: base,
                    exponent: exp,
                } => match (base.data(), exp.data()) {
                    (RSVD::KnownData { value: base }, RSVD::KnownData { value: exp }) => {
                        if usize::from(base) == 2 {
                            (dividend, usize::from(exp))
                        } else {
                            (value, 0)
                        }
                    }
                    _ => (value, 0),
                },
                RSVD::LeftShift { value: base, shift } => match (base.data(), shift.data()) {
                    (RSVD::KnownData { value: base }, RSVD::KnownData { value: shift })
                        if usize::from(base) == 1 =>
                    {
                        (dividend, shift.into())
                    }
                    _ => (value, 0),
                },
                RSVD::KnownData { value: divisor } => {
                    if let Some(shift) = MulShiftedValue::which_power_of_2(*divisor) {
                        (dividend, shift)
                    } else {
                        (value, 0)
                    }
                }
                _ => (value, 0),
            },
            _ => (value, 0),
        }
    }
}

impl Lift for SubWordValue {
    fn run(
        &mut self,
        value: RuntimeBoxedVal,
        _state: &TypeCheckerState,
    ) -> crate::error::unification::Result<RuntimeBoxedVal> {
        /// Inserts any sub word accesses that it can find.
        fn insert_sub_words(data: &RSVD) -> Option<RSVD> {
            // At the top level it must be an 'and'
            let SVD::And { left, right } = data else {
                return None;
            };

            // These can be ordered either way around the `and`, so we have to check both
            // sides
            let (value, SubWord { offset, length }) =
                if let Some(word) = SubWordValue::get_region(left.data()) {
                    (right, word)
                } else if let Some(word) = SubWordValue::get_region(right.data()) {
                    (left, word)
                } else {
                    return None;
                };

            // If it is a constant we don't want to compute it as a sub-word as this gives
            // us wonky sizing in some cases
            if matches!(value.data(), RSVD::KnownData { .. }) {
                return None;
            }

            // Next we have to pull the shift amount (if any) out of the value
            let (value, shift) = SubWordValue::get_shift(value);
            let value = value.clone().transform_data(insert_sub_words);

            let value = match value.data() {
                RSVD::SubWord {
                    offset: i_ofs,
                    size: i_sz,
                    value: i_val,
                } if offset == *i_ofs && length == *i_sz => i_val.clone(),
                _ => value,
            };

            // If we find a word, we can easily construct the return data
            let payload = SVD::SubWord {
                value,
                offset: offset + shift,
                size: length,
            };

            Some(payload)
        }

        Ok(value.transform_data(insert_sub_words))
    }
}

/// A representation of a region within an EVM word that is treated as a single
/// value.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct SubWord {
    /// The zero-indexed offset in bits from the start (LSB) of the word where
    /// the sub-word begins.
    pub offset: usize,

    /// The length in bits of the sub-word.
    pub length: usize,
}

impl SubWord {
    /// Creates a new `SubWord` with the specified `offset` and `length`.
    #[must_use]
    pub fn new(offset: usize, length: usize) -> Self {
        Self { offset, length }
    }
}

#[cfg(test)]
mod test {
    use crate::{
        tc::{
            lift::{sub_word::SubWordValue, Lift},
            state::TypeCheckerState,
        },
        vm::value::{known::KnownWord, Provenance, SV, SVD},
    };

    #[test]
    fn computes_correct_mask_with_no_offset() {
        // A mask that is the lowest 64 bits of the word
        let mask = KnownWord::from_le(0xffff_ffff_ffff_ffffu128);
        let data = SVD::new_known(mask);

        // Run the decomposition process on the mask
        let result = SubWordValue::get_region(&data).expect("Mask resolution failed");

        // Check that it is correct
        assert_eq!(result.offset, 0);
        assert_eq!(result.length, 64);
    }

    #[test]
    fn computes_correct_mask_with_offset() {
        // A mask that is lowest 32 bits of skip then 64 bits of the data
        let mask = KnownWord::from_le_bytes([
            0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ]);
        let data = SVD::new_known(mask);

        // Run the decomposition process on the mask
        let result = SubWordValue::get_region(&data).expect("Mask resolution failed");

        // Check that it is correct
        assert_eq!(result.offset, 32);
        assert_eq!(result.length, 64);
    }

    #[test]
    fn computes_correct_mask_as_rest_of_word() {
        // A mask that is the lowest 128 bits of the word
        let mask = KnownWord::from_le_bytes([
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff,
        ]);
        let data = SVD::new_known(mask);

        // Run the decomposition process on the mask
        let result = SubWordValue::get_region(&data).expect("Mask resolution failed");

        // Check that it is correct
        assert_eq!(result.offset, 128);
        assert_eq!(result.length, 128);
    }

    #[test]
    fn computes_correct_mask_from_expression() {
        // A mask that is the lowest 192 bits of the word
        let shift_amount =
            SV::new_known_value(0, KnownWord::from_le(0xc0u32), Provenance::Synthetic, None);
        let one = SV::new_known_value(1, KnownWord::from_le(1u32), Provenance::Synthetic, None);
        let shift = SV::new_synthetic(
            2,
            SVD::LeftShift {
                shift: shift_amount,
                value: one.clone(),
            },
        );
        let subtract = SV::new_synthetic(
            3,
            SVD::Subtract {
                left:  shift,
                right: one,
            },
        );

        // Run the decomposition process on the mask
        let result = SubWordValue::get_region(subtract.data()).expect("Mask resolution failed");

        // Check that it is correct
        assert_eq!(result.offset, 0);
        assert_eq!(result.length, 192);
    }

    #[test]
    fn does_not_compute_mask_for_non_constant_fold() {
        // A mask that we cannot do a single thing with
        let mask = SV::new_value(0, Provenance::Synthetic);

        // Run the decomposition process on the mask
        let result = SubWordValue::get_region(mask.data());

        // Check it fails out
        assert!(result.is_none());
    }

    #[test]
    fn resolves_word_masks() -> anyhow::Result<()> {
        // Construct the mask value itself (lowest 192 bits of the word)
        let shift_amount =
            SV::new_known_value(0, KnownWord::from_le(0xc0u32), Provenance::Synthetic, None);
        let one = SV::new_known_value(1, KnownWord::from_le(1u32), Provenance::Synthetic, None);
        let shift = SV::new_synthetic(
            2,
            SVD::LeftShift {
                shift: shift_amount,
                value: one.clone(),
            },
        );
        let mask = SV::new_synthetic(
            3,
            SVD::Subtract {
                left:  shift,
                right: one,
            },
        );

        // Create the value being masked
        let input_value = SV::new_value(4, Provenance::Synthetic);

        // Create the two ways round we want to test
        let mask_on_left = SV::new_synthetic(
            5,
            SVD::And {
                left:  mask.clone(),
                right: input_value.clone(),
            },
        );
        let mask_on_right = SV::new_synthetic(
            5,
            SVD::And {
                left:  input_value.clone(),
                right: mask,
            },
        );

        // Run the lifting pass on both
        let state = TypeCheckerState::empty();
        let result_on_left = SubWordValue.run(mask_on_left, &state)?;
        let result_on_right = SubWordValue.run(mask_on_right, &state)?;

        // Check that it is correct
        assert_eq!(result_on_left, result_on_right);

        match result_on_left.data() {
            SVD::SubWord {
                value,
                offset,
                size,
            } => {
                assert_eq!(value, &input_value);
                assert_eq!(offset, &0);
                assert_eq!(size, &192);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn collapses_directly_identical_masks() -> anyhow::Result<()> {
        // Construct the mask value itself (lowest 192 bits of the word)
        let shift_amount =
            SV::new_known_value(0, KnownWord::from_le(0xc0u32), Provenance::Synthetic, None);
        let one = SV::new_known_value(1, KnownWord::from_le(1u32), Provenance::Synthetic, None);
        let shift = SV::new_synthetic(
            2,
            SVD::LeftShift {
                shift: shift_amount,
                value: one.clone(),
            },
        );
        let mask = SV::new_synthetic(
            3,
            SVD::Subtract {
                left:  shift,
                right: one,
            },
        );

        // Create the value being masked and the mask operation
        let input_value = SV::new_value(4, Provenance::Synthetic);
        let mask_operation = SV::new_synthetic(
            5,
            SVD::And {
                left:  mask.clone(),
                right: input_value.clone(),
            },
        );

        // Now wrap these in another mask to check recursion
        let recurse_on_left = SV::new_synthetic(
            6,
            SVD::And {
                left:  mask_operation.clone(),
                right: mask.clone(),
            },
        );
        let recurse_on_right = SV::new_synthetic(
            7,
            SVD::And {
                left:  mask,
                right: mask_operation,
            },
        );

        // Run the lifting pass on both
        let state = TypeCheckerState::empty();
        let result_on_left = SubWordValue.run(recurse_on_left, &state)?;
        let result_on_right = SubWordValue.run(recurse_on_right, &state)?;

        // Check that it is correct
        assert_eq!(result_on_left, result_on_right);

        match result_on_left.data() {
            SVD::SubWord {
                value,
                offset,
                size,
            } => {
                assert_eq!(offset, &0);
                assert_eq!(size, &192);
                assert_eq!(value, &input_value);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }
}
