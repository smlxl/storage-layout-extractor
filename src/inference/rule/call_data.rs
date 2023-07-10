//! This module contains an inference rule that says that a value has a size
//! equivalent to the size that created it when reading from call data.

use crate::{
    constant::BYTE_SIZE_BITS,
    inference::{expression::TE, rule::InferenceRule, state::InferenceState},
    vm::value::{known::KnownWord, BoxedVal, SVD},
};

/// This rule creates equations as described below for expressions of the
/// following form.
///
/// ```text
/// call_data[id](offset, read_size)
///     a           b         c
/// ```
///
/// equates:
/// - `a = word(size = read_size, usage = Bytes)` if `read_size` is constant
///
/// Note that `call_data` is created from both `CallDataLoad`, which loads a
/// single word, and `CallDataCopy`, which may load much more than a single
/// word. In the case where the read size during `CallDataCopy` is constant
/// however, we instead create individual words in memory with defined sizes.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct CallDataRule;

impl InferenceRule for CallDataRule {
    fn infer(
        &self,
        value: &BoxedVal,
        state: &mut InferenceState,
    ) -> crate::error::unification::Result<()> {
        let SVD::CallData { size, .. } = &value.data else {
            return Ok(());
        };

        // If we can make the size into a constant we can work with it
        let SVD::KnownData { value: byte_size } = size.data.clone().constant_fold() else {
            return Ok(());
        };

        // Otherwise, we can infer that the type of the value is word
        let value_bits: usize = <KnownWord as Into<usize>>::into(byte_size) * BYTE_SIZE_BITS;
        state.infer_for(value, TE::bytes(Some(value_bits)));

        // All done
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        constant::BYTE_SIZE_BITS,
        inference::{
            expression::TE,
            rule::{call_data::CallDataRule, InferenceRule},
            state::InferenceState,
        },
        vm::value::{known::KnownWord, Provenance, SV, SVD},
    };

    #[test]
    fn writes_no_inferences_for_non_constant_sizes() -> anyhow::Result<()> {
        // Create the values to run inference on
        let offset = SV::new_value(0, Provenance::Synthetic);
        let size = SV::new_value(1, Provenance::Synthetic);
        let call_data = SV::new_synthetic(2, SVD::call_data(offset.clone(), size.clone()));

        // Register them in the state
        let mut state = InferenceState::empty();
        let [offset_tv, size_tv, call_data_tv] =
            state.register_many([offset, size, call_data.clone()]);

        // Run the inference rule
        CallDataRule.infer(&call_data, &mut state)?;

        // Check that we end up with no equations
        assert!(state.inferences(offset_tv).is_empty());
        assert!(state.inferences(size_tv).is_empty());
        assert!(state.inferences(call_data_tv).is_empty());

        Ok(())
    }

    #[test]
    fn writes_inferences_for_constant_sizes() -> anyhow::Result<()> {
        // Create the values to run inference on
        let offset = SV::new_value(0, Provenance::Synthetic);
        let size = SV::new_known_value(1, KnownWord::from_le(16u32), Provenance::Synthetic);
        let call_data = SV::new_synthetic(2, SVD::call_data(offset.clone(), size.clone()));

        // Register them in the state
        let mut state = InferenceState::empty();
        let [offset_tv, size_tv, call_data_tv] =
            state.register_many([offset, size, call_data.clone()]);

        // Run the inference rule
        CallDataRule.infer(&call_data, &mut state)?;

        // Check that we end up with no equations
        assert!(state.inferences(offset_tv).is_empty());
        assert!(state.inferences(size_tv).is_empty());
        assert_eq!(state.inferences(call_data_tv).len(), 1);
        assert!(
            state
                .inferences(call_data_tv)
                .contains(&TE::bytes(Some(16 * BYTE_SIZE_BITS)))
        );

        Ok(())
    }

    #[test]
    fn writes_inferences_when_size_needs_folding() -> anyhow::Result<()> {
        // Create the values to run inference on
        let offset = SV::new_value(0, Provenance::Synthetic);
        let left_val = SV::new_known_value(1, KnownWord::from_le(7u32), Provenance::Synthetic);
        let right_val = SV::new_known_value(2, KnownWord::from_le(9u32), Provenance::Synthetic);
        let size = SV::new_synthetic(
            3,
            SVD::Add {
                left:  left_val.clone(),
                right: right_val.clone(),
            },
        );
        let call_data = SV::new_synthetic(4, SVD::call_data(offset.clone(), size.clone()));

        // Register them in the state
        let mut state = InferenceState::empty();
        let [offset_tv, left_val_tv, right_val_tv, size_tv, call_data_tv] =
            state.register_many([offset, left_val, right_val, size, call_data.clone()]);

        // Run the inference rule
        CallDataRule.infer(&call_data, &mut state)?;

        // Check that we end up with no equations
        assert!(state.inferences(offset_tv).is_empty());
        assert!(state.inferences(left_val_tv).is_empty());
        assert!(state.inferences(right_val_tv).is_empty());
        assert!(state.inferences(size_tv).is_empty());
        assert_eq!(state.inferences(call_data_tv).len(), 1);
        assert!(
            state
                .inferences(call_data_tv)
                .contains(&TE::bytes(Some(16 * BYTE_SIZE_BITS)))
        );

        Ok(())
    }
}
