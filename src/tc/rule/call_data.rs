//! This module contains an inference rule that says that a value has a size
//! equivalent to the size that created it when reading from call data.

use crate::{
    constant::BYTE_SIZE_BITS,
    error::unification::Result,
    tc::{expression::TE, rule::InferenceRule, state::TypeCheckerState},
    vm::value::{known::KnownWord, TCBoxedVal, TCSVD},
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
    fn infer(&self, value: &TCBoxedVal, state: &mut TypeCheckerState) -> Result<()> {
        let TCSVD::CallData { size, .. } = value.data() else {
            return Ok(());
        };

        // If we can make the size into a constant we can work with it
        let TCSVD::KnownData { value: byte_size } = size.data().constant_fold() else {
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
        tc::{
            expression::TE,
            rule::{call_data::CallDataRule, InferenceRule},
            state::TypeCheckerState,
        },
        vm::value::{known::KnownWord, Provenance, RSV, RSVD, TCSVD},
    };

    #[test]
    fn writes_no_inferences_for_non_constant_sizes() -> anyhow::Result<()> {
        // Create the values to run inference on
        let offset = RSV::new_value(0, Provenance::Synthetic);
        let size = RSV::new_value(1, Provenance::Synthetic);
        let call_data = RSV::new_synthetic(2, RSVD::call_data(offset.clone(), size.clone()));

        // Register them in the state
        let mut state = TypeCheckerState::empty();
        let call_data_tv = state.register(call_data);
        let tc_input = state.value_unchecked(call_data_tv).clone();
        let [offset_tv, size_tv] = match tc_input.data() {
            TCSVD::CallData { offset, size, .. } => [offset.type_var(), size.type_var()],
            _ => panic!("Incorrect payload"),
        };
        CallDataRule.infer(&tc_input, &mut state)?;

        // Check that we end up with no equations
        assert!(state.inferences(offset_tv).is_empty());
        assert!(state.inferences(size_tv).is_empty());
        assert!(state.inferences(call_data_tv).is_empty());

        Ok(())
    }

    #[test]
    fn writes_inferences_for_constant_sizes() -> anyhow::Result<()> {
        // Create the values to run inference on
        let offset = RSV::new_value(0, Provenance::Synthetic);
        let size = RSV::new_known_value(1, KnownWord::from_le(16u32), Provenance::Synthetic, None);
        let call_data = RSV::new_synthetic(2, RSVD::call_data(offset.clone(), size.clone()));

        // Register them in the state
        let mut state = TypeCheckerState::empty();
        let call_data_tv = state.register(call_data);
        let tc_input = state.value_unchecked(call_data_tv).clone();
        let [offset_tv, size_tv] = match tc_input.data() {
            TCSVD::CallData { offset, size, .. } => [offset.type_var(), size.type_var()],
            _ => panic!("Incorrect payload"),
        };
        CallDataRule.infer(&tc_input, &mut state)?;

        // Check that we end up with only the expected equation
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
        let offset = RSV::new_value(0, Provenance::Synthetic);
        let left_val =
            RSV::new_known_value(1, KnownWord::from_le(7u32), Provenance::Synthetic, None);
        let right_val =
            RSV::new_known_value(2, KnownWord::from_le(9u32), Provenance::Synthetic, None);
        let size = RSV::new_synthetic(
            3,
            RSVD::Add {
                left:  left_val.clone(),
                right: right_val.clone(),
            },
        );
        let call_data = RSV::new_synthetic(4, RSVD::call_data(offset.clone(), size.clone()));

        // Register them in the state
        let mut state = TypeCheckerState::empty();
        let call_data_tv = state.register(call_data);
        let tc_input = state.value_unchecked(call_data_tv).clone();
        let [offset_tv, size_tv, left_val_tv, right_val_tv] = match tc_input.data() {
            TCSVD::CallData { offset, size, .. } => match size.data() {
                TCSVD::Add { left, right } => [
                    offset.type_var(),
                    size.type_var(),
                    left.type_var(),
                    right.type_var(),
                ],
                _ => panic!("Incorrect payload"),
            },

            _ => panic!("Incorrect payload"),
        };
        CallDataRule.infer(&tc_input, &mut state)?;

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
