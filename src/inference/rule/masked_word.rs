//! This module contains an inference rule that deals with inferring type widths
//! from value sub-word masking operations.

use crate::{
    inference::{
        expression::{Span, TE},
        rule::InferenceRule,
        state::InferenceState,
    },
    vm::value::{BoxedVal, SVD},
};

/// This rule creates equations as follows for operations that mask values to
/// sub-word values.
///
/// ```text
/// sub_word(value, offset, size)
///    a       b
/// ```
///
/// equating:
/// - `a = Word(width = size, usage = Bytes)`
/// - `b = Packed([Positioned(a, offset)])`
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct MaskedWordRule;

impl InferenceRule for MaskedWordRule {
    fn infer(
        &self,
        value: &BoxedVal,
        state: &mut InferenceState,
    ) -> crate::error::unification::Result<()> {
        let SVD::SubWord {
            value: sub_value,
            offset,
            size,
        } = &value.data
        else {
            return Ok(());
        };

        let a_tv = state.var_unchecked(value);
        let b_tv = state.var_unchecked(sub_value);
        let inferred_word = TE::bytes(Some(*size));
        state.infer(a_tv, inferred_word);

        let inferred_packed = TE::packed_of(vec![Span::new(a_tv, *offset, *size)]);
        state.infer(b_tv, inferred_packed);

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        inference::{
            expression::{Span, WordUse, TE},
            rule::{masked_word::MaskedWordRule, InferenceRule},
            state::InferenceState,
        },
        vm::value::{Provenance, SV, SVD},
    };

    #[test]
    fn creates_correct_inference_equations() -> anyhow::Result<()> {
        // Create the values to run inference on
        let value = SV::new_value(0, Provenance::Synthetic);
        let mask = SV::new_synthetic(
            1,
            SVD::SubWord {
                value:  value.clone(),
                offset: 64,
                size:   128,
            },
        );

        // Register them in the state
        let mut state = InferenceState::empty();
        let [value_tv, mask_tv] = state.register_many([value, mask.clone()]);

        // Run the inference rule
        MaskedWordRule.infer(&mask, &mut state)?;

        // Check that we end up with the correct equations
        assert_eq!(state.inferences(value_tv).len(), 1);
        assert!(
            state
                .inferences(value_tv)
                .contains(&TE::packed_of(vec![Span::new(mask_tv, 64, 128)]))
        );
        assert_eq!(state.inferences(mask_tv).len(), 1);
        assert!(
            state
                .inferences(mask_tv)
                .contains(&TE::word(Some(128), WordUse::Bytes))
        );

        Ok(())
    }
}
