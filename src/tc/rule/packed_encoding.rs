//! This module contains the inference rule definition for inferring packed type
//! encodings for values that represent packed encodings.

use crate::{
    error::unification::Result,
    tc::{
        expression::{Span, TE},
        rule::InferenceRule,
        state::TypeCheckerState,
    },
    vm::value::{TCBoxedVal, TCSVD},
};

/// This rule creates the following equations in the typing state for
/// expressions of the following form.
///
/// ```text
/// packed(elem_1, elem_2, ..., elem_n))
///    a    b_1     b_2   ...    b_n
/// ```
///
/// equating
///
/// - `a = packed(b_1, b_2, ..., b_n)`
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct PackedEncodingRule;

impl InferenceRule for PackedEncodingRule {
    fn infer(&self, value: &TCBoxedVal, state: &mut TypeCheckerState) -> Result<()> {
        let TCSVD::Packed { elements } = value.data() else { return Ok(()) };

        // Construct the inference from this input
        let element_spans: Vec<Span> = elements
            .iter()
            .map(|span| Span::new(state.var_unchecked(&span.value), span.offset, span.size))
            .collect();
        let packed_type = TE::packed_of(element_spans);

        // Actually infer the type
        state.infer_for(value, packed_type);

        // All is well, so we return
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        tc::{
            expression::{Span, TE},
            rule::{packed_encoding::PackedEncodingRule, InferenceRule},
            state::TypeCheckerState,
        },
        vm::value::{PackedSpan, Provenance, RSV, RSVD, TCSVD},
    };

    #[test]
    fn creates_correct_expressions_in_typing_state() -> anyhow::Result<()> {
        // Create the expressions to be typed
        let span_1_value = RSV::new_value(0, Provenance::Synthetic);
        let span_2_value = RSV::new_value(1, Provenance::Synthetic);
        let span_3_value = RSV::new_value(2, Provenance::Synthetic);
        let packed = RSV::new_synthetic(
            3,
            RSVD::Packed {
                elements: vec![
                    PackedSpan::new(0, 64, span_1_value.clone()),
                    PackedSpan::new(128, 32, span_2_value.clone()),
                    PackedSpan::new(192, 16, span_3_value.clone()),
                ],
            },
        );

        // Register these in the typing state
        let mut state = TypeCheckerState::empty();
        let packed_tv = state.register(packed.clone());
        let tc_input = state.value_unchecked(packed_tv).clone();
        let [span_1_tv, span_2_tv, span_3_tv] = match tc_input.data() {
            TCSVD::Packed { elements } => [
                elements[0].value.type_var(),
                elements[1].value.type_var(),
                elements[2].value.type_var(),
            ],
            _ => panic!("Incorrect payload"),
        };
        PackedEncodingRule.infer(&tc_input, &mut state)?;

        assert!(state.inferences(span_1_tv).is_empty());
        assert!(state.inferences(span_2_tv).is_empty());
        assert!(state.inferences(span_3_tv).is_empty());

        assert_eq!(state.inferences(packed_tv).len(), 1);
        assert!(state.inferences(packed_tv).contains(&TE::packed_of(vec![
            Span::new(span_1_tv, 0, 64),
            Span::new(span_2_tv, 128, 32),
            Span::new(span_3_tv, 192, 16),
        ])));

        Ok(())
    }
}
