//! This module contains an inference rule that equates every `SLoad` with the
//! type of its element.

use crate::{
    error::unification::Result,
    inference::{expression::TE, rule::InferenceRule, state::InferenceState},
    vm::value::{TCBoxedVal, TCSVD},
};

/// This rule creates the following equations in the typing state for
/// expressions of the following form.
///
/// ```text
/// s_load(key, value)
///    a    b     c
/// ```
///
/// equating
///
/// - `a = c`
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct SLoadIsElementTypeRule;

impl InferenceRule for SLoadIsElementTypeRule {
    fn infer(&self, value: &TCBoxedVal, state: &mut InferenceState) -> Result<()> {
        let TCSVD::SLoad {
            value: inner_value, ..
        } = &value.data
        else {
            return Ok(());
        };

        let inner_value_tv = state.var_unchecked(inner_value);
        state.infer_for(value, TE::eq(inner_value_tv));

        Ok(())
    }
}

// #[cfg(test)]
// mod test {
//     use crate::{
//         inference::{
//             expression::TE,
//             rule::{s_load_is_element_type::SLoadIsElementTypeRule,
// InferenceRule},             state::InferenceState,
//         },
//         vm::value::{Provenance, RSV, RSVD},
//     };
//
//     #[test]
//     fn creates_correct_equations_in_state() -> anyhow::Result<()> {
//         // Create the expressions to be typed
//         let key = RSV::new_value(0, Provenance::Synthetic);
//         let value = RSV::new_value(1, Provenance::Synthetic);
//         let s_load = RSV::new_synthetic(
//             2,
//             RSVD::SLoad {
//                 key:   key.clone(),
//                 value: value.clone(),
//             },
//         );
//
//         // Register these in the state
//         let mut state = InferenceState::empty();
//         let [key_ty, value_ty, s_load_ty] = state.register_many([key, value,
// s_load.clone()]);
//
//         // Run the inference rule and check things make sense
//         let tc_input = state.value_unchecked(s_load_ty).clone();
//         SLoadIsElementTypeRule.infer(&tc_input, &mut state)?;
//
//         assert!(state.inferences(key_ty).is_empty());
//
//         assert_eq!(state.inferences(value_ty).len(), 1);
//         assert!(state.inferences(value_ty).contains(&TE::eq(s_load_ty)));
//
//         assert_eq!(state.inferences(s_load_ty).len(), 1);
//         assert!(state.inferences(s_load_ty).contains(&TE::eq(value_ty)));
//
//         Ok(())
//     }
// }
