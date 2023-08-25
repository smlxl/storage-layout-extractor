//! This module contains the definition of an inference rule for typing dynamic
//! array writes.

use crate::{
    error::unification::Result,
    inference::{expression::TE, rule::InferenceRule, state::InferenceState},
    vm::value::{TCBoxedVal, TCSVD},
};

/// This rule creates the following equations in the typing state for
/// expressions of the following form.
///
/// ```code
/// s_store(storage_slot(dynamic_array<storage_slot(base_slot)>[index]), value)
///    a          b            c             d          e         f        g
/// ```
///
/// equating
/// - `d = dynamic_array<b>`
/// - `f = word(width = unknown, usage = UnsignedWord)`
/// - `b = g`
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct DynamicArrayWriteRule;

impl InferenceRule for DynamicArrayWriteRule {
    #[allow(clippy::many_single_char_names)] // They correspond to the above spec
    fn infer(&self, value: &TCBoxedVal, state: &mut InferenceState) -> Result<()> {
        let TCSVD::StorageWrite { key: b, value: g } = value.data() else {
            return Ok(());
        };
        let TCSVD::StorageSlot { key: c } = b.data() else {
            return Ok(());
        };
        let TCSVD::DynamicArrayAccess { slot: d, index: f } = c.data() else {
            return Ok(());
        };
        let TCSVD::StorageSlot { .. } = d.data() else {
            return Ok(());
        };

        // `b = g`
        let b_tv = state.var_unchecked(b);
        let g_tv = state.var_unchecked(g);
        state.infer(b_tv, TE::eq(g_tv));

        // `f = unsigned`
        state.infer_for(f, TE::unsigned_word(None));

        // `d = dynamic_array<b>`
        state.infer_for(d, TE::dyn_array(b_tv));

        Ok(())
    }
}

// #[cfg(test)]
// mod test {
//     use crate::{
//         inference::{
//             expression::TE,
//             rule::{dynamic_array_write::DynamicArrayWriteRule,
// InferenceRule},             state::InferenceState,
//         },
//         vm::value::{Provenance, RSV, RSVD},
//     };
//
//     #[test]
//     fn creates_correct_inference_equations() -> anyhow::Result<()> {
//         // Create a value of the relevant structure
//         let value = RSV::new_value(0, Provenance::Synthetic);
//         let index = RSV::new_value(1, Provenance::Synthetic);
//         let base_slot = RSV::new_value(2, Provenance::Synthetic);
//         let slot_of_base_slot = RSV::new(
//             3,
//             RSVD::StorageSlot {
//                 key: base_slot.clone(),
//             },
//             Provenance::Synthetic,
//         );
//         let dyn_array = RSV::new(
//             4,
//             RSVD::DynamicArrayAccess {
//                 slot:  slot_of_base_slot.clone(),
//                 index: index.clone(),
//             },
//             Provenance::Synthetic,
//         );
//         let slot_of_dyn_array = RSV::new(
//             5,
//             RSVD::StorageSlot {
//                 key: dyn_array.clone(),
//             },
//             Provenance::Synthetic,
//         );
//         let store = RSV::new(
//             6,
//             RSVD::StorageWrite {
//                 key:   slot_of_dyn_array.clone(),
//                 value: value.clone(),
//             },
//             Provenance::Synthetic,
//         );
//
//         // Set up the unifier state
//         let mut state = InferenceState::empty();
//         let g_tv = state.register(value);
//         let f_tv = state.register(index);
//         let e_tv = state.register(base_slot);
//         let d_tv = state.register(slot_of_base_slot);
//         let c_tv = state.register(dyn_array);
//         let b_tv = state.register(slot_of_dyn_array);
//         let a_tv = state.register(store.clone());
//
//         // Run the inference rule
//         let tc_input = state.value_unchecked(a_tv).clone();
//         DynamicArrayWriteRule.infer(&tc_input, &mut state)?;
//
//         // Check that we end up with expected results in the state
//         assert_eq!(state.inferences(g_tv).len(), 1);
//         assert!(state.inferences(g_tv).contains(&TE::eq(b_tv)));
//
//         assert_eq!(state.inferences(f_tv).len(), 1);
//         assert!(state.inferences(f_tv).contains(&TE::unsigned_word(None)));
//
//         assert!(state.inferences(e_tv).is_empty());
//
//         assert_eq!(state.inferences(d_tv).len(), 1);
//         assert!(state.inferences(d_tv).contains(&TE::dyn_array(b_tv)));
//
//         assert!(state.inferences(c_tv).is_empty());
//
//         assert_eq!(state.inferences(b_tv).len(), 1);
//         assert!(state.inferences(b_tv).contains(&TE::eq(g_tv)));
//
//         assert!(state.inferences(a_tv).is_empty());
//
//         Ok(())
//     }
// }
