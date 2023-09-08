//! This module contains the definition of the inference rule for dealing with
//! writes to mappings.

use crate::{
    constant::WORD_SIZE_BITS,
    error::unification::Result,
    inference::{
        expression::{Span, TE},
        rule::InferenceRule,
        state::InferenceState,
    },
    vm::value::{TCBoxedVal, TCSVD},
};

/// This rule creates the following equations for any expressions of the
/// following form.
///
/// ```text
/// slot<mapping_addr<slot<c_1>>[v_1])>
///   a       b         c   d     e
/// ```
///
/// equating:
///
/// - `c = mapping<e, b>`
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct MappingAccessRule;

impl InferenceRule for MappingAccessRule {
    fn infer(&self, value: &TCBoxedVal, state: &mut InferenceState) -> Result<()> {
        if let TCSVD::StorageSlot { key } = value.data() {
            let TCSVD::MappingIndex {
                key,
                slot,
                projection,
            } = key.data()
            else {
                return Ok(());
            };

            let p = projection.unwrap_or(0);
            let key_tv = state.var_unchecked(key);
            let original_val_ty = state.var_unchecked(value);
            let val_ty = unsafe { state.allocate_ty_var() };

            state.infer(
                val_ty,
                TE::packed_of(vec![Span::new(
                    original_val_ty,
                    p * WORD_SIZE_BITS,
                    WORD_SIZE_BITS,
                )]),
            );
            let slot_ty = TE::mapping(key_tv, val_ty);
            state.infer_for(slot, slot_ty);
        }

        Ok(())
    }
}

// #[cfg(test)]
// mod test {
//     use crate::{
//         inference::{
//             expression::TE,
//             rule::{mapping_access::MappingAccessRule, InferenceRule},
//             state::InferenceState,
//         },
//         vm::value::{known::KnownWord, Provenance, RSV, RSVD},
//     };
//
//     #[test]
//     fn equates_slot_type_with_mapping() -> anyhow::Result<()> {
//         // Create a value of the relevant kind
//         let v_1 = RSV::new_value(0, Provenance::Synthetic);
//         let c_1 = RSV::new_known_value(1, KnownWord::from(1),
// Provenance::Synthetic);         let mapping_slot = RSV::new(
//             2,
//             RSVD::StorageSlot { key: c_1.clone() },
//             Provenance::Synthetic,
//         );
//         let mapping = RSV::new(
//             3,
//             RSVD::MappingAccess {
//                 key:  v_1.clone(),
//                 slot: mapping_slot.clone(),
//             },
//             Provenance::Synthetic,
//         );
//         let outer_slot = RSV::new(
//             4,
//             RSVD::StorageSlot {
//                 key: mapping.clone(),
//             },
//             Provenance::Synthetic,
//         );
//
//         // Set up the unifier state
//         let mut state = InferenceState::empty();
//         let v_1_tv = state.register(v_1);
//         let c_1_tv = state.register(c_1);
//         let mapping_slot_tv = state.register(mapping_slot);
//         let mapping_tv = state.register(mapping);
//         let outer_slot_tv = state.register(outer_slot.clone());
//
//         // Run the inference rule
//         let tc_input = state.value_unchecked(outer_slot_tv).clone();
//         MappingAccessRule.infer(&tc_input, &mut state)?;
//
//         assert!(state.inferences(v_1_tv).is_empty());
//         assert!(state.inferences(c_1_tv).is_empty());
//         assert_eq!(state.inferences(mapping_slot_tv).len(), 1);
//         assert!(state.inferences(mapping_slot_tv).contains(&TE::Mapping {
//             key:   v_1_tv,
//             value: outer_slot_tv,
//         }));
//         assert!(state.inferences(mapping_tv).is_empty());
//         assert!(state.inferences(outer_slot_tv).is_empty());
//
//         Ok(())
//     }
// }
