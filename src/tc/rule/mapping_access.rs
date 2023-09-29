//! This module contains the definition of the inference rule for dealing with
//! writes to mappings.

use crate::{
    constant::WORD_SIZE_BITS,
    error::unification::Result,
    tc::{
        expression::{Span, TE},
        rule::InferenceRule,
        state::TypeCheckerState,
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
    fn infer(&self, value: &TCBoxedVal, state: &mut TypeCheckerState) -> Result<()> {
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

#[cfg(test)]
mod test {
    use crate::{
        constant::WORD_SIZE_BITS,
        tc::{
            expression::{Span, TE},
            rule::{mapping_access::MappingAccessRule, InferenceRule},
            state::TypeCheckerState,
        },
        vm::value::{known::KnownWord, Provenance, RSV, RSVD, TCSVD},
    };

    #[test]
    fn equates_slot_type_with_mapping() -> anyhow::Result<()> {
        // Create a value of the relevant kind
        let v_1 = RSV::new_value(0, Provenance::Synthetic);
        let c_1 = RSV::new_known_value(1, KnownWord::from(1), Provenance::Synthetic, None);
        let mapping_slot = RSV::new_synthetic(2, RSVD::StorageSlot { key: c_1.clone() });
        let mapping = RSV::new_synthetic(
            3,
            RSVD::MappingIndex {
                key:        v_1.clone(),
                slot:       mapping_slot.clone(),
                projection: None,
            },
        );
        let outer_slot = RSV::new_synthetic(
            4,
            RSVD::StorageSlot {
                key: mapping.clone(),
            },
        );

        // Set up the unifier state
        let mut state = TypeCheckerState::empty();
        let outer_slot_tv = state.register(outer_slot);
        let tc_input = state.value_unchecked(outer_slot_tv).clone();
        let [mapping_tv, mapping_slot_tv, c_1_tv, v_1_tv] = match tc_input.data() {
            TCSVD::StorageSlot { key } => {
                let mapping_tv = key.type_var();
                match key.data() {
                    TCSVD::MappingIndex { key, slot, .. } => {
                        let mapping_slot_tv = slot.type_var();
                        let v_1_tv = key.type_var();
                        match slot.data() {
                            TCSVD::StorageSlot { key } => {
                                let c_1_tv = key.type_var();

                                [mapping_tv, mapping_slot_tv, c_1_tv, v_1_tv]
                            }
                            _ => panic!("Incorrect payload"),
                        }
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        };
        MappingAccessRule.infer(&tc_input, &mut state)?;

        assert!(state.inferences(v_1_tv).is_empty());
        assert!(state.inferences(c_1_tv).is_empty());
        assert_eq!(state.inferences(mapping_slot_tv).len(), 1);
        let val_tv = state
            .inferences(mapping_slot_tv)
            .iter()
            .find(|i| matches!(i, TE::Mapping { key, .. } if *key == v_1_tv));
        match val_tv {
            Some(TE::Mapping { key, value }) => {
                assert_eq!(*key, v_1_tv);

                assert!(
                    state.inferences(value).contains(&TE::packed_of(vec![Span::new(
                        outer_slot_tv,
                        0,
                        WORD_SIZE_BITS
                    )]))
                );
            }
            _ => panic!("Incorrect payload"),
        }
        assert!(state.inferences(mapping_tv).is_empty());
        assert!(state.inferences(outer_slot_tv).is_empty());

        Ok(())
    }
}
