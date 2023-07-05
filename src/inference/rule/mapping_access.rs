//! This module contains the definition of the inference rule for dealing with
//! writes to mappings.

use crate::{
    error::unification::Result,
    inference::{expression::TE, rule::InferenceRule, state::InferenceState},
    vm::value::{BoxedVal, SVD},
};

/// This rule creates the equation `base_slot_ty = mapping<key_ty, val_ty>` such
/// for expressions of the following form.
///
/// ```text
/// val_ty = slot(mapping_addr<slot(c_1)>[v_1])
/// ```
///
/// where:
/// - `base_slot_ty = type(slot(c_1))`
/// - `key_ty = type(v_1)`
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct MappingAccessRule;

impl InferenceRule for MappingAccessRule {
    fn infer(&self, value: &BoxedVal, state: &mut InferenceState) -> Result<()> {
        if let SVD::StorageSlot { key } = &value.data {
            let SVD::MappingAccess { key, slot } = &key.data else {
                return Ok(());
            };

            let key_tv = state.var_unchecked(key);
            let val_ty = state.var_unchecked(value);
            let slot_ty = TE::mapping(key_tv, val_ty);
            state.infer_for(slot, slot_ty);
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        inference::{
            expression::TE,
            rule::{mapping_access::MappingAccessRule, InferenceRule},
            state::InferenceState,
        },
        vm::value::{known::KnownWord, Provenance, SV, SVD},
    };

    #[test]
    fn equates_slot_type_with_mapping() -> anyhow::Result<()> {
        // Create a value of the relevant kind
        let v_1 = SV::new_value(0, Provenance::Synthetic);
        let c_1 = SV::new_known_value(1, KnownWord::from(1), Provenance::Synthetic);
        let mapping_slot = SV::new(
            2,
            SVD::StorageSlot { key: c_1.clone() },
            Provenance::Synthetic,
        );
        let mapping = SV::new(
            3,
            SVD::MappingAccess {
                key:  v_1.clone(),
                slot: mapping_slot.clone(),
            },
            Provenance::Synthetic,
        );
        let outer_slot = SV::new(
            4,
            SVD::StorageSlot {
                key: mapping.clone(),
            },
            Provenance::Synthetic,
        );

        // Set up the unifier state
        let mut state = InferenceState::empty();
        let v_1_tv = state.register(v_1);
        let c_1_tv = state.register(c_1);
        let mapping_slot_tv = state.register(mapping_slot);
        let mapping_tv = state.register(mapping);
        let outer_slot_tv = state.register(outer_slot.clone());

        // Run the inference rule
        MappingAccessRule.infer(&outer_slot, &mut state)?;

        assert!(state.inferences(v_1_tv).is_empty());
        assert!(state.inferences(c_1_tv).is_empty());
        assert_eq!(state.inferences(mapping_slot_tv).len(), 1);
        assert!(state.inferences(mapping_slot_tv).contains(&TE::Mapping {
            key:   v_1_tv,
            value: outer_slot_tv,
        }));
        assert!(state.inferences(mapping_tv).is_empty());
        assert!(state.inferences(outer_slot_tv).is_empty());

        Ok(())
    }
}
