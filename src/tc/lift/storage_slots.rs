//! This module provides a lifting pass that recognises accesses to storage
//! slots, and wraps the constant slots in fixed expressions.

use crate::{
    tc::{lift::Lift, state::TypeCheckerState},
    vm::value::{RuntimeBoxedVal, RSV, RSVD},
};

/// This pass detects and wraps expressions that access constant storage slots
/// so that these constants can be distinguished from other constants of the
/// same value.
///
/// This pass relies on the results of the [`super::mapping_index`] pass, and
/// hence must be ordered after it in the lifting pass ordering.
///
/// # Note
///
/// It currently only recognises a subset of cases, but this will be improved in
/// the future alongside other lifting passes.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct StorageSlots;

impl StorageSlots {
    /// Constructs a new instance of the storage slot access lifting pass.
    #[must_use]
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }
}

impl Lift for StorageSlots {
    fn run(
        &mut self,
        value: RuntimeBoxedVal,
        _state: &TypeCheckerState,
    ) -> crate::error::unification::Result<RuntimeBoxedVal> {
        fn insert_storage_accesses(data: &RSVD) -> Option<RSVD> {
            match data {
                RSVD::MappingIndex {
                    key,
                    slot,
                    projection,
                } => {
                    let data = match &slot.data() {
                        RSVD::StorageSlot { .. } => slot.data().clone(),
                        _ => RSVD::StorageSlot {
                            key: slot.clone().transform_data(insert_storage_accesses),
                        },
                    };
                    let slot = RSV::new(slot.instruction_pointer(), data, slot.provenance(), None);
                    Some(RSVD::MappingIndex {
                        key: key.clone().transform_data(insert_storage_accesses),
                        slot,
                        projection: *projection,
                    })
                }
                RSVD::StorageWrite { key, value } => {
                    let data = match &key.data() {
                        RSVD::StorageSlot { .. } => key.data().clone(),
                        _ => RSVD::StorageSlot {
                            key: key.clone().transform_data(insert_storage_accesses),
                        },
                    };
                    let new_key = RSV::new(key.instruction_pointer(), data, key.provenance(), None);
                    Some(RSVD::StorageWrite {
                        key:   new_key,
                        value: value.clone().transform_data(insert_storage_accesses),
                    })
                }
                RSVD::DynamicArrayIndex { slot, index } => {
                    let data = match &slot.data() {
                        RSVD::StorageSlot { .. } => slot.data().clone(),
                        _ => RSVD::StorageSlot {
                            key: slot.clone().transform_data(insert_storage_accesses),
                        },
                    };
                    let slot = RSV::new(slot.instruction_pointer(), data, slot.provenance(), None);
                    Some(RSVD::DynamicArrayIndex {
                        index: index.clone().transform_data(insert_storage_accesses),
                        slot,
                    })
                }
                RSVD::SLoad { key, value } => {
                    let data = match &key.data() {
                        RSVD::StorageSlot { .. } => key.data().clone(),
                        _ => RSVD::StorageSlot {
                            key: key.clone().transform_data(insert_storage_accesses),
                        },
                    };
                    let slot = RSV::new(key.instruction_pointer(), data, key.provenance(), None);
                    Some(RSVD::SLoad {
                        key:   slot,
                        value: value.clone().transform_data(insert_storage_accesses),
                    })
                }
                _ => None,
            }
        }

        Ok(value.transform_data(insert_storage_accesses))
    }
}

#[cfg(test)]
mod test {
    use crate::{
        tc::{
            lift::{storage_slots::StorageSlots, Lift},
            state::TypeCheckerState,
        },
        vm::value::{known::KnownWord, Provenance, RSV, RSVD},
    };

    #[test]
    fn lifts_storage_slots_in_mappings_at_top_level() -> anyhow::Result<()> {
        let slot_index_constant =
            RSV::new_known_value(0, KnownWord::from(7), Provenance::Synthetic, None);
        let mapping_key = RSV::new_value(1, Provenance::Synthetic);
        let mapping_access = RSV::new_synthetic(
            2,
            RSVD::MappingIndex {
                key:        mapping_key.clone(),
                slot:       slot_index_constant.clone(),
                projection: None,
            },
        );

        let state = TypeCheckerState::empty();
        let result = StorageSlots.run(mapping_access, &state)?;

        match result.data() {
            RSVD::MappingIndex {
                key,
                slot,
                projection,
            } => {
                assert!(projection.is_none());
                assert_eq!(key, &mapping_key);
                match slot.data() {
                    RSVD::StorageSlot { key } => {
                        assert_eq!(key, &slot_index_constant);
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn lifts_storage_slots_in_mappings_when_nested() -> anyhow::Result<()> {
        let slot_index_constant =
            RSV::new_known_value(0, KnownWord::from(7), Provenance::Synthetic, None);
        let mapping_key = RSV::new_value(1, Provenance::Synthetic);
        let mapping_access = RSV::new_synthetic(
            2,
            RSVD::MappingIndex {
                key:        mapping_key.clone(),
                slot:       slot_index_constant.clone(),
                projection: None,
            },
        );
        let outer_key = RSV::new_value(1, Provenance::Synthetic);
        let write = RSV::new_synthetic(
            7,
            RSVD::StorageWrite {
                key:   outer_key.clone(),
                value: mapping_access,
            },
        );

        let state = TypeCheckerState::empty();
        let result = StorageSlots.run(write, &state)?;

        match result.data() {
            RSVD::StorageWrite { key, value } => {
                match key.data() {
                    RSVD::StorageSlot { key } => {
                        assert_eq!(key, &outer_key);
                    }
                    _ => panic!("Incorrect payload"),
                }

                match value.data() {
                    RSVD::MappingIndex {
                        key,
                        slot,
                        projection,
                    } => {
                        assert!(projection.is_none());
                        assert_eq!(key, &mapping_key);
                        match slot.data() {
                            RSVD::StorageSlot { key } => {
                                assert_eq!(key, &slot_index_constant);
                            }
                            _ => panic!("Incorrect payload"),
                        }
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn lifts_storage_slots_in_s_stores() -> anyhow::Result<()> {
        let storage_key = RSV::new_known_value(0, KnownWord::from(1), Provenance::Synthetic, None);
        let storage_value = RSV::new_value(1, Provenance::Synthetic);
        let storage_store = RSV::new_synthetic(
            2,
            RSVD::StorageWrite {
                key:   storage_key.clone(),
                value: storage_value.clone(),
            },
        );

        let state = TypeCheckerState::empty();
        let result = StorageSlots.run(storage_store, &state)?;

        match result.data() {
            RSVD::StorageWrite { key, value } => match key.data() {
                RSVD::StorageSlot { key } => {
                    assert_eq!(key, &storage_key);
                    assert_eq!(value, &storage_value);
                }
                _ => panic!("Incorrect payload"),
            },
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn lifts_storage_slots_in_dyn_arrays() -> anyhow::Result<()> {
        let input_slot = RSV::new_value(0, Provenance::Synthetic);
        let input_index = RSV::new_value(1, Provenance::Synthetic);
        let dyn_array = RSV::new_synthetic(
            2,
            RSVD::DynamicArrayIndex {
                slot:  input_slot.clone(),
                index: input_index.clone(),
            },
        );

        let state = TypeCheckerState::empty();
        let result = StorageSlots.run(dyn_array, &state)?;

        match result.data() {
            RSVD::DynamicArrayIndex { slot, index } => {
                assert_eq!(index, &input_index);

                match slot.data() {
                    RSVD::StorageSlot { key } => {
                        assert_eq!(key, &input_slot);
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn does_not_re_wrap_slots_in_mappings() -> anyhow::Result<()> {
        let input_slot = RSV::new_synthetic(
            0,
            RSVD::StorageSlot {
                key: RSV::new_value(1, Provenance::Synthetic),
            },
        );
        let mapping_key = RSV::new_value(1, Provenance::Synthetic);
        let mapping_access = RSV::new_synthetic(
            2,
            RSVD::MappingIndex {
                key:        mapping_key.clone(),
                slot:       input_slot.clone(),
                projection: None,
            },
        );

        let state = TypeCheckerState::empty();
        let result = StorageSlots.run(mapping_access, &state)?;

        match result.data() {
            RSVD::MappingIndex {
                key,
                slot,
                projection,
            } => {
                assert!(projection.is_none());
                assert_eq!(key, &mapping_key);
                assert_eq!(slot, &input_slot);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn does_not_re_wrap_slots_in_s_stores() -> anyhow::Result<()> {
        let input_slot = RSV::new_synthetic(
            0,
            RSVD::StorageSlot {
                key: RSV::new_value(1, Provenance::Synthetic),
            },
        );
        let storage_value = RSV::new_value(1, Provenance::Synthetic);
        let storage_store = RSV::new_synthetic(
            2,
            RSVD::StorageWrite {
                key:   input_slot.clone(),
                value: storage_value.clone(),
            },
        );

        let state = TypeCheckerState::empty();
        let result = StorageSlots.run(storage_store, &state)?;

        match result.data() {
            RSVD::StorageWrite { key, value } => {
                assert_eq!(key, &input_slot);
                assert_eq!(value, &storage_value);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn does_not_re_wrap_slots_in_dyn_arrays() -> anyhow::Result<()> {
        let input_slot = RSV::new_synthetic(
            0,
            RSVD::StorageSlot {
                key: RSV::new_value(1, Provenance::Synthetic),
            },
        );
        let input_index = RSV::new_value(1, Provenance::Synthetic);
        let dyn_array = RSV::new_synthetic(
            2,
            RSVD::DynamicArrayIndex {
                slot:  input_slot.clone(),
                index: input_index.clone(),
            },
        );

        let state = TypeCheckerState::empty();
        let result = StorageSlots.run(dyn_array, &state)?;

        match result.data() {
            RSVD::DynamicArrayIndex { slot, index } => {
                assert_eq!(index, &input_index);
                assert_eq!(slot, &input_slot);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn wraps_slots_in_s_loads() -> anyhow::Result<()> {
        let input_key = RSV::new_value(0, Provenance::Synthetic);
        let input_value = RSV::new_value(0, Provenance::Synthetic);
        let s_load = RSV::new_synthetic(
            1,
            RSVD::SLoad {
                key:   input_key.clone(),
                value: input_value.clone(),
            },
        );

        let state = TypeCheckerState::empty();
        let result = StorageSlots.run(s_load, &state)?;

        match result.data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(value, &input_value);
                match key.data() {
                    RSVD::StorageSlot { key } => {
                        assert_eq!(key, &input_key);
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }
}
