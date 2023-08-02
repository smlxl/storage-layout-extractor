//! This module provides a lifting pass that recognises accesses to storage
//! slots, and wraps the constant slots in fixed expressions.

use crate::{
    inference::{lift::Lift, state::InferenceState},
    vm::value::{BoxedVal, SymbolicValue, SVD},
};

/// This pass detects and wraps expressions that access constant storage slots
/// so that these constants can be distinguished from other constants of the
/// same value.
///
/// This pass relies on the results of the [`super::mapping_access`] pass, and
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
        value: BoxedVal,
        _state: &InferenceState,
    ) -> crate::error::unification::Result<BoxedVal> {
        fn insert_storage_accesses(data: &SVD) -> Option<SVD> {
            match data {
                SVD::MappingAccess { key, slot } => {
                    let data = match &slot.data {
                        SVD::StorageSlot { .. } => slot.data.clone(),
                        _ => SVD::StorageSlot {
                            key: slot.clone().transform_data(insert_storage_accesses),
                        },
                    };
                    let slot = SymbolicValue::new(slot.instruction_pointer, data, slot.provenance);
                    Some(SVD::MappingAccess {
                        key: key.clone().transform_data(insert_storage_accesses),
                        slot,
                    })
                }
                SVD::StorageWrite { key, value } => {
                    let data = match &key.data {
                        SVD::StorageSlot { .. } => key.data.clone(),
                        _ => SVD::StorageSlot {
                            key: key.clone().transform_data(insert_storage_accesses),
                        },
                    };
                    let new_key = SymbolicValue::new(key.instruction_pointer, data, key.provenance);
                    Some(SVD::StorageWrite {
                        key:   new_key,
                        value: value.clone().transform_data(insert_storage_accesses),
                    })
                }
                SVD::DynamicArrayAccess { slot, index } => {
                    let data = match &slot.data {
                        SVD::StorageSlot { .. } => slot.data.clone(),
                        _ => SVD::StorageSlot {
                            key: slot.clone().transform_data(insert_storage_accesses),
                        },
                    };
                    let slot = SymbolicValue::new(slot.instruction_pointer, data, slot.provenance);
                    Some(SVD::DynamicArrayAccess {
                        index: index.clone().transform_data(insert_storage_accesses),
                        slot,
                    })
                }
                SVD::SLoad { key, value } => {
                    let data = match &key.data {
                        SVD::StorageSlot { .. } => key.data.clone(),
                        _ => SVD::StorageSlot {
                            key: key.clone().transform_data(insert_storage_accesses),
                        },
                    };
                    let slot = SymbolicValue::new(key.instruction_pointer, data, key.provenance);
                    Some(SVD::SLoad {
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
        inference::{
            lift::{storage_slots::StorageSlots, Lift},
            state::InferenceState,
        },
        vm::value::{known::KnownWord, Provenance, SymbolicValue, SV, SVD},
    };

    #[test]
    fn lifts_storage_slots_in_mappings_at_top_level() -> anyhow::Result<()> {
        let slot_index_constant =
            SymbolicValue::new_known_value(0, KnownWord::from(7), Provenance::Synthetic);
        let mapping_key = SymbolicValue::new_value(1, Provenance::Synthetic);
        let mapping_access = SymbolicValue::new(
            2,
            SVD::MappingAccess {
                key:  mapping_key.clone(),
                slot: slot_index_constant.clone(),
            },
            Provenance::Synthetic,
        );

        let state = InferenceState::empty();
        let result = StorageSlots.run(mapping_access, &state)?;

        match result.data {
            SVD::MappingAccess { key, slot } => {
                assert_eq!(key, mapping_key);
                match slot.data {
                    SVD::StorageSlot { key } => {
                        assert_eq!(key, slot_index_constant);
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
            SymbolicValue::new_known_value(0, KnownWord::from(7), Provenance::Synthetic);
        let mapping_key = SymbolicValue::new_value(1, Provenance::Synthetic);
        let mapping_access = SymbolicValue::new(
            2,
            SVD::MappingAccess {
                key:  mapping_key.clone(),
                slot: slot_index_constant.clone(),
            },
            Provenance::Synthetic,
        );
        let outer_key = SymbolicValue::new_value(1, Provenance::Synthetic);
        let write = SymbolicValue::new(
            7,
            SVD::StorageWrite {
                key:   outer_key.clone(),
                value: mapping_access,
            },
            Provenance::Synthetic,
        );

        let state = InferenceState::empty();
        let result = StorageSlots.run(write, &state)?;

        match result.data {
            SVD::StorageWrite { key, value } => {
                match key.data {
                    SVD::StorageSlot { key } => {
                        assert_eq!(key, outer_key);
                    }
                    _ => panic!("Incorrect payload"),
                }

                match value.data {
                    SVD::MappingAccess { key, slot } => {
                        assert_eq!(key, mapping_key);
                        match slot.data {
                            SVD::StorageSlot { key } => {
                                assert_eq!(key, slot_index_constant);
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
        let storage_key =
            SymbolicValue::new_known_value(0, KnownWord::from(1), Provenance::Synthetic);
        let storage_value = SymbolicValue::new_value(1, Provenance::Synthetic);
        let storage_store = SymbolicValue::new(
            2,
            SVD::StorageWrite {
                key:   storage_key.clone(),
                value: storage_value.clone(),
            },
            Provenance::Synthetic,
        );

        let state = InferenceState::empty();
        let result = StorageSlots.run(storage_store, &state)?;

        match result.data {
            SVD::StorageWrite { key, value } => match key.data {
                SVD::StorageSlot { key } => {
                    assert_eq!(key, storage_key);
                    assert_eq!(value, storage_value);
                }
                _ => panic!("Incorrect payload"),
            },
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn lifts_storage_slots_in_dyn_arrays() -> anyhow::Result<()> {
        let input_slot = SV::new_value(0, Provenance::Synthetic);
        let input_index = SV::new_value(1, Provenance::Synthetic);
        let dyn_array = SV::new(
            2,
            SVD::DynamicArrayAccess {
                slot:  input_slot.clone(),
                index: input_index.clone(),
            },
            Provenance::Synthetic,
        );

        let state = InferenceState::empty();
        let result = StorageSlots.run(dyn_array, &state)?;

        match result.data {
            SVD::DynamicArrayAccess { slot, index } => {
                assert_eq!(index, input_index);

                match slot.data {
                    SVD::StorageSlot { key } => {
                        assert_eq!(key, input_slot);
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
        let input_slot = SV::new(
            0,
            SVD::StorageSlot {
                key: SV::new_value(1, Provenance::Synthetic),
            },
            Provenance::Synthetic,
        );
        let mapping_key = SymbolicValue::new_value(1, Provenance::Synthetic);
        let mapping_access = SymbolicValue::new(
            2,
            SVD::MappingAccess {
                key:  mapping_key.clone(),
                slot: input_slot.clone(),
            },
            Provenance::Synthetic,
        );

        let state = InferenceState::empty();
        let result = StorageSlots.run(mapping_access, &state)?;

        match result.data {
            SVD::MappingAccess { key, slot } => {
                assert_eq!(key, mapping_key);
                assert_eq!(slot, input_slot);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn does_not_re_wrap_slots_in_s_stores() -> anyhow::Result<()> {
        let input_slot = SV::new(
            0,
            SVD::StorageSlot {
                key: SV::new_value(1, Provenance::Synthetic),
            },
            Provenance::Synthetic,
        );
        let storage_value = SymbolicValue::new_value(1, Provenance::Synthetic);
        let storage_store = SymbolicValue::new(
            2,
            SVD::StorageWrite {
                key:   input_slot.clone(),
                value: storage_value.clone(),
            },
            Provenance::Synthetic,
        );

        let state = InferenceState::empty();
        let result = StorageSlots.run(storage_store, &state)?;

        match result.data {
            SVD::StorageWrite { key, value } => {
                assert_eq!(key, input_slot);
                assert_eq!(value, storage_value);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn does_not_re_wrap_slots_in_dyn_arrays() -> anyhow::Result<()> {
        let input_slot = SV::new(
            0,
            SVD::StorageSlot {
                key: SV::new_value(1, Provenance::Synthetic),
            },
            Provenance::Synthetic,
        );
        let input_index = SV::new_value(1, Provenance::Synthetic);
        let dyn_array = SV::new(
            2,
            SVD::DynamicArrayAccess {
                slot:  input_slot.clone(),
                index: input_index.clone(),
            },
            Provenance::Synthetic,
        );

        let state = InferenceState::empty();
        let result = StorageSlots.run(dyn_array, &state)?;

        match result.data {
            SVD::DynamicArrayAccess { slot, index } => {
                assert_eq!(index, input_index);
                assert_eq!(slot, input_slot);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn wraps_slots_in_s_loads() -> anyhow::Result<()> {
        let input_key = SV::new_value(0, Provenance::Synthetic);
        let input_value = SV::new_value(0, Provenance::Synthetic);
        let s_load = SV::new_synthetic(
            1,
            SVD::SLoad {
                key:   input_key.clone(),
                value: input_value.clone(),
            },
        );

        let state = InferenceState::empty();
        let result = StorageSlots.run(s_load, &state)?;

        match result.data {
            SVD::SLoad { key, value } => {
                assert_eq!(value, input_value);
                match key.data {
                    SVD::StorageSlot { key } => {
                        assert_eq!(key, input_key);
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }
}
