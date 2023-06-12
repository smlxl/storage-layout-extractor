//! This module provides a re-sugaring pass that recognises accesses to storage
//! slots, and wraps the constant slots in fixed expressions.

use crate::{
    unifier::{state::UnifierState, sugar::ReSugar},
    vm::value::{BoxedVal, SymbolicValue, SVD},
};

/// This pass detects and wraps expressions that access constant storage slots
/// so that these constants can be distinguished from other constants of the
/// same value.
///
/// This pass relies on the results of the [`super::mapping_access`] pass, and
/// hence must be ordered after it in the re-sugar pass ordering.
///
/// # Note
///
/// It currently only recognises one case (mappings), but will be extended in
/// the future alongside other re-sugaring passes.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct StorageSlots;

impl StorageSlots {
    /// Constructs a new instance of the storage slot access re-sugaring pass.
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }
}

impl ReSugar for StorageSlots {
    fn run(
        &mut self,
        value: BoxedVal,
        _state: &mut UnifierState,
    ) -> crate::error::unification::Result<BoxedVal> {
        fn insert_storage_accesses(data: &SVD) -> Option<SVD> {
            match data {
                SVD::MappingAddress { key, slot } => {
                    let SVD::KnownData { value } = &slot.data else { return None };
                    let slot = SymbolicValue::new(
                        slot.instruction_pointer,
                        SVD::StorageSlot { index: *value },
                        slot.provenance,
                    );
                    Some(SVD::MappingAddress {
                        key: key.clone(),
                        slot,
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
        unifier::{
            state::UnifierState,
            sugar::{storage_slots::StorageSlots, ReSugar},
        },
        vm::value::{known::KnownWord, Provenance, SymbolicValue, SVD},
    };

    #[test]
    fn lifts_storage_slots_in_mappings_at_top_level() -> anyhow::Result<()> {
        let slot_index_constant =
            SymbolicValue::new_known_value(0, KnownWord::from(7), Provenance::Synthetic);
        let mapping_key = SymbolicValue::new_value(1, Provenance::Synthetic);
        let mapping_access = SymbolicValue::new(
            2,
            SVD::MappingAddress {
                key:  mapping_key.clone(),
                slot: slot_index_constant,
            },
            Provenance::Synthetic,
        );

        let mut state = UnifierState::new();
        let result = StorageSlots.run(mapping_access, &mut state)?;

        match result.data {
            SVD::MappingAddress { key, slot } => {
                assert_eq!(key, mapping_key);
                match slot.data {
                    SVD::StorageSlot { index } => {
                        assert_eq!(index, KnownWord::from(7))
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
            SVD::MappingAddress {
                key:  mapping_key.clone(),
                slot: slot_index_constant,
            },
            Provenance::Synthetic,
        );
        let not = SymbolicValue::new(
            3,
            SVD::Not {
                value: mapping_access,
            },
            Provenance::Synthetic,
        );

        let mut state = UnifierState::new();
        let result = StorageSlots.run(not, &mut state)?;

        match result.data {
            SVD::Not { value } => match value.data {
                SVD::MappingAddress { key, slot } => {
                    assert_eq!(key, mapping_key);
                    match slot.data {
                        SVD::StorageSlot { index } => {
                            assert_eq!(index, KnownWord::from(7))
                        }
                        _ => panic!("Incorrect payload"),
                    }
                }
                _ => panic!("Incorrect payload"),
            },
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }
}
