//! This module provides a lifting pass that recognises accesses to individual
//! storage slots as part of a mapping.

use crate::{
    tc::{lift::Lift, state::TypeCheckerState},
    vm::value::{RuntimeBoxedVal, RSVD},
};

/// This pass detects and folds expressions that represent indices into mappings
/// in storage.
///
/// These have a form as follows:
///
/// ```code
/// sha3(concat(key, slot_ix))
///
/// becomes
///
/// mapping_ix<slot_ix>[key]
/// ```
///
/// We only perform this resolution underneath [`RSVD::StorageWrite`],
/// [`RSVD::SLoad`] and [`RSVD::UnwrittenStorageValue`] to ensure that we do not
/// inadvertently capture non-mapping access patterns as mappings.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MappingIndex;

impl MappingIndex {
    /// Constructs a new instance of the mapping access lifting pass.
    #[must_use]
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }
}

impl Lift for MappingIndex {
    fn run(
        &mut self,
        value: RuntimeBoxedVal,
        _state: &TypeCheckerState,
    ) -> crate::error::unification::Result<RuntimeBoxedVal> {
        fn guard_mapping_accesses(data: &RSVD) -> Option<RSVD> {
            match data {
                RSVD::StorageWrite { key, value } => Some(RSVD::StorageWrite {
                    key:   key.clone().transform_data(insert_mapping_accesses),
                    value: value.clone().transform_data(insert_mapping_accesses),
                }),
                RSVD::SLoad { key, value } => Some(RSVD::SLoad {
                    key:   key.clone().transform_data(insert_mapping_accesses),
                    value: value.clone().transform_data(insert_mapping_accesses),
                }),
                RSVD::UnwrittenStorageValue { key } => Some(RSVD::UnwrittenStorageValue {
                    key: key.clone().transform_data(insert_mapping_accesses),
                }),
                _ => None,
            }
        }

        fn insert_mapping_accesses(data: &RSVD) -> Option<RSVD> {
            let RSVD::Sha3 { data } = data else {
                return None;
            };
            let RSVD::Concat { values } = data.data() else {
                return None;
            };
            let [key, slot] = &values[..] else {
                return None;
            };

            Some(RSVD::MappingIndex {
                key:        key.clone().transform_data(insert_mapping_accesses),
                slot:       slot.clone().transform_data(insert_mapping_accesses),
                projection: None,
            })
        }

        Ok(value.transform_data(guard_mapping_accesses))
    }
}

#[cfg(test)]
mod test {
    use crate::{
        tc::{
            lift::{mapping_index::MappingIndex, Lift},
            state::TypeCheckerState,
        },
        vm::value::{known::KnownWord, Provenance, RSV, RSVD},
    };

    #[test]
    fn resolves_mapping_accesses_at_top_level() -> anyhow::Result<()> {
        let input_key = RSV::new_value(0, Provenance::Synthetic);
        let input_slot = RSV::new_known_value(1, KnownWord::from(10), Provenance::Synthetic, None);
        let concat = RSV::new_synthetic(
            2,
            RSVD::Concat {
                values: vec![input_key.clone(), input_slot.clone()],
            },
        );
        let hash = RSV::new_synthetic(3, RSVD::Sha3 { data: concat });
        let slot_key = RSV::new_value(4, Provenance::Synthetic);
        let s_load = RSV::new_synthetic(
            5,
            RSVD::SLoad {
                key:   slot_key.clone(),
                value: hash.clone(),
            },
        );

        let state = TypeCheckerState::empty();
        let result = MappingIndex.run(s_load, &state)?;

        match result.data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(key, &slot_key);

                match value.data() {
                    RSVD::MappingIndex {
                        key,
                        slot,
                        projection,
                    } => {
                        assert!(projection.is_none());
                        assert_eq!(key, &input_key);
                        assert_eq!(slot, &input_slot);
                    }
                    _ => panic!("Invalid payload"),
                }
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }

    #[test]
    fn resolves_mapping_accesses_while_nested() -> anyhow::Result<()> {
        let input_key = RSV::new_value(0, Provenance::Synthetic);
        let input_slot = RSV::new_known_value(1, KnownWord::from(10), Provenance::Synthetic, None);
        let concat = RSV::new_synthetic(
            2,
            RSVD::Concat {
                values: vec![input_key.clone(), input_slot.clone()],
            },
        );
        let inner_hash = RSV::new_synthetic(3, RSVD::Sha3 { data: concat });
        let outer_concat = RSV::new_synthetic(
            4,
            RSVD::Concat {
                values: vec![input_key.clone(), inner_hash],
            },
        );
        let outer_hash = RSV::new_synthetic(5, RSVD::Sha3 { data: outer_concat });
        let slot_key = RSV::new_value(6, Provenance::Synthetic);
        let s_store = RSV::new_synthetic(
            7,
            RSVD::StorageWrite {
                key:   slot_key.clone(),
                value: outer_hash.clone(),
            },
        );

        let state = TypeCheckerState::empty();
        let result = MappingIndex.run(s_store, &state)?;

        match result.data() {
            RSVD::StorageWrite { key, value } => {
                assert_eq!(key, &slot_key);

                match value.data() {
                    RSVD::MappingIndex {
                        key,
                        slot,
                        projection,
                    } => {
                        assert!(projection.is_none());
                        assert_eq!(key, &input_key);

                        match slot.data() {
                            RSVD::MappingIndex {
                                key,
                                slot,
                                projection,
                            } => {
                                assert!(projection.is_none());
                                assert_eq!(key, &input_key);
                                assert_eq!(slot, &input_slot);
                            }
                            _ => panic!("Invalid payload"),
                        }
                    }
                    _ => panic!("Invalid payload"),
                }
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }
}
