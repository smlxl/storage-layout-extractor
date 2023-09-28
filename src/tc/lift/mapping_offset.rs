//! This module provides a lifting pass that recognises offset accesses to
//! mapping storage slots to account for larger structs as mapping values.

use crate::{
    tc::{lift::Lift, state::TypeCheckerState},
    vm::value::{RuntimeBoxedVal, RSVD},
};

/// This pass detects and folds expressions that access values in mappings that
/// are larger than one word.
///
/// ```code
/// slot<offset + mapping_ix<slot_ix>[key][0]>
///
/// becomes
///
/// slot<mapping_ix<slot_ix>[key][offset]>
/// ```
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MappingOffset;

impl MappingOffset {
    /// Constructs a new instance of the mapping offset lifting pass.
    #[must_use]
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }
}

impl Lift for MappingOffset {
    fn run(
        &mut self,
        value: RuntimeBoxedVal,
        _state: &TypeCheckerState,
    ) -> crate::error::unification::Result<RuntimeBoxedVal> {
        fn insert_mapping_offset(data: &RSVD) -> Option<RSVD> {
            let RSVD::Add { left, right } = data else { return None };

            let (key, slot, offset) = match (left.data(), right.data()) {
                (RSVD::MappingIndex { key, slot, .. }, RSVD::KnownData { value })
                | (RSVD::KnownData { value }, RSVD::MappingIndex { key, slot, .. }) => {
                    (key, slot, value.into())
                }
                _ => return None,
            };

            Some(RSVD::MappingIndex {
                key:        key.clone().transform_data(insert_mapping_offset),
                slot:       slot.clone().transform_data(insert_mapping_offset),
                projection: Some(offset),
            })
        }

        Ok(value.transform_data(insert_mapping_offset))
    }
}

#[cfg(test)]
mod test {
    use crate::{
        tc::{
            lift::{mapping_offset::MappingOffset, Lift},
            state::TypeCheckerState,
        },
        vm::value::{known::KnownWord, Provenance, RSV, RSVD},
    };

    #[test]
    fn discovers_mapping_offsets_at_top_level() -> anyhow::Result<()> {
        // Create some input values
        let input_key = RSV::new_value(0, Provenance::Synthetic);
        let input_slot = RSV::new_known_value(1, KnownWord::from(10), Provenance::Synthetic, None);
        let mapping = RSV::new_synthetic(
            2,
            RSVD::MappingIndex {
                slot:       input_slot.clone(),
                key:        input_key.clone(),
                projection: None,
            },
        );
        let constant = RSV::new_known_value(3, KnownWord::from(256), Provenance::Synthetic, None);
        let add = RSV::new_synthetic(
            4,
            RSVD::Add {
                left:  mapping.clone(),
                right: constant.clone(),
            },
        );

        // Run the lifting pass
        let state = TypeCheckerState::empty();
        let result = MappingOffset.run(add, &state)?;

        // Check that the values make sense
        match result.data() {
            RSVD::MappingIndex {
                key,
                slot,
                projection,
            } => {
                assert_eq!(key, &input_key);
                assert_eq!(slot, &input_slot);
                assert_eq!(projection, &Some(256));
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn discovers_mapping_offsets_when_nested() -> anyhow::Result<()> {
        // Create some input values
        let input_key = RSV::new_value(0, Provenance::Synthetic);
        let input_slot = RSV::new_known_value(1, KnownWord::from(10), Provenance::Synthetic, None);
        let inner_mapping = RSV::new_synthetic(
            2,
            RSVD::MappingIndex {
                slot:       input_slot.clone(),
                key:        input_key.clone(),
                projection: None,
            },
        );
        let inner_constant =
            RSV::new_known_value(3, KnownWord::from(256), Provenance::Synthetic, None);
        let inner_add = RSV::new_synthetic(
            4,
            RSVD::Add {
                left:  inner_mapping.clone(),
                right: inner_constant.clone(),
            },
        );
        let outer_mapping = RSV::new_synthetic(
            5,
            RSVD::MappingIndex {
                slot:       inner_add.clone(),
                key:        input_key.clone(),
                projection: None,
            },
        );
        let outer_constant =
            RSV::new_known_value(6, KnownWord::from(512), Provenance::Synthetic, None);
        let outer_add = RSV::new_synthetic(
            7,
            RSVD::Add {
                left:  outer_constant.clone(),
                right: outer_mapping.clone(),
            },
        );

        // Run the lifting pass
        let state = TypeCheckerState::empty();
        let result = MappingOffset.run(outer_add, &state)?;

        // Check that the results make sense
        match result.data() {
            RSVD::MappingIndex {
                key,
                slot,
                projection,
            } => {
                assert_eq!(key, &input_key);
                assert_eq!(projection, &Some(512));

                match slot.data() {
                    RSVD::MappingIndex {
                        key,
                        slot,
                        projection,
                    } => {
                        assert_eq!(key, &input_key);
                        assert_eq!(slot, &input_slot);
                        assert_eq!(projection, &Some(256));
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }
}
