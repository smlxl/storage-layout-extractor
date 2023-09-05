//! This module provides a lifting pass that recognises accesses to
//! individual storage slots as part of a mapping.

use crate::{
    inference::{lift::Lift, state::InferenceState},
    vm::value::{RuntimeBoxedVal, RSVD},
};

/// This pass detects and folds expressions that access mappings in storage.
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
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MappingAccess;

impl MappingAccess {
    /// Constructs a new instance of the mapping access lifting pass.
    #[must_use]
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }
}

impl Lift for MappingAccess {
    fn run(
        &mut self,
        value: RuntimeBoxedVal,
        _state: &InferenceState,
    ) -> crate::error::unification::Result<RuntimeBoxedVal> {
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

        Ok(value.transform_data(insert_mapping_accesses))
    }
}

#[cfg(test)]
mod test {
    use crate::{
        inference::{
            lift::{mapping_access::MappingAccess, Lift},
            state::InferenceState,
        },
        vm::value::{known::KnownWord, Provenance, RSV, RSVD},
    };

    #[test]
    fn resolves_mapping_accesses_at_top_level() -> anyhow::Result<()> {
        let input_key = RSV::new_value(0, Provenance::Synthetic);
        let input_slot = RSV::new_known_value(1, KnownWord::from(10), Provenance::Synthetic, None);
        let concat = RSV::new(
            2,
            RSVD::Concat {
                values: vec![input_key.clone(), input_slot.clone()],
            },
            Provenance::Synthetic,
            None,
        );
        let hash = RSV::new(3, RSVD::Sha3 { data: concat }, Provenance::Synthetic, None);

        let state = InferenceState::empty();
        let result = MappingAccess.run(hash, &state)?;

        match result.data() {
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

        Ok(())
    }

    #[test]
    fn resolves_mapping_accesses_while_nested() -> anyhow::Result<()> {
        let input_key = RSV::new_value(0, Provenance::Synthetic);
        let input_slot = RSV::new_known_value(1, KnownWord::from(10), Provenance::Synthetic, None);
        let concat = RSV::new(
            2,
            RSVD::Concat {
                values: vec![input_key.clone(), input_slot.clone()],
            },
            Provenance::Synthetic,
            None,
        );
        let inner_hash = RSV::new(3, RSVD::Sha3 { data: concat }, Provenance::Synthetic, None);
        let outer_concat = RSV::new(
            2,
            RSVD::Concat {
                values: vec![input_key.clone(), inner_hash],
            },
            Provenance::Synthetic,
            None,
        );
        let outer_hash = RSV::new(
            3,
            RSVD::Sha3 { data: outer_concat },
            Provenance::Synthetic,
            None,
        );

        let state = InferenceState::empty();
        let result = MappingAccess.run(outer_hash, &state)?;

        match result.data() {
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

        Ok(())
    }
}
