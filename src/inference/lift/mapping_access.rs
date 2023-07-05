//! This module provides a lifting pass that recognises accesses to
//! individual storage slots as part of a mapping.

use crate::{
    inference::{lift::Lift, state::InferenceState},
    vm::value::{BoxedVal, SVD},
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
        value: BoxedVal,
        _state: &InferenceState,
    ) -> crate::error::unification::Result<BoxedVal> {
        fn insert_mapping_accesses(data: &SVD) -> Option<SVD> {
            let SVD::Sha3 { data } = data else {
                return None;
            };
            let SVD::Concat { values } = &data.data else {
                return None;
            };
            let [key, slot] = &values[..] else {
                return None;
            };

            Some(SVD::MappingAccess {
                key:  key.clone().transform_data(insert_mapping_accesses),
                slot: slot.clone().transform_data(insert_mapping_accesses),
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
        vm::value::{known::KnownWord, Provenance, SymbolicValue, SVD},
    };

    #[test]
    fn resolves_mapping_accesses_at_top_level() -> anyhow::Result<()> {
        let input_key = SymbolicValue::new_value(0, Provenance::Synthetic);
        let input_slot =
            SymbolicValue::new_known_value(1, KnownWord::from(10), Provenance::Synthetic);
        let concat = SymbolicValue::new(
            2,
            SVD::Concat {
                values: vec![input_key.clone(), input_slot.clone()],
            },
            Provenance::Synthetic,
        );
        let hash = SymbolicValue::new(3, SVD::Sha3 { data: concat }, Provenance::Synthetic);

        let state = InferenceState::empty();
        let result = MappingAccess.run(hash, &state)?;

        match result.data {
            SVD::MappingAccess { key, slot } => {
                assert_eq!(key, input_key);
                assert_eq!(slot, input_slot);
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }

    #[test]
    fn resolves_mapping_accesses_while_nested() -> anyhow::Result<()> {
        let input_key = SymbolicValue::new_value(0, Provenance::Synthetic);
        let input_slot =
            SymbolicValue::new_known_value(1, KnownWord::from(10), Provenance::Synthetic);
        let concat = SymbolicValue::new(
            2,
            SVD::Concat {
                values: vec![input_key.clone(), input_slot.clone()],
            },
            Provenance::Synthetic,
        );
        let inner_hash = SymbolicValue::new(3, SVD::Sha3 { data: concat }, Provenance::Synthetic);
        let outer_concat = SymbolicValue::new(
            2,
            SVD::Concat {
                values: vec![input_key.clone(), inner_hash],
            },
            Provenance::Synthetic,
        );
        let outer_hash =
            SymbolicValue::new(3, SVD::Sha3 { data: outer_concat }, Provenance::Synthetic);

        let state = InferenceState::empty();
        let result = MappingAccess.run(outer_hash, &state)?;

        match result.data {
            SVD::MappingAccess { key, slot } => {
                assert_eq!(key, input_key);

                match slot.data {
                    SVD::MappingAccess { key, slot } => {
                        assert_eq!(key, input_key);
                        assert_eq!(slot, input_slot);
                    }
                    _ => panic!("Invalid payload"),
                }
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }
}
