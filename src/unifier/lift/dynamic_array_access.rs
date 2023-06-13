//! This module contains definition of a lifting pass that recognises dynamic
//! array accesses and makes them constant.

use crate::{
    unifier::{lift::Lift, state::TypingState},
    vm::value::{BoxedVal, SV, SVD},
};

/// This pass detects and lifts expressions that perform dynamic array accesses
/// in storage.
///
/// These have a form as follows:
///
/// ```code
/// s_store(sha3(slot) + index), value)
/// ```
///
/// where:
/// - `slot` is the storage slot key.
/// - The `sha3(slot)` expression may be constant-folded.
/// - `index` is the index in the array to write to.
/// - `value` is the value to be written to `index` in the array.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DynamicArrayAccess;

impl DynamicArrayAccess {
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }
}

impl Lift for DynamicArrayAccess {
    fn run(
        &mut self,
        value: BoxedVal,
        _state: &TypingState,
    ) -> crate::error::unification::Result<BoxedVal> {
        fn lift_dyn_array_accesses(value: &SVD) -> Option<SVD> {
            let SVD::StorageWrite { key, value } = &value else { return None };
            let SVD::Add {left, right} = &key.data else { return None };

            // We have to deal with two cases, the raw hash, and the optimised hash
            let slot = match &left.data {
                SVD::StorageSlot { .. } => left.clone().transform_data(lift_dyn_array_accesses),
                SVD::Sha3 { data } => match &data.data {
                    SVD::KnownData { .. } => data.clone().transform_data(lift_dyn_array_accesses),
                    _ => return None,
                },
                _ => return None,
            };

            let access = SV::new(
                key.instruction_pointer,
                SVD::DynamicArrayAccess {
                    slot,
                    index: right.clone().transform_data(lift_dyn_array_accesses),
                },
                key.provenance,
            );

            let value = SVD::StorageWrite {
                key:   access,
                value: value.clone(),
            };

            Some(value)
        }

        Ok(value.transform_data(lift_dyn_array_accesses))
    }
}

#[cfg(test)]
mod test {
    use crate::{
        unifier::{
            lift::{dynamic_array_access::DynamicArrayAccess, Lift},
            state::TypingState,
        },
        vm::value::{known::KnownWord, Provenance, SV, SVD},
    };

    #[test]
    fn lifts_optimised_dyn_array_accesses() -> anyhow::Result<()> {
        // Prepare the data
        let input_value = SV::new_value(0, Provenance::Synthetic);
        let input_index = SV::new_value(1, Provenance::Synthetic);
        let hash = SV::new(
            2,
            SVD::StorageSlot {
                key: SV::new_known_value(3, KnownWord::from(3), Provenance::Synthetic),
            },
            Provenance::Synthetic,
        );
        let add = SV::new(
            3,
            SVD::Add {
                left:  hash.clone(),
                right: input_index.clone(),
            },
            Provenance::Synthetic,
        );
        let store = SV::new(
            4,
            SVD::StorageWrite {
                key:   add,
                value: input_value.clone(),
            },
            Provenance::Synthetic,
        );

        // Run the pass
        let state = TypingState::empty();
        let result = DynamicArrayAccess.run(store, &state)?;

        // Inspect the result
        match result.data {
            SVD::StorageWrite { key, value } => {
                assert_eq!(value, input_value);

                match key.data {
                    SVD::DynamicArrayAccess { slot, index } => {
                        assert_eq!(index, input_index);
                        assert_eq!(slot, hash)
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn lifts_unoptimised_dyn_array_accesses() -> anyhow::Result<()> {
        let input_value = SV::new_value(0, Provenance::Synthetic);
        let input_index = SV::new_value(1, Provenance::Synthetic);
        let input_slot = SV::new_known_value(3, KnownWord::from(3), Provenance::Synthetic);
        let hash = SV::new(
            2,
            SVD::Sha3 {
                data: input_slot.clone(),
            },
            Provenance::Synthetic,
        );
        let add = SV::new(
            3,
            SVD::Add {
                left:  hash,
                right: input_index.clone(),
            },
            Provenance::Synthetic,
        );
        let store = SV::new(
            4,
            SVD::StorageWrite {
                key:   add,
                value: input_value.clone(),
            },
            Provenance::Synthetic,
        );

        // Run the pass
        let state = TypingState::empty();
        let result = DynamicArrayAccess.run(store, &state)?;

        // Inspect the result
        match result.data {
            SVD::StorageWrite { key, value } => {
                assert_eq!(value, input_value);

                match key.data {
                    SVD::DynamicArrayAccess { slot, index } => {
                        assert_eq!(index, input_index);
                        assert_eq!(slot, input_slot);
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }
}
