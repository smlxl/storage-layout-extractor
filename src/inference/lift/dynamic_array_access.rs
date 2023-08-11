//! This module contains definition of a lifting pass that recognises dynamic
//! array accesses and makes them constant.

use crate::{
    inference::{lift::Lift, state::InferenceState},
    vm::value::{RuntimeBoxedVal, RSV, RSVD},
};

/// This pass detects and lifts expressions that perform dynamic array accesses
/// in storage.
///
/// These have a form as follows:
///
/// ```code
/// s_store((sha3(slot) + index), value)
///
/// becomes
///
/// s_store(dynamic_array<slot>[index], value)
/// ```
///
/// where:
/// - `slot` is the storage slot key.
/// - `index` is the index in the array to write to.
/// - `value` is the value to be written to `index` in the array.
///
/// Note that this pass must be run _after_
/// [`crate::inference::lift::recognise_hashed_slots::StorageSlotHashes`] as it
/// relies on its results.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DynamicArrayAccess;

impl DynamicArrayAccess {
    #[must_use]
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }
}

impl Lift for DynamicArrayAccess {
    fn run(
        &mut self,
        value: RuntimeBoxedVal,
        _state: &InferenceState,
    ) -> crate::error::unification::Result<RuntimeBoxedVal> {
        fn lift_dyn_array_accesses(value: &RSVD) -> Option<RSVD> {
            let RSVD::StorageWrite { key, value } = &value else {
                return None;
            };
            let RSVD::Add { left, right } = &key.data else {
                return None;
            };

            // Important to check if either side of the addition is the hash
            let data = if let RSVD::Sha3 { data } = &left.data {
                data
            } else if let RSVD::Sha3 { data } = &right.data {
                data
            } else {
                return None;
            }
            .clone()
            .constant_fold();
            let RSVD::KnownData { .. } = &data.data else {
                return None;
            };

            let access = RSV::new(
                key.instruction_pointer,
                RSVD::DynamicArrayAccess {
                    slot:  data.transform_data(lift_dyn_array_accesses),
                    index: right.clone().transform_data(lift_dyn_array_accesses),
                },
                key.provenance,
            );

            let value = RSVD::StorageWrite {
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
        inference::{
            lift::{dynamic_array_access::DynamicArrayAccess, Lift},
            state::InferenceState,
        },
        vm::value::{known::KnownWord, Provenance, RSV, RSVD},
    };

    #[test]
    fn lifts_dyn_array_accesses() -> anyhow::Result<()> {
        let input_value = RSV::new_value(0, Provenance::Synthetic);
        let input_index = RSV::new_value(1, Provenance::Synthetic);
        let input_slot = RSV::new_known_value(3, KnownWord::from(3), Provenance::Synthetic);
        let hash = RSV::new(
            2,
            RSVD::Sha3 {
                data: input_slot.clone(),
            },
            Provenance::Synthetic,
        );
        let add = RSV::new(
            3,
            RSVD::Add {
                left:  hash,
                right: input_index.clone(),
            },
            Provenance::Synthetic,
        );
        let store = RSV::new(
            4,
            RSVD::StorageWrite {
                key:   add,
                value: input_value.clone(),
            },
            Provenance::Synthetic,
        );

        // Run the pass
        let state = InferenceState::empty();
        let result = DynamicArrayAccess.run(store, &state)?;

        // Inspect the result
        match result.data {
            RSVD::StorageWrite { key, value } => {
                assert_eq!(value, input_value);

                match key.data {
                    RSVD::DynamicArrayAccess { slot, index } => {
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
