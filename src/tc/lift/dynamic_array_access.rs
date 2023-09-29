//! This module contains definition of a lifting pass that recognises dynamic
//! array indices and makes them constant.

use crate::{
    tc::{lift::Lift, state::TypeCheckerState},
    vm::value::{RuntimeBoxedVal, RSVD},
};

/// This pass detects and lifts expressions that perform dynamic array indices
/// in storage.
///
/// These have a form as follows:
///
/// ```code
/// s_store((sha3(slot) + index), value)
///
/// becomes
///
/// s_store(dyn_array_ix<slot>[index], value)
/// ```
///
/// where:
/// - `slot` is the storage slot key.
/// - `index` is the index in the array to write to.
/// - `value` is the value to be written to `index` in the array.
///
/// Note that this pass must be run _after_
/// [`crate::tc::lift::recognise_hashed_slots::StorageSlotHashes`] as it
/// relies on its results.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DynamicArrayIndex;

impl DynamicArrayIndex {
    #[must_use]
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }
}

impl Lift for DynamicArrayIndex {
    fn run(
        &mut self,
        value: RuntimeBoxedVal,
        _state: &TypeCheckerState,
    ) -> crate::error::unification::Result<RuntimeBoxedVal> {
        fn guard_dyn_array_accesses(data: &RSVD) -> Option<RSVD> {
            match data {
                RSVD::StorageWrite { key, value } => Some(RSVD::StorageWrite {
                    key:   key.clone().transform_data(lift_dyn_array_accesses),
                    value: value.clone().transform_data(lift_dyn_array_accesses),
                }),
                RSVD::SLoad { key, value } => Some(RSVD::SLoad {
                    key:   key.clone().transform_data(lift_dyn_array_accesses),
                    value: value.clone().transform_data(lift_dyn_array_accesses),
                }),
                RSVD::UnwrittenStorageValue { key } => Some(RSVD::UnwrittenStorageValue {
                    key: key.clone().transform_data(lift_dyn_array_accesses),
                }),
                _ => None,
            }
        }

        fn lift_dyn_array_accesses(value: &RSVD) -> Option<RSVD> {
            let RSVD::Add { left, right } = value else {
                return None;
            };

            // Important to check if either side of the addition is the hash
            let data = if let RSVD::Sha3 { data } = left.data() {
                data
            } else if let RSVD::Sha3 { data } = right.data() {
                data
            } else {
                return None;
            }
            .clone();

            let data = match data.data() {
                RSVD::Concat { values } if values.len() == 1 => values[0].constant_fold(),
                RSVD::Concat { .. } => return None,
                _ => data,
            };

            let access = RSVD::DynamicArrayIndex {
                slot:  data.transform_data(lift_dyn_array_accesses),
                index: right.clone().transform_data(lift_dyn_array_accesses),
            };

            Some(access)
        }

        Ok(value.transform_data(guard_dyn_array_accesses))
    }
}

#[cfg(test)]
mod test {
    use crate::{
        tc::{
            lift::{dynamic_array_access::DynamicArrayIndex, Lift},
            state::TypeCheckerState,
        },
        vm::value::{known::KnownWord, Provenance, RSV, RSVD},
    };

    #[test]
    fn lifts_dyn_array_accesses() -> anyhow::Result<()> {
        let input_value = RSV::new_value(0, Provenance::Synthetic);
        let input_index = RSV::new_value(1, Provenance::Synthetic);
        let input_slot = RSV::new_known_value(3, KnownWord::from(3), Provenance::Synthetic, None);
        let hash = RSV::new_synthetic(
            2,
            RSVD::Sha3 {
                data: input_slot.clone(),
            },
        );
        let add = RSV::new_synthetic(
            3,
            RSVD::Add {
                left:  hash,
                right: input_index.clone(),
            },
        );
        let store = RSV::new_synthetic(
            4,
            RSVD::StorageWrite {
                key:   add,
                value: input_value.clone(),
            },
        );

        // Run the pass
        let state = TypeCheckerState::empty();
        let result = DynamicArrayIndex.run(store, &state)?;

        // Inspect the result
        match result.data() {
            RSVD::StorageWrite { key, value } => {
                assert_eq!(value, &input_value);

                match key.data() {
                    RSVD::DynamicArrayIndex { slot, index } => {
                        assert_eq!(index, &input_index);
                        assert_eq!(slot, &input_slot);
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }
}
