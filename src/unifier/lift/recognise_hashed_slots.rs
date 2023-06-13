//! This module contains a lifting pass that recognises the keccaks of the first
//! [`SLOT_COUNT`] storage slot indices in order to make the recognition of
//! dynamic array accesses easier.
use bimap::BiMap;
use ethnum::U256;
use sha3::{Digest, Keccak256};

use crate::{
    unifier::{lift::Lift, state::TypingState},
    vm::value::{known::KnownWord, BoxedVal, SV, SVD},
};

/// The number of storage indices for which hashes will be generated (and hence
/// recognised).
pub const SLOT_COUNT: usize = 1000;

/// This pass detects and lifts expressions that appear to be the hashes of the
/// first [`SLOT_COUNT`] storage slots.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct StorageSlotHashes;

impl StorageSlotHashes {
    /// Creates a new instance of the mapping access lifting pass.
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }

    /// Generates the slot hashes for the first `count` slots, assuming
    /// big-endian (network) byte ordering.
    pub fn slot_hashes(count: usize) -> BiMap<U256, usize> {
        let mut data = BiMap::new();

        for slot_ix in 0..count {
            let mut hasher = Keccak256::new();
            hasher.update(U256::from(slot_ix as u64).to_be_bytes());
            let hash = hasher.finalize().to_vec();
            let key = U256::from_be_bytes(hash.as_slice().try_into().unwrap());
            data.insert(key, slot_ix);
        }

        data
    }
}

impl Lift for StorageSlotHashes {
    fn run(
        &mut self,
        value: BoxedVal,
        _state: &TypingState,
    ) -> crate::error::unification::Result<BoxedVal> {
        let hashes = StorageSlotHashes::slot_hashes(SLOT_COUNT);
        let value_clone = value.clone();
        let lift_hashes = |input_value: &SVD| {
            let SVD::KnownData { value: known_value } = input_value else { return None };

            // Now we can look up the hash we found, and convert it to a known slot if we
            // get a result
            if let Some(slot_index) = hashes.get_by_left(&known_value.value()) {
                let key = SV::new_known_value(
                    value_clone.instruction_pointer,
                    KnownWord::from(*slot_index),
                    value_clone.provenance,
                );

                Some(SVD::StorageSlot { key })
            } else {
                None
            }
        };

        Ok(value.transform_data(lift_hashes))
    }
}

#[cfg(test)]
mod test {
    use crate::{
        unifier::{
            lift::{recognise_hashed_slots::StorageSlotHashes, Lift},
            state::TypingState,
        },
        vm::value::{known::KnownWord, Provenance, SV, SVD},
    };

    #[test]
    #[allow(clippy::needless_range_loop)] // Clearer way to write it for the test
    fn computes_first_five_hashes_correctly() {
        // A vec of expected hashes
        let hashes = vec![
            "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
            "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
            "405787fa12a823e0f2b7631cc41b3ba8828b3321ca811111fa75cd3aa3bb5ace",
            "c2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b",
            "8a35acfbc15ff81a39ae7d344fd709f28e8600b4aa8c65c6b64bfe7fe36bd19b",
        ];

        // Get the first five slot indices as hashes.
        let hash_count = 5;
        let hashes_map = StorageSlotHashes::slot_hashes(hash_count);

        for index in 0..hash_count {
            let slot_expected = util::expected_hash_from_be_hex_string(hashes[index]);
            let slot_actual = hashes_map.get_by_right(&index).unwrap();
            assert_eq!(slot_actual, &slot_expected);
        }
    }

    #[test]
    fn can_recognise_a_slot_hash_in_lifting() -> anyhow::Result<()> {
        let word = KnownWord::from(util::expected_hash_from_be_hex_string(
            "c2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b",
        ));
        let value = SV::new_known_value(0, word, Provenance::Synthetic);

        // Run the pass
        let state = TypingState::empty();
        let result = StorageSlotHashes.run(value, &state)?;

        // Check the structure
        match result.data {
            SVD::StorageSlot { key } => match key.data {
                SVD::KnownData { value } => {
                    assert_eq!(value, KnownWord::from(3))
                }

                _ => panic!("Incorrect payload"),
            },
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    mod util {
        use ethnum::U256;

        pub fn expected_hash_from_be_hex_string(string: impl Into<String>) -> U256 {
            let bytes = hex::decode(string.into().bytes().collect::<Vec<_>>())
                .expect("Hash was not valid as text");
            assert_eq!(bytes.len(), 32);
            let key = U256::from_be_bytes(
                bytes.as_slice().try_into().expect("Wrong number of decoded bytes"),
            );
            key
        }
    }
}
