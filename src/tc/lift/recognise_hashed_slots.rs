//! This module contains a lifting pass that recognises the keccaks of the first
//! [`SLOT_COUNT`] storage slot indices in order to make the recognition of
//! dynamic array accesses easier.

use std::sync::{Arc, RwLock};

use bimap::BiMap;
use ethnum::U256;
use sha3::{Digest, Keccak256};

use crate::{
    tc::{lift::Lift, state::TypeCheckerState},
    vm::value::{known::KnownWord, RuntimeBoxedVal, RSV, RSVD},
};

/// The number of storage indices for which hashes will be generated (and hence
/// recognised).
pub const SLOT_COUNT: usize = 10000;

/// This pass detects and lifts expressions that appear to be the hashes of the
/// first [`SLOT_COUNT`] storage slot indices.
///
/// ```text
/// C
///
/// becomes
///
/// sha3(preimage(C))
/// ```
///
/// where:
/// - `C` is the sha3 hash of one of the first [`SLOT_COUNT`] integers.
#[derive(Clone, Debug)]
pub struct StorageSlotHashes {
    hashes: Arc<RwLock<BiMap<U256, usize>>>,
}

impl StorageSlotHashes {
    /// Creates a new instance of the slot hashes lifting pass.
    #[must_use]
    pub fn new() -> Box<Self> {
        let hashes = Arc::new(RwLock::new(Self::make_hashes(SLOT_COUNT)));
        Self::new_with_hashes(hashes)
    }

    // Creates a new instance with the provided hashes
    #[must_use]
    pub fn new_with_hashes(hashes: impl Into<Arc<RwLock<BiMap<U256, usize>>>>) -> Box<Self> {
        Box::new(Self {
            hashes: hashes.into(),
        })
    }

    /// Generates the slot hashes for the first `count` slots, assuming
    /// big-endian (network) byte ordering.
    #[allow(clippy::missing_panics_doc)] // Panics are guarded and should never happen
    #[must_use]
    pub fn make_hashes(count: usize) -> BiMap<U256, usize> {
        let mut data = BiMap::new();

        for slot_ix in 0..count {
            let mut hasher = Keccak256::new();
            hasher.update(U256::from(slot_ix as u64).to_be_bytes());
            let hash = hasher.finalize().to_vec();
            let key = U256::from_be_bytes(
                hash.as_slice()
                    .try_into()
                    .expect("The number of bytes in `hash` should be correct"),
            );
            data.insert(key, slot_ix);
        }

        data
    }
}

impl Lift for StorageSlotHashes {
    fn run(
        &mut self,
        value: RuntimeBoxedVal,
        _state: &TypeCheckerState,
    ) -> crate::error::unification::Result<RuntimeBoxedVal> {
        let hashes = &self.hashes;
        let value_clone = value.clone();
        let lift_hashes = |input_value: &RSVD| {
            let RSVD::KnownData { value: known_value } = input_value else {
                return None;
            };

            // Now we can look up the hash we found, and convert it to the `Sha3` of a known
            // value if it is one.
            match hashes.read() {
                Ok(hashes) => {
                    if let Some(slot_index) = hashes.get_by_left(&known_value.value_le()) {
                        let data = RSV::new_known_value(
                            value_clone.instruction_pointer(),
                            KnownWord::from(*slot_index),
                            value_clone.provenance(),
                            None,
                        );

                        Some(RSVD::Sha3 { data })
                    } else {
                        None
                    }
                }
                _ => None,
            }
        };

        Ok(value.transform_data(lift_hashes))
    }
}

#[cfg(test)]
mod test {
    use crate::{
        tc::{
            lift::{recognise_hashed_slots::StorageSlotHashes, Lift},
            state::TypeCheckerState,
        },
        vm::value::{known::KnownWord, Provenance, RSV, RSVD},
    };

    #[test]
    #[allow(clippy::needless_range_loop)] // Clearer way to write it for the test
    fn computes_first_five_hashes_correctly() {
        // A vec of expected hashes
        let hashes = [
            "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563",
            "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6",
            "405787fa12a823e0f2b7631cc41b3ba8828b3321ca811111fa75cd3aa3bb5ace",
            "c2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b",
            "8a35acfbc15ff81a39ae7d344fd709f28e8600b4aa8c65c6b64bfe7fe36bd19b",
        ];

        // Get the first five slot indices as hashes.
        let hash_count = 5;
        let hashes_map = StorageSlotHashes::make_hashes(hash_count);

        for index in 0..hash_count {
            let slot_expected = util::expected_hash_from_be_hex_string(hashes[index]);
            let slot_actual = hashes_map.get_by_right(&index).unwrap();
            assert_eq!(slot_actual, &slot_expected);
        }
    }

    #[test]
    fn can_recognise_a_slot_hash_in_lifting() -> anyhow::Result<()> {
        let word = KnownWord::from_le(util::expected_hash_from_be_hex_string(
            "c2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b",
        ));
        let value = RSV::new_known_value(0, word, Provenance::Synthetic, None);

        // Run the pass
        let state = TypeCheckerState::empty();
        let result = StorageSlotHashes::new().run(value, &state)?;

        // Check the structure
        match result.data() {
            RSVD::Sha3 { data } => match data.data() {
                RSVD::KnownData { value } => {
                    assert_eq!(value, &KnownWord::from(3));
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
