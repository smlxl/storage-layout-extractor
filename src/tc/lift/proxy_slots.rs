//! This module provides a lifting pass that recognises slot indices created
//! using common patterns for proxy storage in proxy contracts.

use ethnum::U256;
use itertools::Itertools;
use sha3::{Digest, Keccak256};

use crate::{
    constant::SOLIDITY_STRING_POINTER,
    tc::{lift::Lift, state::TypeCheckerState},
    vm::value::{known::KnownWord, RuntimeBoxedVal, RSV, RSVD},
};

/// This pass detects and folds expressions that access slots constructed using
/// common patterns for proxy contracts.
///
/// ```code
///  s_load(sha3(c), value) where c = constant or concat(...)
/// s_store(sha3(c), value)
///
/// becomes
///
///  s_load(slot(s), value) where s is computed
/// s_store(slot(s), value) where s is computed
/// ```
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct ProxySlots;

impl ProxySlots {
    /// Constructs a new instance of the proxy slots lifting pass.
    #[must_use]
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }

    /// Calculates the keccak256 hash of the provided `words` in order, using
    /// big-endian byte encoding internally to match the EVM.
    #[allow(clippy::missing_panics_doc)] // Panics are guarded as to never happen
    #[must_use]
    pub fn sha3_known_words(words: &[KnownWord]) -> KnownWord {
        let mut hasher = Keccak256::new();

        for word in words {
            hasher.update(word.bytes_be());
        }

        let hash = hasher.finalize().to_vec();
        let u256 = U256::from_be_bytes(
            hash.as_slice()
                .try_into()
                .expect("The number of bytes in the hash output was not 32"),
        );
        KnownWord::from_le(u256)
    }

    /// Determines if the data in `words` is likely to be a sequence of ascii
    /// characters.
    ///
    /// The string must meet the below likelihood criteria as well as have its
    /// MSB be non-zero.
    ///
    /// # Likelihood
    ///
    /// In particular, it collects all bytes in big-endian byte ordering,
    /// removes any trailing `NUL` bytes, and then checks that all remaining
    /// bytes fall into the ASCII printable range (`0x1f <= c < 0x7f`).
    ///
    /// The chances of _all_ bytes in a byte vector of length `n` being in the
    /// printable ascii character range is `(95/256) ^ n`, so for reasonable
    /// length strings we are probabilistically correct.
    #[must_use]
    pub fn is_likely_string(words: &[KnownWord]) -> bool {
        if let Some(first) = words.first() {
            let msb_non_zero =
                matches!(first.bytes_be().first(), Some(first_byte) if first_byte != &0);
            let stripped = Self::strip_trailing_nuls(words);
            stripped.iter().all(|byte| byte > &0x1f && byte < &0x7f) && msb_non_zero
        } else {
            false
        }
    }

    /// Asserts that the byte length of the byte string described by `words` is
    /// `expected_len`.
    ///
    /// It does this by dropping any trailing `NUL` bytes in the string and then
    /// counting the number of bytes.
    #[must_use]
    pub fn has_correct_number_of_bytes(words: &[KnownWord], expected_len: KnownWord) -> bool {
        let stripped = Self::strip_trailing_nuls(words);
        KnownWord::from(stripped.len()) == expected_len
    }

    /// Strips any trailing `NUL` bytes in the byte string described by `words`.
    #[must_use]
    pub fn strip_trailing_nuls(words: &[KnownWord]) -> Vec<u8> {
        let all_bytes: Vec<u8> = words.iter().flat_map(KnownWord::bytes_be).collect_vec();
        let mut no_trailing_nuls = all_bytes
            .into_iter()
            .rev()
            .skip_while(|byte| byte == &0x0)
            .collect_vec();
        no_trailing_nuls.reverse();

        no_trailing_nuls
    }
}

impl Lift for ProxySlots {
    fn run(
        &mut self,
        value: RuntimeBoxedVal,
        _state: &TypeCheckerState,
    ) -> crate::error::unification::Result<RuntimeBoxedVal> {
        fn unpick_sha3_data(data: &RSVD) -> Option<RSVD> {
            let RSVD::Sha3 { data } = data else { return None };

            let slot_key = match data.data().clone() {
                // In this case, we are directly hashing a constant value
                RSVD::KnownData { value } => {
                    if ProxySlots::is_likely_string(&[value]) {
                        ProxySlots::sha3_known_words(&[value])
                    } else {
                        return None;
                    }
                }
                RSVD::Concat { values } => {
                    // First we constant fold all the values to make it more likely we have data to
                    // work on
                    let words = values
                        .iter()
                        .cloned()
                        .flat_map(|value| {
                            let folded = value.constant_fold();
                            match folded.data() {
                                RSVD::KnownData { value } => vec![*value],
                                _ => Vec::new(),
                            }
                        })
                        .collect_vec();

                    // If the vec of words is not the same length as the input values, we don't have
                    // constants and can't proceed
                    if words.len() != values.len() {
                        return None;
                    }

                    // If we can surmise it to be a non-packed encoding by looking for the string
                    // pointer in the first index, then we can treat the second index as the length
                    if words.len() >= 3 && words[0] == KnownWord::from(SOLIDITY_STRING_POINTER) {
                        let length = words[1];
                        let string_data = &words[2..];

                        // If the length doesn't match, or it doesn't look like a string, we're
                        // wrong about the encoding and bail
                        if !ProxySlots::has_correct_number_of_bytes(string_data, length)
                            || !ProxySlots::is_likely_string(string_data)
                        {
                            return None;
                        }
                    } else if !ProxySlots::is_likely_string(words.as_slice()) {
                        // Even if it does not match an encoding, we expect it to look like a string
                        return None;
                    }

                    ProxySlots::sha3_known_words(words.as_slice())
                }
                _ => return None,
            };

            Some(RSVD::new_known(slot_key))
        }

        fn unpick_proxy_slots(data: &RSVD) -> Option<RSVD> {
            match data {
                RSVD::Add { left, right } => {
                    let (left, right) =
                        if let Some(new_left_payload) = unpick_sha3_data(left.data()) {
                            let new_left = RSV::new(
                                left.instruction_pointer(),
                                new_left_payload,
                                left.provenance(),
                                None,
                            );
                            (new_left, right.clone())
                        } else if let Some(new_right_payload) = unpick_sha3_data(right.data()) {
                            let new_right = RSV::new(
                                right.instruction_pointer(),
                                new_right_payload,
                                right.provenance(),
                                None,
                            );
                            (left.clone(), new_right)
                        } else {
                            return None;
                        };

                    let add = RSVD::Add { left, right };
                    let constant_folded = add.constant_fold();

                    if matches!(constant_folded, RSVD::KnownData { .. }) {
                        Some(constant_folded)
                    } else {
                        None
                    }
                }
                _ => unpick_sha3_data(data),
            }
        }

        fn recognise_proxy_slots(data: &RSVD) -> Option<RSVD> {
            match data {
                RSVD::SLoad { key, value } => Some(RSVD::SLoad {
                    key:   if let Some(new_key) = unpick_proxy_slots(key.data()) {
                        RSV::new(key.instruction_pointer(), new_key, key.provenance(), None)
                    } else {
                        key.clone().transform_data(recognise_proxy_slots)
                    },
                    value: value.clone().transform_data(recognise_proxy_slots),
                }),
                RSVD::StorageWrite { key, value } => Some(RSVD::StorageWrite {
                    key:   if let Some(new_key) = unpick_proxy_slots(key.data()) {
                        RSV::new(key.instruction_pointer(), new_key, key.provenance(), None)
                    } else {
                        key.clone().transform_data(recognise_proxy_slots)
                    },
                    value: value.clone().transform_data(recognise_proxy_slots),
                }),
                _ => None,
            }
        }

        Ok(value.transform_data(recognise_proxy_slots))
    }
}

#[cfg(test)]
mod test {
    use ethnum::U256;
    use itertools::Itertools;

    use crate::{
        tc::{
            lift::{proxy_slots::ProxySlots, Lift},
            state::TypeCheckerState,
        },
        vm::value::{known::KnownWord, Provenance, RSV, RSVD},
    };

    #[test]
    fn computes_correct_hash_of_words() {
        // Create the data to be hashed
        let string_pointer = KnownWord::from(0x20);
        let string_length = KnownWord::from(0x21);
        let word_1 = KnownWord::from_le(
            U256::from_str_hex(
                "0x696f2e73796e7468657469782e636f72652d636f6e7472616374732e50726f78",
            )
            .unwrap(),
        );
        let word_2 = KnownWord::from_le(
            U256::from_str_hex(
                "0x7900000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
        );

        // Check that the result is right
        let expected_result = KnownWord::from_le(
            U256::from_str_hex(
                "0x5a648c35a2f5512218b4683cf10e03f5b7c9dc7346e1bf77d304ae97f60f592b",
            )
            .unwrap(),
        );
        assert_eq!(
            ProxySlots::sha3_known_words(&[string_pointer, string_length, word_1, word_2]),
            expected_result
        );
        assert_eq!(
            ProxySlots::sha3_known_words(&[word_1]),
            ProxySlots::sha3_known_words(&[word_1]),
        );
    }

    #[test]
    fn discovers_likely_uris() {
        let word_1 = KnownWord::from_le(
            U256::from_str_hex(
                "0x696f2e73796e7468657469782e636f72652d636f6e7472616374732e50726f78",
            )
            .unwrap(),
        );
        let word_2 = KnownWord::from_le(
            U256::from_str_hex(
                "0x7900000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
        );

        // Check that we get the result correct
        assert!(ProxySlots::is_likely_string(&[word_1, word_2],));
    }

    #[test]
    fn correctly_rejects_non_uri() {
        let word_1 = KnownWord::from_le(
            U256::from_str_hex(
                "0x1f6f2e73796e7468657469782e636f72652d636f6e7472616374732e50726f78",
            )
            .unwrap(),
        );

        // Check that we get the result correct
        assert!(!ProxySlots::is_likely_string(&[word_1],));
    }

    #[test]
    fn correctly_asserts_string_length() {
        let word_1 = KnownWord::from_le(
            U256::from_str_hex(
                "0x696f2e73796e7468657469782e636f72652d636f6e7472616374732e50726f78",
            )
            .unwrap(),
        );
        let word_2 = KnownWord::from_le(
            U256::from_str_hex(
                "0x7900000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
        );

        // Check that the result is correct
        assert!(ProxySlots::has_correct_number_of_bytes(
            &[word_1, word_2],
            KnownWord::from(0x21)
        ));
    }

    #[test]
    fn correctly_detects_length_mismatches() {
        let word_1 = KnownWord::from_le(
            U256::from_str_hex(
                "0x696f2e73796e7468657469782e636f72652d636f6e7472616374732e50726f78",
            )
            .unwrap(),
        );
        let word_2 = KnownWord::from_le(
            U256::from_str_hex(
                "0x7979000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
        );

        // Check that the result is correct
        assert!(!ProxySlots::has_correct_number_of_bytes(
            &[word_1, word_2],
            KnownWord::from(0x21)
        ));
    }

    #[test]
    fn correctly_finds_a_direct_constant_slot() -> anyhow::Result<()> {
        // Create some data to run on
        let word = KnownWord::from_le(
            U256::from_str_hex(
                "0x696f2e73796e7468657469782e636f72652d636f6e7472616374732e50726f78",
            )
            .unwrap(),
        );
        let input_word = RSV::new_known_value(0, word, Provenance::Synthetic, None);
        let input_value = RSV::new_value(1, Provenance::Synthetic);
        let input_key = RSV::new_synthetic(2, RSVD::Sha3 { data: input_word });
        let s_load = RSV::new_synthetic(
            3,
            RSVD::SLoad {
                key:   input_key.clone(),
                value: input_value.clone(),
            },
        );

        // Run the pass
        let state = TypeCheckerState::empty();
        let result = ProxySlots.run(s_load, &state)?;

        // Inspect the result
        match result.data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(value, &input_value);

                match key.data() {
                    RSVD::KnownData { value } => {
                        assert_eq!(value, &ProxySlots::sha3_known_words(&[word]));
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn correctly_finds_single_word_under_concat() -> anyhow::Result<()> {
        // Create some data to run on
        let word = KnownWord::from_le(
            U256::from_str_hex(
                "0x696f2e73796e7468657469782e636f72652d636f6e7472616374732e50726f78",
            )
            .unwrap(),
        );
        let input_word = RSV::new_known_value(0, word, Provenance::Synthetic, None);
        let input_value = RSV::new_value(1, Provenance::Synthetic);
        let concat = RSV::new_synthetic(
            2,
            RSVD::Concat {
                values: vec![input_word],
            },
        );
        let input_key = RSV::new_synthetic(2, RSVD::Sha3 { data: concat });
        let s_load = RSV::new_synthetic(
            3,
            RSVD::SLoad {
                key:   input_key.clone(),
                value: input_value.clone(),
            },
        );

        // Run the pass
        let state = TypeCheckerState::empty();
        let result = ProxySlots.run(s_load, &state)?;

        // Inspect the result
        match result.data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(value, &input_value);

                match key.data() {
                    RSVD::KnownData { value } => {
                        assert_eq!(value, &ProxySlots::sha3_known_words(&[word]));
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn correctly_finds_packed_multi_word_under_concat() -> anyhow::Result<()> {
        // Create the data to test on
        let word_1 = KnownWord::from_le(
            U256::from_str_hex(
                "0x696f2e73796e7468657469782e636f72652d636f6e7472616374732e50726f78",
            )
            .unwrap(),
        );
        let word_2 = KnownWord::from_le(
            U256::from_str_hex(
                "0x7900000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
        );
        let words = vec![word_1, word_2]
            .into_iter()
            .map(|w| RSV::new_known_value(0, w, Provenance::Synthetic, None))
            .collect_vec();
        let concat = RSV::new_synthetic(1, RSVD::Concat { values: words });
        let sha3 = RSV::new_synthetic(2, RSVD::Sha3 { data: concat });
        let input_value = RSV::new_value(3, Provenance::Synthetic);
        let s_load = RSV::new_synthetic(
            4,
            RSVD::SLoad {
                key:   sha3,
                value: input_value.clone(),
            },
        );

        // Run the lifting
        let state = TypeCheckerState::empty();
        let result = ProxySlots.run(s_load, &state)?;

        // Check that the result is sane
        match result.data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(value, &input_value);

                match key.data() {
                    RSVD::KnownData { value } => {
                        assert_eq!(value, &ProxySlots::sha3_known_words(&[word_1, word_2]));
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn ignores_common_mapping_patterns() -> anyhow::Result<()> {
        // Create the data to test on
        let word_1 = KnownWord::from_le(
            U256::from_str_hex("0x696f2e73796e7468657469782e636f72652d636f6e7472616374732e50")
                .unwrap(),
        );
        let word_2 = KnownWord::from_le(
            U256::from_str_hex(
                "0x7900000000007380000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
        );
        let words = vec![word_1, word_2]
            .into_iter()
            .map(|w| RSV::new_known_value(0, w, Provenance::Synthetic, None))
            .collect_vec();
        let concat = RSV::new_synthetic(1, RSVD::Concat { values: words });
        let sha3 = RSV::new_synthetic(2, RSVD::Sha3 { data: concat });
        let input_value = RSV::new_value(3, Provenance::Synthetic);
        let s_load = RSV::new_synthetic(
            4,
            RSVD::SLoad {
                key:   sha3.clone(),
                value: input_value.clone(),
            },
        );

        // Run the lifting
        let state = TypeCheckerState::empty();
        let result = ProxySlots.run(s_load, &state)?;

        // Check that the result is sane
        match result.data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(key, &sha3);
                assert_eq!(value, &input_value);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn correctly_finds_abi_encoded_with_length() -> anyhow::Result<()> {
        // Create the data to test on
        let string_pointer = KnownWord::from(0x20);
        let string_length = KnownWord::from(0x21);
        let word_1 = KnownWord::from_le(
            U256::from_str_hex(
                "0x696f2e73796e7468657469782e636f72652d636f6e7472616374732e50726f78",
            )
            .unwrap(),
        );
        let word_2 = KnownWord::from_le(
            U256::from_str_hex(
                "0x7900000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
        );
        let words = vec![string_pointer, string_length, word_1, word_2]
            .into_iter()
            .map(|w| RSV::new_known_value(0, w, Provenance::Synthetic, None))
            .collect_vec();
        let concat = RSV::new_synthetic(1, RSVD::Concat { values: words });
        let sha3 = RSV::new_synthetic(2, RSVD::Sha3 { data: concat });
        let input_value = RSV::new_value(3, Provenance::Synthetic);
        let s_load = RSV::new_synthetic(
            4,
            RSVD::SLoad {
                key:   sha3,
                value: input_value.clone(),
            },
        );

        // Run the lifting
        let expected_result = KnownWord::from_le(
            U256::from_str_hex(
                "0x5a648c35a2f5512218b4683cf10e03f5b7c9dc7346e1bf77d304ae97f60f592b",
            )
            .unwrap(),
        );
        let state = TypeCheckerState::empty();
        let result = ProxySlots.run(s_load, &state)?;

        // Check that the result is sane
        match result.data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(value, &input_value);

                match key.data() {
                    RSVD::KnownData { value } => {
                        assert_eq!(value, &expected_result);
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn errors_if_abi_encoded_string_has_wrong_length() -> anyhow::Result<()> {
        // Create the data to test on
        let string_pointer = KnownWord::from(0x20);
        let string_length = KnownWord::from(0x22);
        let word_1 = KnownWord::from_le(
            U256::from_str_hex(
                "0x696f2e73796e7468657469782e636f72652d636f6e7472616374732e50726f78",
            )
            .unwrap(),
        );
        let word_2 = KnownWord::from_le(
            U256::from_str_hex(
                "0x7900000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
        );
        let words = vec![string_pointer, string_length, word_1, word_2]
            .into_iter()
            .map(|w| RSV::new_known_value(0, w, Provenance::Synthetic, None))
            .collect_vec();
        let concat = RSV::new_synthetic(1, RSVD::Concat { values: words });
        let sha3 = RSV::new_synthetic(2, RSVD::Sha3 { data: concat });
        let input_value = RSV::new_value(3, Provenance::Synthetic);
        let s_load = RSV::new_synthetic(
            4,
            RSVD::SLoad {
                key:   sha3.clone(),
                value: input_value.clone(),
            },
        );

        // Run the lifting
        let state = TypeCheckerState::empty();
        let result = ProxySlots.run(s_load, &state)?;

        // Check that the result is sane
        match result.data() {
            RSVD::SLoad { key, value } => {
                assert_eq!(key, &sha3);
                assert_eq!(value, &input_value);
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }
}
