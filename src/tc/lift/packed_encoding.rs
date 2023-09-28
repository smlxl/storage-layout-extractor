//! This module contains a pass that aims to discover and lift instances of
//! multiple types being packed into a single machine word. We call these
//! "packed encodings" throughout the codebase.

use itertools::Itertools;

use crate::{
    tc::{lift::Lift, state::TypeCheckerState},
    vm::value::{PackedSpan, RuntimeBoxedVal, RSV, RSVD},
};

/// This pass detects and lifts expressions that represent the packing of
/// multiple values into a single machine word.
///
/// These have a form as follows:
///
/// ```text
/// s_store(slot, seg_1 | seg_2 | ... | seg_n)
///
/// becomes
///
/// s_store(slot, packed(seg_1, seg_2, ..., seg_n))
/// ```
///
/// where:
///
/// - Each `seg_i` is one of either `shifted` or `sub_word`
/// - All of the `seg_i` elements completely cover the EVM word without
///   overlapping.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct PackedEncoding;

impl PackedEncoding {
    /// Creates a new instance of the packed encoding discovery and lifting
    /// pass.
    #[must_use]
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }
}

impl Lift for PackedEncoding {
    fn run(
        &mut self,
        value: RuntimeBoxedVal,
        _state: &TypeCheckerState,
    ) -> crate::error::unification::Result<RuntimeBoxedVal> {
        /// Pulls apart nodes representing bitwise ors all at the same semantic
        /// level, or returns [`None`] if none were found.
        ///
        /// The order of the returned values is arbitrary.
        #[allow(clippy::boxed_local)] // We pass all these things around boxed
        fn unpick_ors(data: RuntimeBoxedVal) -> Vec<RuntimeBoxedVal> {
            let RSVD::Or { left, right } = data.data() else { return vec![data] };
            let mut left_ors = unpick_ors(left.clone());
            let right_ors = unpick_ors(right.clone());
            left_ors.extend(right_ors);
            left_ors
        }

        fn lift_packed_encodings(data: &RSVD) -> Option<RSVD> {
            // At the top level it needs to be a storage write
            let RSVD::StorageWrite { key, value } = data else { return None };

            // We then pull it apart into top-level elements, and fail out if they are not
            // valid types for this
            let elements = unpick_ors(value.clone());
            let true = elements
                .iter()
                .map(|e| matches!(e.data(), RSVD::Shifted { .. } | RSVD::SubWord { .. }))
                .all(|r| r)
            else {
                return None;
            };

            // Next, we need to turn those elements into spans so that we can compute
            // coverage of the word (by sorting elements)
            let spans: Vec<PackedSpan<()>> = elements
                .into_iter()
                .map(|e| match &e.data() {
                    RSVD::SubWord { offset, size, .. } => PackedSpan::new(*offset, *size, e),
                    RSVD::Shifted { offset, value } => match &value.data() {
                        RSVD::SubWord { size, .. } => {
                            PackedSpan::new(*offset, *size, value.clone())
                        }
                        _ => panic!("Shift of non-sub-word"),
                    },
                    _ => unreachable!("Element was of impossible type"),
                })
                .sorted_by_key(|elem| elem.offset)
                .collect();

            // To be valid, spans must not overlap
            let mut spans_are_valid = true;
            let mut last_position = 0;
            for PackedSpan { offset, size, .. } in &spans {
                spans_are_valid = spans_are_valid && last_position <= *offset;
                last_position = offset + size;
            }

            // In order to prevent issues with inferring types for unused portions of a
            // slot, we drop the portions that are unused. We define being unused as a span
            // containing a sub-word that directly reads from the same storage slot that it
            // gets written to.
            let used_spans: Vec<_> = spans
                .into_iter()
                .filter(|span| match &span.value.data() {
                    RSVD::SubWord { value, .. } => !matches!(
                        value.data(),
                        RSVD::SLoad { key: inner_key, .. } if key == inner_key
                    ),
                    _ => true,
                })
                .collect();

            if spans_are_valid {
                let packed = RSV::new(
                    value.instruction_pointer(),
                    RSVD::Packed {
                        elements: used_spans,
                    },
                    value.provenance(),
                    None,
                );
                let store = RSVD::StorageWrite {
                    key:   key.clone(),
                    value: packed,
                };
                Some(store)
            } else {
                None
            }
        }

        Ok(value.transform_data(lift_packed_encodings))
    }
}

#[cfg(test)]
mod test {
    use crate::{
        tc::{
            lift::{packed_encoding::PackedEncoding, Lift},
            state::TypeCheckerState,
        },
        vm::value::{PackedSpan, Provenance, RSV, RSVD},
    };

    #[test]
    fn lifts_two_element_packed_encodings() -> anyhow::Result<()> {
        // Construct the data to work on
        let value = RSV::new_value(0, Provenance::Synthetic);
        let sub_word_1 = RSV::new_synthetic(
            1,
            RSVD::SubWord {
                value:  value.clone(),
                offset: 128,
                size:   128,
            },
        );
        let sub_word_2 = RSV::new_synthetic(
            2,
            RSVD::SubWord {
                value,
                offset: 0,
                size: 128,
            },
        );
        let or = RSV::new_synthetic(
            3,
            RSVD::Or {
                left:  sub_word_1.clone(),
                right: sub_word_2.clone(),
            },
        );
        let input_key = RSV::new_value(4, Provenance::Synthetic);
        let store = RSV::new_synthetic(
            5,
            RSVD::StorageWrite {
                key:   input_key.clone(),
                value: or,
            },
        );

        // Run the pass
        let state = TypeCheckerState::empty();
        let result = PackedEncoding.run(store, &state)?;

        // Check the structure of the data
        match result.data() {
            RSVD::StorageWrite { key, value } => {
                assert_eq!(key, &input_key);
                match value.data() {
                    RSVD::Packed { elements } => {
                        assert_eq!(elements.len(), 2);
                        assert!(elements.contains(&PackedSpan::new(128, 128, sub_word_1)));
                        assert!(elements.contains(&PackedSpan::new(0, 128, sub_word_2)));
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn lifts_more_complex_packed_encodings() -> anyhow::Result<()> {
        // Construct the data to work on
        let value = RSV::new_value(0, Provenance::Synthetic);
        let sub_word_1 = RSV::new_synthetic(
            1,
            RSVD::SubWord {
                value:  value.clone(),
                offset: 128,
                size:   128,
            },
        );
        let sub_word_2 = RSV::new_synthetic(
            2,
            RSVD::SubWord {
                value:  value.clone(),
                offset: 64,
                size:   64,
            },
        );
        let sub_word_3 = RSV::new_synthetic(
            3,
            RSVD::SubWord {
                value,
                offset: 0,
                size: 64,
            },
        );
        let inner_or = RSV::new_synthetic(
            4,
            RSVD::Or {
                left:  sub_word_1.clone(),
                right: sub_word_2.clone(),
            },
        );
        let outer_or = RSV::new_synthetic(
            5,
            RSVD::Or {
                left:  inner_or,
                right: sub_word_3.clone(),
            },
        );
        let input_key = RSV::new_value(6, Provenance::Synthetic);
        let store = RSV::new_synthetic(
            7,
            RSVD::StorageWrite {
                key:   input_key.clone(),
                value: outer_or,
            },
        );

        // Run the pass
        let state = TypeCheckerState::empty();
        let result = PackedEncoding.run(store, &state)?;

        // Check the structure of the data
        match result.data() {
            RSVD::StorageWrite { key, value } => {
                assert_eq!(key, &input_key);
                match value.data() {
                    RSVD::Packed { elements } => {
                        assert_eq!(elements.len(), 3);
                        assert!(elements.contains(&PackedSpan::new(128, 128, sub_word_1)));
                        assert!(elements.contains(&PackedSpan::new(64, 64, sub_word_2)));
                        assert!(elements.contains(&PackedSpan::new(0, 64, sub_word_3)));
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn lifts_packed_encodings_with_sized_shifted_elements() -> anyhow::Result<()> {
        // Construct the test data
        let value = RSV::new_value(0, Provenance::Synthetic);
        let sub_word_1 = RSV::new_synthetic(
            1,
            RSVD::SubWord {
                value:  value.clone(),
                offset: 128,
                size:   128,
            },
        );
        let sub_word_2 = RSV::new_synthetic(
            2,
            RSVD::SubWord {
                value:  value.clone(),
                offset: 0,
                size:   64,
            },
        );
        let sub_word_3 = RSV::new_synthetic(
            3,
            RSVD::SubWord {
                value,
                offset: 0,
                size: 64,
            },
        );
        let shifted = RSV::new_synthetic(
            4,
            RSVD::Shifted {
                offset: 64,
                value:  sub_word_3.clone(),
            },
        );
        let inner_or = RSV::new_synthetic(
            4,
            RSVD::Or {
                left:  sub_word_1.clone(),
                right: sub_word_2.clone(),
            },
        );
        let outer_or = RSV::new_synthetic(
            5,
            RSVD::Or {
                left:  inner_or,
                right: shifted.clone(),
            },
        );
        let input_key = RSV::new_value(6, Provenance::Synthetic);
        let store = RSV::new_synthetic(
            7,
            RSVD::StorageWrite {
                key:   input_key.clone(),
                value: outer_or,
            },
        );

        // Run the pass
        let state = TypeCheckerState::empty();
        let result = PackedEncoding.run(store, &state)?;

        // Check the structure of the data
        match result.data() {
            RSVD::StorageWrite { key, value } => {
                assert_eq!(key, &input_key);
                match value.data() {
                    RSVD::Packed { elements } => {
                        assert_eq!(elements.len(), 3);
                        assert!(elements.contains(&PackedSpan::new(128, 128, sub_word_1)));
                        assert!(elements.contains(&PackedSpan::new(0, 64, sub_word_2)));
                        assert!(elements.contains(&PackedSpan::new(64, 64, sub_word_3)));
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        }

        Ok(())
    }

    #[test]
    fn drops_direct_reads_from_same_slot_in_packed_encodings() -> anyhow::Result<()> {
        // Create the expressions to be lifted
        let input_key = RSV::new_value(4, Provenance::Synthetic);
        let value = RSV::new_value(0, Provenance::Synthetic);
        let uninit_load = RSV::new_synthetic(
            0,
            RSVD::UnwrittenStorageValue {
                key: input_key.clone(),
            },
        );
        let s_load = RSV::new_synthetic(
            7,
            RSVD::SLoad {
                key:   input_key.clone(),
                value: uninit_load,
            },
        );
        let sub_word_1 = RSV::new_synthetic(
            1,
            RSVD::SubWord {
                value,
                offset: 128,
                size: 128,
            },
        );
        let sub_word_2 = RSV::new_synthetic(
            2,
            RSVD::SubWord {
                value:  s_load,
                offset: 0,
                size:   128,
            },
        );
        let or = RSV::new_synthetic(
            3,
            RSVD::Or {
                left:  sub_word_1.clone(),
                right: sub_word_2,
            },
        );
        let store = RSV::new_synthetic(
            5,
            RSVD::StorageWrite {
                key:   input_key.clone(),
                value: or,
            },
        );

        // Run the pass
        let state = TypeCheckerState::empty();
        let result = PackedEncoding.run(store, &state)?;

        // Check the structure of the data
        match result.data() {
            RSVD::StorageWrite { key, value } => {
                assert_eq!(key, &input_key);
                match value.data() {
                    RSVD::Packed { elements } => {
                        assert_eq!(elements.len(), 1);
                        assert!(elements.contains(&PackedSpan::new(128, 128, sub_word_1)));
                    }
                    _ => panic!("Invalid payload"),
                }
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }
}
