//! This module contains the definition of an inference rule for typing dynamic
//! array writes.

use crate::{
    error::unification::Result,
    tc::{expression::TE, rule::InferenceRule, state::TypeCheckerState},
    vm::value::{TCBoxedVal, TCSVD},
};

/// This rule creates the following equations in the typing state for
/// expressions of the following form.
///
/// ```code
/// s_store(storage_slot(dynamic_array<storage_slot(base_slot)>[index]), value)
///    a          b            c             d          e         f        g
/// ```
///
/// equating
/// - `d = dynamic_array<b>`
/// - `f = word(width = unknown, usage = UnsignedWord)`
/// - `b = g`
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct DynamicArrayWriteRule;

impl InferenceRule for DynamicArrayWriteRule {
    #[allow(clippy::many_single_char_names)] // They correspond to the above spec
    fn infer(&self, value: &TCBoxedVal, state: &mut TypeCheckerState) -> Result<()> {
        let TCSVD::StorageWrite { key: b, value: g } = value.data() else {
            return Ok(());
        };
        let TCSVD::StorageSlot { key: c } = b.data() else {
            return Ok(());
        };
        let TCSVD::DynamicArrayIndex { slot: d, index: f } = c.data() else {
            return Ok(());
        };
        let TCSVD::StorageSlot { .. } = d.data() else {
            return Ok(());
        };

        // `b = g`
        let b_tv = state.var_unchecked(b);
        let g_tv = state.var_unchecked(g);
        state.infer(b_tv, TE::eq(g_tv));

        // `f = unsigned`
        state.infer_for(f, TE::unsigned_word(None));

        // `d = dynamic_array<b>`
        state.infer_for(d, TE::dyn_array(b_tv));

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        tc::{
            expression::TE,
            rule::{dynamic_array_write::DynamicArrayWriteRule, InferenceRule},
            state::TypeCheckerState,
        },
        vm::value::{Provenance, RSV, RSVD, TCSVD},
    };

    #[test]
    fn creates_correct_inference_equations() -> anyhow::Result<()> {
        // Create a value of the relevant structure
        let value = RSV::new_value(0, Provenance::Synthetic);
        let index = RSV::new_value(1, Provenance::Synthetic);
        let base_slot = RSV::new_value(2, Provenance::Synthetic);
        let slot_of_base_slot = RSV::new_synthetic(
            3,
            RSVD::StorageSlot {
                key: base_slot.clone(),
            },
        );
        let dyn_array = RSV::new_synthetic(
            4,
            RSVD::DynamicArrayIndex {
                slot:  slot_of_base_slot.clone(),
                index: index.clone(),
            },
        );
        let slot_of_dyn_array = RSV::new_synthetic(
            5,
            RSVD::StorageSlot {
                key: dyn_array.clone(),
            },
        );
        let store = RSV::new_synthetic(
            6,
            RSVD::StorageWrite {
                key:   slot_of_dyn_array.clone(),
                value: value.clone(),
            },
        );

        // Set up the unifier state
        let mut state = TypeCheckerState::empty();
        let a_tv = state.register(store);
        let tc_input = state.value_unchecked(a_tv).clone();
        let [b_tv, c_tv, d_tv, e_tv, f_tv, g_tv] = match tc_input.data() {
            TCSVD::StorageWrite { key, value } => {
                let g_tv = value.type_var();
                let b_tv = key.type_var();
                match key.data() {
                    TCSVD::StorageSlot { key } => {
                        let c_tv = key.type_var();
                        match key.data() {
                            TCSVD::DynamicArrayIndex { slot, index } => {
                                let d_tv = slot.type_var();
                                let f_tv = index.type_var();
                                match slot.data() {
                                    TCSVD::StorageSlot { key } => {
                                        let e_tv = key.type_var();
                                        [b_tv, c_tv, d_tv, e_tv, f_tv, g_tv]
                                    }
                                    _ => panic!("Incorrect payload"),
                                }
                            }
                            _ => panic!("Incorrect payload"),
                        }
                    }
                    _ => panic!("Incorrect payload"),
                }
            }
            _ => panic!("Incorrect payload"),
        };
        DynamicArrayWriteRule.infer(&tc_input, &mut state)?;

        // Check that we end up with expected results in the state
        assert_eq!(state.inferences(g_tv).len(), 1);
        assert!(state.inferences(g_tv).contains(&TE::eq(b_tv)));

        assert_eq!(state.inferences(f_tv).len(), 1);
        assert!(state.inferences(f_tv).contains(&TE::unsigned_word(None)));

        assert!(state.inferences(e_tv).is_empty());

        assert_eq!(state.inferences(d_tv).len(), 1);
        assert!(state.inferences(d_tv).contains(&TE::dyn_array(b_tv)));

        assert!(state.inferences(c_tv).is_empty());

        assert_eq!(state.inferences(b_tv).len(), 1);
        assert!(state.inferences(b_tv).contains(&TE::eq(g_tv)));

        assert!(state.inferences(a_tv).is_empty());

        Ok(())
    }
}
