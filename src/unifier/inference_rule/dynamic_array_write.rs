//! This module contains the definition of an inference rule for typing dynamic
//! array writes.

use crate::{
    error::unification::Result,
    unifier::{expression::TE, inference_rule::InferenceRule, state::TypingState},
    vm::value::{BoxedVal, SVD},
};

/// This rule creates the equations `d = dynamic_array<b>`, `f = unsigned`, `b =
/// g` for expressions of the following form.
///
/// ```code
/// s_store(storage_slot(dynamic_array<storage_slot(base_slot)>[index]), value)
///    a          b            c             d          e         f        g
/// ```
///
/// where
/// - The second row are the type variable names for the corresponding
///   expression above. These type variables extend over the whole enclosing
///   expression.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct DynamicArrayWriteRule;

impl InferenceRule for DynamicArrayWriteRule {
    #[allow(clippy::many_single_char_names)] // They correspond to the above spec
    fn infer(&self, value: &BoxedVal, state: &mut TypingState) -> Result<()> {
        let SVD::StorageWrite { key: b, value: g } = &value.data else { return Ok(()) };
        let SVD::StorageSlot { key: c } = &b.data else { return Ok(()) };
        let SVD::DynamicArrayAccess { slot: d, index: f } = &c.data else { return Ok(()) };
        let SVD::StorageSlot { .. } = &d.data else { return Ok(()) };

        // `b = g`
        let b_tv = state.var_unchecked(b);
        let g_tv = state.var_unchecked(g);
        state.infer(b_tv, TE::eq(g_tv));

        // `f = unsigned`
        let f_tv = state.var_unchecked(f);
        state.infer(f_tv, TE::unsigned_word(None));

        // `d = dynamic_array<b>`
        let d_tv = state.var_unchecked(d);
        state.infer(d_tv, TE::dyn_array(b_tv));

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        unifier::{
            expression::TE,
            inference_rule::{dynamic_array_write::DynamicArrayWriteRule, InferenceRule},
            state::TypingState,
        },
        vm::value::{Provenance, SV, SVD},
    };

    #[test]
    fn creates_correct_inference_equations() -> anyhow::Result<()> {
        // Create a value of the relevant structure
        let value = SV::new_value(0, Provenance::Synthetic);
        let index = SV::new_value(1, Provenance::Synthetic);
        let base_slot = SV::new_value(2, Provenance::Synthetic);
        let slot_of_base_slot = SV::new(
            3,
            SVD::StorageSlot {
                key: base_slot.clone(),
            },
            Provenance::Synthetic,
        );
        let dyn_array = SV::new(
            4,
            SVD::DynamicArrayAccess {
                slot:  slot_of_base_slot.clone(),
                index: index.clone(),
            },
            Provenance::Synthetic,
        );
        let slot_of_dyn_array = SV::new(
            5,
            SVD::StorageSlot {
                key: dyn_array.clone(),
            },
            Provenance::Synthetic,
        );
        let store = SV::new(
            6,
            SVD::StorageWrite {
                key:   slot_of_dyn_array.clone(),
                value: value.clone(),
            },
            Provenance::Synthetic,
        );

        // Set up the unifier state
        let mut state = TypingState::empty();
        let g_tv = state.register(value);
        let f_tv = state.register(index);
        let e_tv = state.register(base_slot);
        let d_tv = state.register(slot_of_base_slot);
        let c_tv = state.register(dyn_array);
        let b_tv = state.register(slot_of_dyn_array);
        let a_tv = state.register(store.clone());

        // Run the inference rule
        DynamicArrayWriteRule.infer(&store, &mut state)?;

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
