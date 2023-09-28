//! This module contains an inference rule that equates every `SLoad` with the
//! type of its element and its key.

use crate::{
    error::unification::Result,
    tc::{expression::TE, rule::InferenceRule, state::TypeCheckerState},
    vm::value::{TCBoxedVal, TCSVD},
};

/// This rule creates the following equations in the typing state for
/// expressions of the following form.
///
/// ```text
/// s_load(key, value)
///    a    b     c
/// ```
///
/// equating
///
/// - `a = b`
/// - `a = c`
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct SLoadIsInnerTypesRule;

impl InferenceRule for SLoadIsInnerTypesRule {
    fn infer(&self, value: &TCBoxedVal, state: &mut TypeCheckerState) -> Result<()> {
        let TCSVD::SLoad {
            value: inner_value,
            key,
        } = value.data()
        else {
            return Ok(());
        };

        let inner_value_tv = state.var_unchecked(inner_value);
        let slot_tv = state.var_unchecked(key);

        state.infer_for(value, TE::eq(inner_value_tv));
        state.infer_for(value, TE::eq(slot_tv));

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{
        tc::{
            expression::TE,
            rule::{s_load_is_inner_types::SLoadIsInnerTypesRule, InferenceRule},
            state::TypeCheckerState,
        },
        vm::value::{Provenance, RSV, RSVD, TCSVD},
    };

    #[test]
    fn creates_correct_equations_in_state() -> anyhow::Result<()> {
        // Create the expressions to be typed
        let key = RSV::new_value(0, Provenance::Synthetic);
        let value = RSV::new_value(1, Provenance::Synthetic);
        let s_load = RSV::new_synthetic(
            2,
            RSVD::SLoad {
                key:   key.clone(),
                value: value.clone(),
            },
        );

        // Register these in the state
        let mut state = TypeCheckerState::empty();
        let s_load_ty = state.register(s_load);
        let tc_input = state.value_unchecked(s_load_ty).clone();
        let [key_ty, value_ty] = match tc_input.data() {
            TCSVD::SLoad { key, value } => [key.type_var(), value.type_var()],
            _ => panic!("Incorrect payload"),
        };
        SLoadIsInnerTypesRule.infer(&tc_input, &mut state)?;

        assert_eq!(state.inferences(key_ty).len(), 1);
        assert!(state.inferences(key_ty).contains(&TE::eq(s_load_ty)));

        assert_eq!(state.inferences(value_ty).len(), 1);
        assert!(state.inferences(value_ty).contains(&TE::eq(s_load_ty)));

        assert_eq!(state.inferences(s_load_ty).len(), 2);
        assert!(state.inferences(s_load_ty).contains(&TE::eq(value_ty)));
        assert!(state.inferences(s_load_ty).contains(&TE::eq(key_ty)));

        Ok(())
    }
}
