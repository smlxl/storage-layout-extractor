//! This module contains the implementation of inference rules to do with
//! external message calls.

use crate::{
    error::unification::Result,
    inference::{expression::TE, rule::InferenceRule, state::InferenceState},
    vm::value::{TCBoxedVal, TCSVD},
};

/// This rule creates the following equations for external calls.
///
/// For expressions of the form:
///
/// ```text
/// call_with_value(gas, address, value, argument_data, ret_offset, ret_size)
///        a         b      c       d          e             f          g
/// ```
///
/// - `a = address`
/// - `b = unsigned`
/// - `c = address`
/// - `d = unsigned`
/// - `f = unsigned`
/// - `g = unsigned`
///
/// For expressions of the form:
///
/// ```text
/// call_without_value(gas, address, argument_data, ret_offset, ret_size)
///         a           b      c           d             e          f
/// ```
///
/// - `a = address`
/// - `b = unsigned`
/// - `c = address`
/// - `e = unsigned`
/// - `f = unsigned`
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct ExternalCallRule;

impl InferenceRule for ExternalCallRule {
    #[allow(clippy::many_single_char_names)] // They correspond to the above spec
    fn infer(&self, value: &TCBoxedVal, state: &mut InferenceState) -> Result<()> {
        match &value.data {
            TCSVD::CallWithValue {
                gas: b,
                address: c,
                value: d,
                ret_offset: f,
                ret_size: g,
                ..
            } => {
                // a = address
                state.infer_for(value, TE::address());

                // b = unsigned
                state.infer_for(b, TE::unsigned_word(None));

                // c = address
                state.infer_for(c, TE::address());

                // d = unsigned
                state.infer_for(d, TE::unsigned_word(None));

                // f = unsigned
                state.infer_for(f, TE::unsigned_word(None));

                // g = unsigned
                state.infer_for(g, TE::unsigned_word(None));

                Ok(())
            }
            TCSVD::CallWithoutValue {
                gas: b,
                address: c,
                ret_offset: e,
                ret_size: f,
                ..
            } => {
                // a = address
                state.infer_for(value, TE::address());

                // b = unsigned
                state.infer_for(b, TE::unsigned_word(None));

                // c = address
                state.infer_for(c, TE::address());

                // e = unsigned
                state.infer_for(e, TE::unsigned_word(None));

                // f = unsigned
                state.infer_for(f, TE::unsigned_word(None));

                Ok(())
            }
            _ => Ok(()),
        }
    }
}

// #[cfg(test)]
// mod test {
//     use crate::{
//         inference::{
//             expression::TE,
//             rule::{external_calls::ExternalCallRule, InferenceRule},
//             state::InferenceState,
//         },
//         vm::value::{Provenance, RSV, RSVD},
//     };
//
//     #[test]
//     #[allow(clippy::many_single_char_names)] // They correspond to the above
// spec     fn creates_correct_equations_for_call_with_value() ->
// anyhow::Result<()> {         // Create some values
//         let ret_size = RSV::new_value(0, Provenance::Synthetic);
//         let ret_offset = RSV::new_value(1, Provenance::Synthetic);
//         let arg_data = RSV::new_value(2, Provenance::Synthetic);
//         let value = RSV::new_value(3, Provenance::Synthetic);
//         let address = RSV::new_value(4, Provenance::Synthetic);
//         let gas = RSV::new_value(5, Provenance::Synthetic);
//         let call = RSV::new(
//             6,
//             RSVD::CallWithValue {
//                 gas:           gas.clone(),
//                 address:       address.clone(),
//                 value:         value.clone(),
//                 argument_data: arg_data.clone(),
//                 ret_offset:    ret_offset.clone(),
//                 ret_size:      ret_size.clone(),
//             },
//             Provenance::Synthetic,
//         );
//
//         // Create the state and register the values
//         let mut state = InferenceState::empty();
//         let [g, f, _, d, c, b, a] = state.register_many([
//             ret_size,
//             ret_offset,
//             arg_data,
//             value,
//             address,
//             gas,
//             call.clone(),
//         ]);
//
//         // Run the rule
//         let tc_input = state.value_unchecked(a).clone();
//         ExternalCallRule.infer(&tc_input, &mut state)?;
//
//         // Check that the equations are correct
//         assert!(state.inferences(g).contains(&TE::unsigned_word(None)));
//         assert!(state.inferences(f).contains(&TE::unsigned_word(None)));
//         assert!(state.inferences(d).contains(&TE::unsigned_word(None)));
//         assert!(state.inferences(c).contains(&TE::address()));
//         assert!(state.inferences(b).contains(&TE::unsigned_word(None)));
//         assert!(state.inferences(a).contains(&TE::address()));
//
//         Ok(())
//     }
//
//     #[test]
//     #[allow(clippy::many_single_char_names)] // They correspond to the above
// spec     fn creates_correct_equations_for_call_without_value() ->
// anyhow::Result<()> {         // Create some values
//         let ret_size = RSV::new_value(0, Provenance::Synthetic);
//         let ret_offset = RSV::new_value(1, Provenance::Synthetic);
//         let arg_data = RSV::new_value(2, Provenance::Synthetic);
//         let address = RSV::new_value(4, Provenance::Synthetic);
//         let gas = RSV::new_value(5, Provenance::Synthetic);
//         let call = RSV::new(
//             6,
//             RSVD::CallWithoutValue {
//                 gas:           gas.clone(),
//                 address:       address.clone(),
//                 argument_data: arg_data.clone(),
//                 ret_offset:    ret_offset.clone(),
//                 ret_size:      ret_size.clone(),
//             },
//             Provenance::Synthetic,
//         );
//
//         // Create the state and register the values
//         let mut state = InferenceState::empty();
//         let [f, e, _, c, b, a] =
//             state.register_many([ret_size, ret_offset, arg_data, address,
// gas, call.clone()]);
//
//         // Run the rule
//         let tc_input = state.value_unchecked(a).clone();
//         ExternalCallRule.infer(&tc_input, &mut state)?;
//
//         // Check that the equations are correct
//         assert!(state.inferences(f).contains(&TE::unsigned_word(None)));
//         assert!(state.inferences(e).contains(&TE::unsigned_word(None)));
//         assert!(state.inferences(c).contains(&TE::address()));
//         assert!(state.inferences(b).contains(&TE::unsigned_word(None)));
//         assert!(state.inferences(a).contains(&TE::address()));
//
//         Ok(())
//     }
// }
