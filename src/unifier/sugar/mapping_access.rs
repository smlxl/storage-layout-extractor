//! This module provides a re-sugaring pass that recognises accesses to
//! individual storing slots as part of a mapping.

use crate::{
    unifier::{state::UnifierState, sugar::ReSugar},
    vm::value::{BoxedVal, SVD},
};

/// This pass detects and folds expressions that access mappings in storage.
///
/// These have a form as follows:
///
/// ```code
/// sha3(concat(key, slot_ix))
/// ```
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct MappingAccess;

impl MappingAccess {
    /// Constructs a new instance of the mapping access re-sugaring pass.
    pub fn new() -> Box<Self> {
        Box::new(Self)
    }
}

impl ReSugar for MappingAccess {
    fn run(
        &mut self,
        value: BoxedVal,
        _state: &mut UnifierState,
    ) -> crate::error::unification::Result<BoxedVal> {
        fn insert_mapping_accesses(data: &SVD) -> Option<SVD> {
            let SVD::Sha3 {data} = data else { return None };
            let SVD::Concat {values} = &data.data else { return None };
            let [key, slot] = &values[..] else { return None };

            Some(SVD::MappingAddress {
                key:  key.clone(),
                slot: slot.clone(),
            })
        }

        Ok(value.transform_data(insert_mapping_accesses))
    }
}

#[cfg(test)]
mod test {
    use crate::{
        unifier::{
            state::UnifierState,
            sugar::{mapping_access::MappingAccess, ReSugar},
        },
        vm::value::{known::KnownWord, Provenance, SymbolicValue, SVD},
    };

    #[test]
    fn resolves_mapping_accesses_at_top_level() -> anyhow::Result<()> {
        let input_key = SymbolicValue::new_value(0, Provenance::Synthetic);
        let input_slot =
            SymbolicValue::new_known_value(1, KnownWord::from(10), Provenance::Synthetic);
        let concat = SymbolicValue::new(
            2,
            SVD::Concat {
                values: vec![input_key.clone(), input_slot.clone()],
            },
            Provenance::Synthetic,
        );
        let hash = SymbolicValue::new(3, SVD::Sha3 { data: concat }, Provenance::Synthetic);

        let mut state = UnifierState::new();
        let result = MappingAccess.run(hash, &mut state)?;

        match result.data {
            SVD::MappingAddress { key, slot } => {
                assert_eq!(key, input_key);
                assert_eq!(slot, input_slot);
            }
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }

    #[test]
    fn resolves_mapping_accesses_while_nested() -> anyhow::Result<()> {
        let input_key = SymbolicValue::new_value(0, Provenance::Synthetic);
        let input_slot =
            SymbolicValue::new_known_value(1, KnownWord::from(10), Provenance::Synthetic);
        let concat = SymbolicValue::new(
            2,
            SVD::Concat {
                values: vec![input_key.clone(), input_slot.clone()],
            },
            Provenance::Synthetic,
        );
        let hash = SymbolicValue::new(3, SVD::Sha3 { data: concat }, Provenance::Synthetic);
        let not = SymbolicValue::new(4, SVD::Not { value: hash }, Provenance::Synthetic);

        let mut state = UnifierState::new();
        let result = MappingAccess.run(not, &mut state)?;

        match result.data {
            SVD::Not { value: bool } => match bool.data {
                SVD::MappingAddress { key, slot } => {
                    assert_eq!(key, input_key);
                    assert_eq!(slot, input_slot);
                }
                _ => panic!("Invalid payload"),
            },
            _ => panic!("Invalid payload"),
        }

        Ok(())
    }
}
