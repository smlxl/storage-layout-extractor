//! This module contains the definitions for the `U256wrapper` type
//!
//! It used for making it possible to serialize `U256` to JSON
use ethnum::U256;
use serde::{Serialize, Serializer};

/// The `U256Wrapper` is responsible for serializing the U256 type
#[derive(Clone, Copy, Default, Eq, Hash, PartialEq, Debug)]
#[repr(transparent)]
pub struct U256Wrapper(pub U256);

impl Serialize for U256Wrapper {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&self.0.to_string())
    }
}

#[cfg(test)]
mod tests {
    use ethnum::U256;
    use serde_json::json;

    use super::U256Wrapper;

    #[test]
    fn can_be_serialized() {
        let value = U256Wrapper(U256::from(0x42_u128));
        let expected = "66";
        assert!(
            json!(value).as_str().unwrap().eq(expected),
            "Serialization failed"
        );
    }
}
