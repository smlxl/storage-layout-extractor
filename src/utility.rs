//! Utility functions useful throughout the codebase.

use uuid::Uuid;

/// Formats a UUID as the first 16 bytes in hex, rather than the full thing.
/// This allows for more-compact printing.
#[must_use]
pub fn clip_uuid(uuid: &Uuid) -> String {
    let string = format!("{uuid}");
    string[0..8].to_string()
}
