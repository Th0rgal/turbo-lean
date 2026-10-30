//! Content-addressed storage (CAS) and `.tlpack` bundle primitives.
//!
//! Exposes `TurboStore`, `ActionRecord`, `BlobEntry`, `StorageStatus`, and `.tlpack`
//! attestation/archive helpers as a cohesive single-crate module surface.

pub use crate::db::{now_unix, ActionRecord, BlobEntry, SingleflightOutcome, StorageStatus, TurboStore};
pub use crate::pack::{
    compute_pack_attestation_digest, decode_hex_fixed, encode_hex_bytes, PackManifest,
};
