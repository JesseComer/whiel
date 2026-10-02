//! Proposer API version, including its public process communication contract.

pub const API_VERSION: &str = "3.2.0";

// Existing wire versions remain independent of the semantic API version.
pub(crate) const AGENT_HOUDINI_PROTOCOL_VERSION: u64 = 4;
pub(crate) const AGENT_FEEDBACK_SCHEMA_VERSION: u64 = 10;
pub(crate) const AGENT_PRESENTATION_SCHEMA_VERSION: u64 = 16;
