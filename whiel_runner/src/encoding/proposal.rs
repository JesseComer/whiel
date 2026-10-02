//! Append-only reference-proposal authority and worker replay plans.

use std::sync::Arc;

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::entailment::assembly::Sha256;

/// Semantic version of the typed reference-proposal payload.
pub const REFERENCE_PROPOSAL_VERSION: u64 = 3;

/// Version of the shared paginated proposal wire contract.
pub const PROPOSAL_PAGE_PROTOCOL_VERSION: u64 = 4;

// ------------------------------------------------------------
// Proposal Realizations
// ------------------------------------------------------------

/// Compiled implementation behind the symbolic proposal boundary.
///
/// The realization is fixed for one encoding context.  Its stable identity is
/// carried on every live and replayed proposal page, while Houdini and the INV
/// algorithm continue to observe only typed proposal batches.  Realizations
/// must be benchmark-blind: they may inspect the formal synthesis task and the
/// global enumeration policy, but not benchmark names, paths, suite membership,
/// expected answers, or per-example tuning tables.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ProposalRealization {
    ReferenceV3,
    FastV1,
    #[default]
    SeededV1,
    CappedV1,
}

impl ProposalRealization {
    pub const fn realization_id(self) -> &'static str {
        match self {
            Self::ReferenceV3 => "lean-reference-v3",
            Self::FastV1 => "lean-fast-v1",
            Self::SeededV1 => "lean-fast-v2-seeded",
            Self::CappedV1 => "lean-fast-v3-capped",
        }
    }

    pub const fn realization_version(self) -> u64 {
        match self {
            Self::ReferenceV3 => 3,
            Self::FastV1 => 1,
            Self::SeededV1 => 2,
            Self::CappedV1 => 3,
        }
    }

    pub const fn cli_name(self) -> &'static str {
        match self {
            Self::ReferenceV3 => "reference",
            Self::FastV1 => "fast",
            Self::SeededV1 => "seeded",
            Self::CappedV1 => "capped",
        }
    }

    pub fn parse_cli(value: &str) -> Option<Self> {
        match value {
            "reference" => Some(Self::ReferenceV3),
            "fast" => Some(Self::FastV1),
            "seeded" => Some(Self::SeededV1),
            "capped" => Some(Self::CappedV1),
            _ => None,
        }
    }

    pub(crate) fn from_wire(realization_id: &str, realization_version: u64) -> Option<Self> {
        [
            Self::ReferenceV3,
            Self::FastV1,
            Self::SeededV1,
            Self::CappedV1,
        ]
        .into_iter()
        .find(|realization| {
            realization.realization_id() == realization_id
                && realization.realization_version() == realization_version
        })
    }
}

// ------------------------------------------------------------
// Proposal Revisions
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ProposalRevision(u64);

impl ProposalRevision {
    pub const INITIAL: Self = Self(0);

    pub fn get(self) -> u64 {
        self.0
    }

    pub(crate) fn successor(self) -> Option<Self> {
        self.0.checked_add(1).map(Self)
    }

    #[cfg(test)]
    pub(crate) const fn from_raw(value: u64) -> Self {
        Self(value)
    }
}

// ------------------------------------------------------------
// Replay Authority
// ------------------------------------------------------------

#[derive(Clone, Debug)]
pub(crate) struct ProposalDelta {
    pub(crate) realization: ProposalRealization,
    pub(crate) base_revision: ProposalRevision,
    pub(crate) revision: ProposalRevision,
    pub(crate) stage: u64,
    pub(crate) cursor: u64,
    pub(crate) next_cursor: u64,
    pub(crate) max_response_bytes: u64,
    pub(crate) complete: bool,
    pub(crate) fragment: Arc<str>,
    pub(crate) expected_digest: Arc<str>,
}

#[derive(Clone, Debug)]
pub(crate) struct ProposalSync {
    pub(crate) realization: ProposalRealization,
    pub(crate) target_revision: ProposalRevision,
    pub(crate) target_page_count: usize,
    pub(crate) authority_page_count: usize,
    pub(crate) deltas: Arc<Vec<Arc<ProposalDelta>>>,
}

#[derive(Clone, Debug)]
pub(crate) struct ReferenceProposalAuthority {
    realization: ProposalRealization,
    revision: ProposalRevision,
    deltas: Arc<Vec<Arc<ProposalDelta>>>,
    completed_page_counts: Arc<Vec<usize>>,
}

impl ReferenceProposalAuthority {
    pub(crate) fn new(realization: ProposalRealization) -> Self {
        Self {
            realization,
            revision: ProposalRevision::INITIAL,
            deltas: Arc::new(Vec::new()),
            completed_page_counts: Arc::new(vec![0]),
        }
    }

    pub(crate) fn revision(&self) -> ProposalRevision {
        self.revision
    }

    pub(crate) fn realization(&self) -> ProposalRealization {
        self.realization
    }

    pub(crate) fn sync(&self) -> ProposalSync {
        ProposalSync {
            realization: self.realization,
            target_revision: self.revision,
            target_page_count: self.deltas.len(),
            authority_page_count: self.deltas.len(),
            deltas: Arc::clone(&self.deltas),
        }
    }

    pub(crate) fn sync_through(&self, revision: ProposalRevision) -> Option<ProposalSync> {
        if revision > self.revision {
            return None;
        }
        let revision_index = usize::try_from(revision.get()).ok()?;
        let page_count = *self.completed_page_counts.get(revision_index)?;
        let deltas = Arc::new(self.deltas.iter().take(page_count).cloned().collect());
        Some(ProposalSync {
            realization: self.realization,
            target_revision: revision,
            target_page_count: page_count,
            authority_page_count: self.deltas.len(),
            deltas,
        })
    }

    pub(crate) fn next_cursor(&self) -> u64 {
        let completed_page_count = self.completed_page_counts.last().copied().unwrap_or(0);
        self.deltas
            .get(completed_page_count..)
            .and_then(|partial| partial.last())
            .map_or(0, |delta| delta.next_cursor)
    }

    pub(crate) fn partial_fragment_text(&self) -> String {
        let completed_page_count = self.completed_page_counts.last().copied().unwrap_or(0);
        self.deltas[completed_page_count..]
            .iter()
            .map(|delta| delta.fragment.as_ref())
            .collect()
    }

    pub(crate) fn discard_partial(&mut self) {
        let completed_page_count = self.completed_page_counts.last().copied().unwrap_or(0);
        Arc::make_mut(&mut self.deltas).truncate(completed_page_count);
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn commit_page(
        &mut self,
        base_revision: ProposalRevision,
        stage: u64,
        cursor: u64,
        next_cursor: u64,
        max_response_bytes: u64,
        complete: bool,
        fragment: Arc<str>,
        expected_payload: Value,
    ) -> Option<ProposalRevision> {
        if self.revision != base_revision
            || stage != base_revision.get()
            || cursor != self.next_cursor()
            || next_cursor != cursor.checked_add(fragment.chars().count().try_into().ok()?)?
            || (!complete && fragment.is_empty())
        {
            return None;
        }
        let revision = if complete {
            base_revision.successor()?
        } else {
            base_revision
        };
        Arc::make_mut(&mut self.deltas).push(Arc::new(ProposalDelta {
            realization: self.realization,
            base_revision,
            revision,
            stage,
            cursor,
            next_cursor,
            max_response_bytes,
            complete,
            fragment,
            expected_digest: Arc::from(canonical_value_sha256(&expected_payload)),
        }));
        if complete {
            self.revision = revision;
            let page_count = self.deltas.len();
            Arc::make_mut(&mut self.completed_page_counts).push(page_count);
        }
        Some(revision)
    }
}

pub(crate) fn canonical_value_sha256(value: &Value) -> String {
    let bytes =
        serde_json::to_vec(value).expect("an in-memory JSON value always serializes to JSON");
    bytes_sha256(&bytes)
}

pub(crate) fn bytes_sha256(bytes: &[u8]) -> String {
    let mut digest = Sha256::new();
    digest.update(bytes);
    digest.finalize_hex()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn byte_digest_is_exact_sha256() {
        assert_eq!(
            bytes_sha256(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn realization_ids_are_stable_and_seeded_is_default() {
        assert_eq!(
            ProposalRealization::default(),
            ProposalRealization::SeededV1
        );
        assert_eq!(
            ProposalRealization::ReferenceV3.realization_id(),
            "lean-reference-v3"
        );
        assert_eq!(ProposalRealization::FastV1.realization_id(), "lean-fast-v1");
        assert_eq!(ProposalRealization::ReferenceV3.realization_version(), 3);
        assert_eq!(ProposalRealization::FastV1.realization_version(), 1);
        assert_eq!(
            ProposalRealization::parse_cli("fast"),
            Some(ProposalRealization::FastV1)
        );
        assert!(ProposalRealization::parse_cli("Example0012").is_none());
        assert_eq!(
            ProposalRealization::from_wire("lean-fast-v1", 1),
            Some(ProposalRealization::FastV1)
        );
        assert!(ProposalRealization::from_wire("lean-fast-v1", 3).is_none());
        assert_eq!(
            ProposalRealization::SeededV1.realization_id(),
            "lean-fast-v2-seeded"
        );
        assert_eq!(ProposalRealization::SeededV1.realization_version(), 2);
        assert_eq!(
            ProposalRealization::parse_cli("seeded"),
            Some(ProposalRealization::SeededV1)
        );
        assert_eq!(
            ProposalRealization::from_wire("lean-fast-v2-seeded", 2),
            Some(ProposalRealization::SeededV1)
        );
        assert!(ProposalRealization::from_wire("lean-fast-v2-seeded", 1).is_none());
        assert_eq!(
            ProposalRealization::CappedV1.realization_id(),
            "lean-fast-v3-capped"
        );
        assert_eq!(ProposalRealization::CappedV1.realization_version(), 3);
        assert_eq!(
            ProposalRealization::parse_cli("capped"),
            Some(ProposalRealization::CappedV1)
        );
        assert_eq!(
            ProposalRealization::from_wire("lean-fast-v3-capped", 3),
            Some(ProposalRealization::CappedV1)
        );
        assert!(ProposalRealization::from_wire("lean-fast-v3-capped", 2).is_none());
    }

    #[test]
    fn authority_commits_only_the_next_stage() {
        let mut authority = ReferenceProposalAuthority::new(ProposalRealization::ReferenceV3);
        assert!(
            authority
                .commit_page(
                    ProposalRevision::from_raw(1),
                    1,
                    0,
                    0,
                    4096,
                    true,
                    Arc::from(""),
                    Value::Null,
                )
                .is_none()
        );
        assert!(
            authority
                .commit_page(
                    ProposalRevision::INITIAL,
                    2,
                    0,
                    0,
                    4096,
                    true,
                    Arc::from(""),
                    Value::Null,
                )
                .is_none()
        );
        assert_eq!(
            authority.commit_page(
                ProposalRevision::INITIAL,
                0,
                0,
                2,
                4096,
                false,
                Arc::from("ab"),
                Value::Null,
            ),
            Some(ProposalRevision::INITIAL)
        );
        assert_eq!(authority.revision(), ProposalRevision::INITIAL);
        assert_eq!(
            authority
                .sync_through(ProposalRevision::INITIAL)
                .unwrap()
                .deltas
                .len(),
            0
        );
        assert_eq!(authority.sync().deltas.len(), 1);
        let mut discarded = authority.clone();
        discarded.discard_partial();
        assert_eq!(discarded.sync().deltas.len(), 0);
        assert_eq!(discarded.next_cursor(), 0);
        assert_eq!(
            authority.commit_page(
                ProposalRevision::INITIAL,
                0,
                2,
                2,
                4096,
                true,
                Arc::from(""),
                Value::Null,
            ),
            Some(ProposalRevision::from_raw(1))
        );
        assert_eq!(authority.sync().deltas.len(), 2);
        assert_eq!(authority.partial_fragment_text(), "");
    }
}
