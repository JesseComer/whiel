//! Per-condition leancheck profile labels read from search provenance.
//!
//! Every certificate job of a frozen Core carries one closed profile label
//! (`direct` or `casc_2025`) naming the schedule the certification build
//! must run that job under. The label is *provenance*, never root
//! tracking: the reports make the ledger provenance-only and drop
//! search-time root tracking, so a committed clause's root is no longer a
//! place a profile can be read from.
//!
//! [`SearchProfileProvenance`] is the one source. It carries, per checked
//! condition (a check role together with the Lean-issued content digest of
//! the checked clause's own formula, plus the single termination
//! conjecture), the [`ProofSearchProfile`] of the winning attempt recorded
//! in the semantic dictionary's proof entry for that condition — the same
//! `RuntimeProofReceipt::winner` the original launch published. It is built
//! against the *final* Core, which is what picks the entry when a
//! conjecture holds several: the last launched entry whose cited premises
//! the final Core's own request carries. A condition the search never
//! closed by such a launch — one served entirely from the dictionary, or
//! closed by reviewed Lean theorem selection on a protected row — carries
//! no winner and takes the run's configured search profile instead.
//!
//! There is deliberately no fallback *between* profiles at certification
//! time. A job launched under its label either proves or fails; the
//! certification never retries the same job under the other schedule.

use std::collections::BTreeMap;
use std::sync::Arc;

use crate::vampire::PROOF_CASC_PROFILE_ID;

use super::ledger::FrameworkIICheckRole;
use super::production::ProofSearchProfile;

// ------------------------------------------------------------
// Condition Keys
// ------------------------------------------------------------

/// The dictionary index key of one tagged conjecture: `<role>:<digest>`.
///
/// This is the single owner of the key format. `production.rs`'s semantic
/// dictionary indexes its proof and refutation entries with exactly these
/// strings and [`SearchProfileProvenance`] looks winners up by them, so the
/// two can never drift apart.
pub(crate) fn tagged_conjecture_key(role: FrameworkIICheckRole, clause_identity: &str) -> Arc<str> {
    Arc::from(format!("{}:{clause_identity}", role_name(role)))
}

/// The dictionary index key of the single termination conjecture.
///
/// The termination request names no clause, so every termination entry is
/// indexed under this one key and separated only by its tagged premise set
/// (`houdini.tex` Section 4.4).
pub(crate) fn termination_conjecture_key() -> Arc<str> {
    Arc::from(format!(
        "termination:{}",
        super::production::FRAMEWORK_II_TERMINATION_CONJECTURE_NAME
    ))
}

/// The wire name of one check role, shared by the dictionary keys, the
/// certificate job roles Lean emits, and the frozen Core payload.
pub(crate) fn role_name(role: FrameworkIICheckRole) -> &'static str {
    match role {
        FrameworkIICheckRole::Initialization => "initialization",
        FrameworkIICheckRole::Maintenance => "maintenance",
    }
}

// ------------------------------------------------------------
// Provenance
// ------------------------------------------------------------

/// The run's per-condition profile provenance, captured from its checker.
///
/// `profile_id` binds the labels to the shared pinned argument-profile
/// version. `winners` holds one entry per condition of the final Core the
/// run's semantic dictionary recorded a *launched* proof for, against that
/// Core's own request; `configured` is the run's configured search profile,
/// which labels every other condition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SearchProfileProvenance {
    profile_id: &'static str,
    configured: ProofSearchProfile,
    winners: BTreeMap<Arc<str>, ProofSearchProfile>,
}

impl SearchProfileProvenance {
    /// Provenance with no recorded winner at all: every condition takes
    /// `configured`. This is what a checker without a semantic dictionary
    /// (a deterministic unit-test adapter) reports.
    pub fn configured_only(configured: ProofSearchProfile) -> Self {
        Self {
            profile_id: PROOF_CASC_PROFILE_ID,
            configured,
            winners: BTreeMap::new(),
        }
    }

    /// Build provenance from `configured` and the winners the run's
    /// dictionary recorded, keyed by tagged conjecture.
    pub(crate) fn from_dictionary_winners(
        configured: ProofSearchProfile,
        winners: impl IntoIterator<Item = (Arc<str>, ProofSearchProfile)>,
    ) -> Self {
        Self {
            profile_id: PROOF_CASC_PROFILE_ID,
            configured,
            winners: winners.into_iter().collect(),
        }
    }

    /// The shared pinned argument-profile version for every recorded label.
    pub fn profile_id(&self) -> &'static str {
        self.profile_id
    }

    /// The run's configured search profile: the label of every condition
    /// the search closed without a launch of its own.
    pub fn configured(&self) -> ProofSearchProfile {
        self.configured
    }

    /// How many conditions carry a recorded launch winner.
    pub fn recorded_winners(&self) -> usize {
        self.winners.len()
    }

    /// The label of one clause condition, by check role and the clause's
    /// Lean-issued formula identity.
    pub fn clause_profile(
        &self,
        role: FrameworkIICheckRole,
        clause_identity: &str,
    ) -> ProofSearchProfile {
        self.winners
            .get(tagged_conjecture_key(role, clause_identity).as_ref())
            .copied()
            .unwrap_or(self.configured)
    }

    /// The label of the single termination condition.
    pub fn termination_profile(&self) -> ProofSearchProfile {
        self.winners
            .get(termination_conjecture_key().as_ref())
            .copied()
            .unwrap_or(self.configured)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_unrecorded_condition_takes_the_configured_profile() {
        let provenance = SearchProfileProvenance::configured_only(ProofSearchProfile::Casc2025);
        assert_eq!(provenance.profile_id(), PROOF_CASC_PROFILE_ID);
        assert_eq!(provenance.recorded_winners(), 0);
        assert_eq!(
            provenance.clause_profile(FrameworkIICheckRole::Initialization, &"a".repeat(64)),
            ProofSearchProfile::Casc2025
        );
        assert_eq!(
            provenance.termination_profile(),
            ProofSearchProfile::Casc2025
        );
    }

    #[test]
    fn a_recorded_winner_labels_exactly_its_own_role_and_clause() {
        let identity = "b".repeat(64);
        let provenance = SearchProfileProvenance::from_dictionary_winners(
            ProofSearchProfile::Direct,
            [
                (
                    tagged_conjecture_key(FrameworkIICheckRole::Maintenance, &identity),
                    ProofSearchProfile::Casc2025,
                ),
                (termination_conjecture_key(), ProofSearchProfile::Casc2025),
            ],
        );
        assert_eq!(provenance.profile_id(), PROOF_CASC_PROFILE_ID);
        assert_eq!(
            provenance.clause_profile(FrameworkIICheckRole::Maintenance, &identity),
            ProofSearchProfile::Casc2025
        );
        // The initialization condition of the same clause is a different
        // conjecture and keeps the configured label.
        assert_eq!(
            provenance.clause_profile(FrameworkIICheckRole::Initialization, &identity),
            ProofSearchProfile::Direct
        );
        assert_eq!(
            provenance.termination_profile(),
            ProofSearchProfile::Casc2025
        );
        assert_eq!(provenance.recorded_winners(), 2);
    }
}
