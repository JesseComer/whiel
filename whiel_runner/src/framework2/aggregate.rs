//! Certification of one frozen Core's exact `2N+1` batch.
//!
//! `houdini.tex` Section 2, after the soundness theorem: certification
//! re-proves *every* condition of the frozen final Core — `N`
//! initialization conditions, `N` step conditions, and one termination
//! condition — none of them skipped because the search happens to hold
//! evidence for it. A condition the search served from its semantic
//! dictionary and a condition it closed by reviewed Lean theorem selection
//! on a protected row are launched here exactly like the rest.
//!
//! [`certify_frozen_core`] does that, in one shape:
//!
//! 1. Re-admit the frozen input and clauses. The frozen record's task and
//!    scope identities must match the live bound solver's, its canonical
//!    sources go back through Lean's admission, and each re-admitted clause
//!    must intern to the exact Lean-issued identity and catalog id the
//!    freeze recorded. Any drift in identity, level, or order fails closed.
//! 2. Rebuild the immutable candidate snapshot at the frozen levels and
//!    require its partition digest to equal the frozen record's, so the
//!    batch certifies the frozen Core and never a Core the certification
//!    itself changed.
//! 3. Run the Pass-7.4 coordinator ([`build_certificate`]) over that
//!    snapshot in canonical order, under this certification's own
//!    independent deadline, with bounded concurrency, and with each job's
//!    closed profile label read from the frozen record — never a fallback
//!    between profiles.
//! 4. Revalidate the finished batch: exactly `2N+1` receipts, ordinals
//!    `0..2N` each once, each clause job naming its own frozen row at its
//!    own frozen level, the termination job naming no clause, and every
//!    receipt carrying the label the frozen record assigned it.
//!
//! The result is one *private* checked aggregate candidate. It is not
//! published, it is not returned as a public `Valid`, and its tree lives
//! under a caller-supplied private root that
//! [`CheckedAggregateCandidate`] removes when it is dropped unless the
//! caller explicitly retains it. Pass 7.5g owns publication.

use std::collections::BTreeMap;
use std::fmt;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use tokio::time::Instant;

use crate::runtime::phase::{PhaseCancellation, PhaseStop};
use crate::runtime::{CancellationToken, SolverAdmission};

use super::admission::{FrameworkIIAdmissionContext, FrameworkIIAdmissionError};
use super::catalog::LeveledClauseCatalog;
#[cfg(feature = "test-hooks")]
use super::certificate::CertificateBuildHooks;
use super::certificate::{
    CertificateBuildError, CertificateBuildReceipt, CertificateBuildRequest, CertificateJobReceipt,
    build_certificate_in_owned_directory,
};
use super::certificate_ops::CertificateJob;
use super::freeze::{CoreFreezeError, FrozenCoreRow, FrozenLeveledCore};
use super::leancheck::{LeancheckProfile, PinnedLeancheckVampire};
use super::snapshot::LeveledCandidateSnapshot;
use super::solver::FrameworkIISolverContext;
use super::types::{AdmissionOutcome, FrameworkIILevel};

/// Default bound on how many of a frozen Core's `2N+1` jobs are solved at
/// once. Certification is the only consumer of the coordinator's
/// concurrent path; the checked-in-tree regeneration CLI stays sequential.
pub const DEFAULT_CERTIFICATION_CONCURRENCY: NonZeroUsize = NonZeroUsize::new(2).unwrap();

/// One request to certify a frozen Core's exact batch.
pub struct CertifyFrozenCoreRequest<'a> {
    /// The frozen record. Immutable: nothing here writes to it.
    pub frozen: &'a FrozenLeveledCore,
    /// The live bound admission context the frozen input is re-admitted
    /// through.
    pub admission: &'a FrameworkIIAdmissionContext,
    pub solver: &'a FrameworkIISolverContext,
    pub solver_admission: &'a SolverAdmission,
    /// The catalog the frozen clauses were interned in. Read only: the
    /// re-admitted clauses must already be interned here under the exact
    /// ids the freeze recorded.
    pub catalog: &'a LeveledClauseCatalog,
    pub pinned: &'a PinnedLeancheckVampire,
    /// Per-job leancheck deadline.
    pub time_limit_seconds: u64,
    /// This certification's own deadline, independent of the search's.
    pub certification_limit: Duration,
    /// How many jobs may be solved at once.
    pub concurrency: NonZeroUsize,
    pub repository_root: PathBuf,
    /// Parent directory for the coordinator's own staging tree.
    pub staging_root: PathBuf,
    /// Private root the candidate's tree is built under. It is never a
    /// published location: the candidate owns and removes its own
    /// subdirectory unless the caller retains it.
    pub private_root: PathBuf,
    /// Where the batch's staged solver-evidence subtree is moved just
    /// before the candidate's private `Certificate` tree is promoted, or
    /// `None` to drop it. See
    /// [`super::certificate::CertificateBuildRequest::evidence_destination`].
    /// Must not lie inside `private_root` or the caller's eventual
    /// publication destination. Removed again (best effort) if this
    /// candidate is ever dropped without being retained, exactly like the
    /// private tree, so a leftover evidence directory never blocks a later
    /// certification of the same frozen Core.
    pub evidence_destination: Option<PathBuf>,
    /// Deadline-free external cancellation root. The candidate owns a fresh
    /// certification phase through its final revalidation; search tokens are
    /// refused here because their expiry must not cancel certification.
    pub cancellation: &'a CancellationToken,
    #[cfg(feature = "test-hooks")]
    pub hooks: CertificateBuildHooks,
}

// ------------------------------------------------------------
// The Private Candidate
// ------------------------------------------------------------

/// Exclusive ownership is shared with the private builder capability.
type PrivateTree = crate::runtime::owned_path::OwnedDirectory;

/// One privately checked aggregate candidate for a frozen Core.
///
/// "Checked" means every one of the frozen Core's `2N+1` conditions was
/// re-proved by the pinned leancheck Vampire, every proof was packaged and
/// compiled, the aggregate theorem elaborated at the exact input-schema
/// Hoare-triple type, and its axiom closure audited to exactly std3.
///
/// "Private" and "candidate" mean what they say: this is not a published
/// certificate and not a public `Valid` result. It holds no run authority,
/// and its tree is removed when it is dropped unless [`Self::retain`] is
/// called. Pass 7.5g integrates it with the provider-neutral result
/// lifecycle and owns atomic publication.
///
/// A candidate whose build already moved its solver evidence out (see
/// [`CertifyFrozenCoreRequest::evidence_destination`]) removes that
/// directory too when it is dropped without being retained: evidence is
/// worth keeping only for a candidate that is actually published, exactly
/// the rule [`Self::retain`] already applies to the private tree itself.
#[derive(Debug)]
pub struct CheckedAggregateCandidate {
    phase: Option<PhaseCancellation>,
    certification_limit: Duration,
    frozen: FrozenLeveledCore,
    receipt: CertificateBuildReceipt,
    tree: PrivateTree,
    evidence_destination: Option<PathBuf>,
    retained: bool,
}

impl Drop for CheckedAggregateCandidate {
    fn drop(&mut self) {
        if self.retained {
            return;
        }
        if let Some(evidence_destination) = &self.evidence_destination {
            remove_evidence_best_effort(evidence_destination);
        }
    }
}

impl CheckedAggregateCandidate {
    pub(crate) fn take_certification_phase(
        &mut self,
    ) -> Result<(PhaseCancellation, Duration), AggregateCertificationError> {
        self.phase
            .take()
            .map(|phase| (phase, self.certification_limit))
            .ok_or_else(|| {
                AggregateCertificationError::PhaseControl(
                    "candidate certification phase was already consumed".into(),
                )
            })
    }

    /// The frozen Core this candidate certifies.
    pub fn frozen(&self) -> &FrozenLeveledCore {
        &self.frozen
    }

    /// The coordinator's own durable evidence for the batch.
    pub fn receipt(&self) -> &CertificateBuildReceipt {
        &self.receipt
    }

    /// The exact number of conditions this candidate re-proved: `2N+1`.
    pub fn condition_count(&self) -> usize {
        self.receipt.jobs.len()
    }

    /// The audited axiom closure of the aggregate theorem: exactly std3.
    pub fn axioms(&self) -> &[String] {
        &self.receipt.axioms
    }

    /// The private tree this candidate's sources live in. Never a
    /// published location.
    pub fn private_tree(&self) -> &Path {
        self.tree.path()
    }

    /// Keep the private tree — and any evidence directory this candidate's
    /// build already moved staged evidence into — in place instead of
    /// removing them on drop.
    ///
    /// Certification itself never calls this. It exists so Pass 7.5g's
    /// publication can take the tree over, and so a test can inspect it.
    pub fn retain(&mut self) {
        self.tree.preserve();
        self.retained = true;
    }
}

// ------------------------------------------------------------
// Certification
// ------------------------------------------------------------

/// Certify one frozen Core's exact `2N+1` batch. See the module doc.
pub async fn certify_frozen_core(
    mut request: CertifyFrozenCoreRequest<'_>,
) -> Result<CheckedAggregateCandidate, AggregateCertificationError> {
    // The one allowance begins at entry, before re-admission. Its owned
    // phase rides with the private candidate until publication revalidates it.
    let started_at = Instant::now();
    let deadline = started_at
        .checked_add(request.certification_limit)
        .ok_or_else(|| {
            AggregateCertificationError::PhaseControl(
                "certification allowance overflows the monotonic clock".into(),
            )
        })?;
    let phase = PhaseCancellation::new(request.cancellation).map_err(|_| {
        AggregateCertificationError::PhaseControl(
            "certification requires a deadline-free external root".into(),
        )
    })?;
    assert!(phase.token().bind_absolute_deadline(deadline));
    let result = certify_with_phase(&mut request, &phase).await;
    match result {
        Ok((receipt, tree)) => Ok(CheckedAggregateCandidate {
            phase: Some(phase),
            certification_limit: request.certification_limit,
            frozen: request.frozen.clone(),
            receipt,
            tree,
            evidence_destination: request.evidence_destination.clone(),
            retained: false,
        }),
        Err(error) => {
            // Preserve the original failure, but always stop/join the relay.
            // Awaited admission/build operations already own their child cleanup.
            let _ = phase.finish().await;
            Err(error)
        }
    }
}

fn phase_stop_error(phase: &PhaseCancellation, limit: Duration) -> AggregateCertificationError {
    match phase.stop_reason() {
        Some(PhaseStop::DeadlineExpired) => AggregateCertificationError::DeadlineExpired(limit),
        Some(PhaseStop::Interrupted) => AggregateCertificationError::Interrupted,
        None => AggregateCertificationError::PhaseControl(
            "certification cancelled without an external or deadline signal".into(),
        ),
    }
}

fn check_phase(
    phase: &PhaseCancellation,
    limit: Duration,
) -> Result<(), AggregateCertificationError> {
    if phase.stop_reason().is_some() {
        return Err(phase_stop_error(phase, limit));
    }
    Ok(())
}

async fn certify_with_phase(
    request: &mut CertifyFrozenCoreRequest<'_>,
    phase: &PhaseCancellation,
) -> Result<(CertificateBuildReceipt, PrivateTree), AggregateCertificationError> {
    check_phase(phase, request.certification_limit)?;
    let snapshot = readmit_frozen_core(request, phase).await?;
    check_phase(phase, request.certification_limit)?;
    std::fs::create_dir_all(&request.private_root).map_err(|error| {
        AggregateCertificationError::Io(format!(
            "create the private certification root {}: {error}",
            request.private_root.display()
        ))
    })?;
    let tree = prepare_private_tree(&request.private_root, request.frozen.freeze_digest())?;
    let destination = tree.path().join("Certificate");
    let frozen = request.frozen;
    let profiles = move |job: &CertificateJob| {
        frozen
            .job_profile(&job.role, job.clause_id)
            .map(LeancheckProfile::new)
    };
    // The same actively signalled token controls re-admission and every build
    // child. No fresh Duration or token restarts the certification allowance.
    let receipt = build_certificate_in_owned_directory(
        CertificateBuildRequest {
            solver: request.solver,
            admission: request.solver_admission,
            snapshot: Arc::clone(&snapshot),
            pinned: request.pinned,
            profiles: &profiles,
            time_limit_seconds: request.time_limit_seconds,
            concurrency: request.concurrency,
            repository_root: request.repository_root.clone(),
            staging_root: request.staging_root.clone(),
            destination,
            evidence_destination: request.evidence_destination.clone(),
            cancellation: phase.token(),
            #[cfg(feature = "test-hooks")]
            hooks: std::mem::take(&mut request.hooks),
        },
        &tree,
    )
    .await
    .map_err(|error| match error {
        CertificateBuildError::Cancelled => phase_stop_error(phase, request.certification_limit),
        error => AggregateCertificationError::Build(Box::new(error)),
    })?;
    // Past this point the build has succeeded, so any evidence destination
    // has already received the batch's staged evidence. A failure from
    // here on is this function's own — the batch does not match the
    // frozen record, or the certification's own deadline has since passed
    // — and it never becomes a [`CheckedAggregateCandidate`], so nothing
    // else will remove that evidence on drop; remove it here instead, so
    // a later certification of the same frozen Core is not blocked by it.
    if let Err(error) = validate_batch(request.frozen, &receipt)
        .and_then(|()| check_phase(phase, request.certification_limit))
    {
        if let Some(evidence_destination) = request.evidence_destination.as_deref() {
            remove_evidence_best_effort(evidence_destination);
        }
        return Err(error);
    }
    Ok((receipt, tree))
}

/// Best-effort removal of an evidence directory a certification attempt
/// already moved staged evidence into, when the attempt itself then fails
/// before it produces a [`CheckedAggregateCandidate`] to own that cleanup.
/// See [`CheckedAggregateCandidate`]'s own `Drop` for the case where a
/// candidate exists but is never retained.
fn remove_evidence_best_effort(path: &Path) {
    if let Err(error) = std::fs::remove_dir_all(path)
        && error.kind() != std::io::ErrorKind::NotFound
    {
        eprintln!(
            "warning: a failed certification could not remove its evidence directory {}: {error}",
            path.display()
        );
    }
}

/// Create the private tree this candidate builds under, refusing to touch a
/// tree that is already there.
///
/// Exclusive creation is the ownership boundary. A losing concurrent attempt
/// never acquires a removing guard, and a retained candidate survives a later
/// certification of the same frozen Core untouched.
fn prepare_private_tree(
    private_root: &Path,
    freeze_digest: &str,
) -> Result<PrivateTree, AggregateCertificationError> {
    let path = private_root.join(format!("aggregate-{}", &freeze_digest[..16]));
    PrivateTree::create(path.clone()).map_err(|error| {
        if error.kind() == std::io::ErrorKind::AlreadyExists {
            AggregateCertificationError::PrivateTreeExists(path)
        } else {
            AggregateCertificationError::Io(format!("create {}: {error}", path.display()))
        }
    })
}

/// Re-admit the frozen input and clauses and rebuild the frozen snapshot,
/// failing closed on every identity, level, and order disagreement.
async fn readmit_frozen_core(
    request: &CertifyFrozenCoreRequest<'_>,
    phase: &PhaseCancellation,
) -> Result<Arc<LeveledCandidateSnapshot>, AggregateCertificationError> {
    let frozen = request.frozen;
    let scope = request.solver.scope();
    if scope != request.admission.scope() || scope != request.catalog.scope() {
        return Err(AggregateCertificationError::AuthoritiesDisagree);
    }
    if scope.task_identity().canonical_id() != frozen.task_canonical_id()
        || scope.task_identity().namespace() != frozen.task_namespace()
        || scope.identity_sha256() != frozen.scope_identity_sha256()
    {
        return Err(AggregateCertificationError::StaleFrozenRecord {
            frozen_task: frozen.task_canonical_id().to_string(),
            live_task: scope.task_identity().canonical_id().to_string(),
        });
    }

    let sources = frozen.canonical_sources();
    let admitted = request
        .admission
        .admit_clauses(&sources, None, request.solver_admission, phase.token())
        .await
        .map_err(|error| match error {
            FrameworkIIAdmissionError::Cancelled => {
                phase_stop_error(phase, request.certification_limit)
            }
            error => AggregateCertificationError::Readmission(format!(
                "re-admit the frozen Core's clauses: {error}"
            )),
        })?;
    let AdmissionOutcome::Accepted(clauses) = admitted else {
        return Err(AggregateCertificationError::Readmission(
            "the frozen Core's own clauses were not re-admitted verbatim".to_string(),
        ));
    };
    if clauses.len() != frozen.rows().len() {
        return Err(AggregateCertificationError::Readmission(format!(
            "re-admitted {} clauses for {} frozen rows",
            clauses.len(),
            frozen.rows().len()
        )));
    }

    let mut level_of = BTreeMap::new();
    let mut interned_rows = Vec::with_capacity(clauses.len());
    for (clause, row) in clauses.iter().zip(frozen.rows()) {
        if clause.identity_sha256() != row.identity_sha256()
            || clause.canonical_source() != row.canonical_source()
        {
            return Err(AggregateCertificationError::IdentityDrift {
                clause_id: row.clause_id(),
                frozen: row.identity_sha256().to_string(),
                readmitted: clause.identity_sha256().to_string(),
            });
        }
        let interned = request
            .catalog
            .find(clause)
            .map_err(|error| AggregateCertificationError::Readmission(error.to_string()))?
            .ok_or(AggregateCertificationError::ClauseNotInterned {
                clause_id: row.clause_id(),
            })?;
        if interned.get() != row.clause_id() {
            return Err(AggregateCertificationError::IdentityDrift {
                clause_id: row.clause_id(),
                frozen: row.identity_sha256().to_string(),
                readmitted: format!("interned as clause {}", interned.get()),
            });
        }
        if level_of
            .insert(interned, FrameworkIILevel::new(row.level()))
            .is_some()
        {
            return Err(AggregateCertificationError::Freeze(
                CoreFreezeError::DuplicateRow(row.clause_id()),
            ));
        }
        interned_rows.push((interned, row));
    }

    let snapshot = LeveledCandidateSnapshot::build(
        request.catalog,
        frozen.max_level().map(FrameworkIILevel::new),
        level_of,
    )
    .map_err(|error| AggregateCertificationError::Readmission(error.to_string()))?;
    let rebuilt_order = snapshot
        .canonical_order()
        .iter()
        .map(|clause| clause.get())
        .collect::<Vec<_>>();
    let frozen_order = frozen
        .rows()
        .iter()
        .map(FrozenCoreRow::clause_id)
        .collect::<Vec<_>>();
    if rebuilt_order != frozen_order {
        return Err(AggregateCertificationError::OrderDrift);
    }
    for (interned, row) in interned_rows {
        let level = snapshot
            .level_of(interned)
            .ok_or(AggregateCertificationError::OrderDrift)?;
        if level.get() != row.level() {
            return Err(AggregateCertificationError::LevelDrift {
                clause_id: row.clause_id(),
                frozen: row.level(),
                rebuilt: level.get(),
            });
        }
    }
    if snapshot.partition_digest() != frozen.partition_digest() {
        return Err(AggregateCertificationError::PartitionDrift);
    }
    Ok(Arc::new(snapshot))
}

/// Revalidate the finished batch against the frozen record.
fn validate_batch(
    frozen: &FrozenLeveledCore,
    receipt: &CertificateBuildReceipt,
) -> Result<(), AggregateCertificationError> {
    let expected = frozen.condition_count();
    if receipt.jobs.len() != expected {
        return Err(AggregateCertificationError::ConditionCount {
            expected,
            found: receipt.jobs.len(),
        });
    }
    let mut by_ordinal: BTreeMap<u64, &CertificateJobReceipt> = BTreeMap::new();
    for job in &receipt.jobs {
        if by_ordinal.insert(job.ordinal, job).is_some() {
            return Err(AggregateCertificationError::DuplicateJobOrdinal(
                job.ordinal,
            ));
        }
    }
    let core_size = frozen.rows().len() as u64;
    for ordinal in 0..expected as u64 {
        let job = by_ordinal
            .get(&ordinal)
            .ok_or(AggregateCertificationError::MissingJobOrdinal(ordinal))?;
        let (expected_role, expected_row) = if ordinal < core_size {
            ("initialization", Some(&frozen.rows()[ordinal as usize]))
        } else if ordinal < 2 * core_size {
            (
                "maintenance",
                Some(&frozen.rows()[(ordinal - core_size) as usize]),
            )
        } else {
            ("termination", None)
        };
        if job.role != expected_role {
            return Err(AggregateCertificationError::JobRoleDrift {
                ordinal,
                expected: expected_role,
                found: job.role.clone(),
            });
        }
        match expected_row {
            Some(row) => {
                if job.clause_id != Some(row.clause_id()) || job.level != Some(row.level()) {
                    return Err(AggregateCertificationError::JobSubjectDrift {
                        ordinal,
                        expected_clause: Some(row.clause_id()),
                        found_clause: job.clause_id,
                    });
                }
            }
            None => {
                if job.clause_id.is_some() {
                    return Err(AggregateCertificationError::JobSubjectDrift {
                        ordinal,
                        expected_clause: None,
                        found_clause: job.clause_id,
                    });
                }
            }
        }
        let label = frozen
            .job_profile(&job.role, job.clause_id)
            .map_err(AggregateCertificationError::Freeze)?;
        if job.profile.profile() != label {
            return Err(AggregateCertificationError::ProfileDrift { ordinal });
        }
    }
    Ok(())
}

// ------------------------------------------------------------
// Errors
// ------------------------------------------------------------

/// Why the certification of a frozen Core's batch failed closed.
#[derive(Debug)]
pub enum AggregateCertificationError {
    /// The owned phase could not be established or completed.
    PhaseControl(String),
    /// The admission context, solver, and catalog do not share one scope.
    AuthoritiesDisagree,
    /// The frozen record belongs to another task or another bound input:
    /// certification never continues onto a stale record.
    StaleFrozenRecord {
        frozen_task: String,
        live_task: String,
    },
    /// Re-admitting the frozen clauses failed or was not verbatim.
    Readmission(String),
    /// A re-admitted clause's Lean-issued identity is not the one the
    /// freeze recorded.
    IdentityDrift {
        clause_id: u64,
        frozen: String,
        readmitted: String,
    },
    /// A frozen clause is not interned in the run's catalog at all.
    ClauseNotInterned { clause_id: u64 },
    /// The rebuilt snapshot places a frozen clause at another level.
    LevelDrift {
        clause_id: u64,
        frozen: u64,
        rebuilt: u64,
    },
    /// The rebuilt snapshot's canonical order is not the frozen order.
    OrderDrift,
    /// The rebuilt snapshot is not the frozen partition.
    PartitionDrift,
    /// The private tree this candidate would build under already exists.
    PrivateTreeExists(PathBuf),
    /// The batch did not carry exactly `2N+1` conditions.
    ConditionCount { expected: usize, found: usize },
    /// Two jobs of the batch claim the same ordinal.
    DuplicateJobOrdinal(u64),
    /// The batch has no job at one of the `2N+1` ordinals.
    MissingJobOrdinal(u64),
    /// A job's role is not the one its ordinal must carry.
    JobRoleDrift {
        ordinal: u64,
        expected: &'static str,
        found: String,
    },
    /// A job names another clause, or another level, than its frozen row.
    JobSubjectDrift {
        ordinal: u64,
        expected_clause: Option<u64>,
        found_clause: Option<u64>,
    },
    /// A job was solved under a profile other than its frozen label.
    ProfileDrift { ordinal: u64 },
    /// The frozen record itself was rejected.
    Freeze(CoreFreezeError),
    /// The Pass-7.4 coordinator failed.
    Build(Box<CertificateBuildError>),
    /// The certification's own independent deadline expired.
    DeadlineExpired(Duration),
    /// The run's cancellation stopped the certification.
    Interrupted,
    /// A filesystem operation failed.
    Io(String),
}

impl fmt::Display for AggregateCertificationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PhaseControl(detail) => {
                write!(formatter, "certification phase control failed: {detail}")
            }
            Self::AuthoritiesDisagree => write!(
                formatter,
                "the certification's admission, solver, and catalog do not share one scope"
            ),
            Self::StaleFrozenRecord {
                frozen_task,
                live_task,
            } => write!(
                formatter,
                "the frozen Core belongs to task {frozen_task}, not the live task {live_task}"
            ),
            Self::Readmission(detail) => write!(formatter, "re-admission failed: {detail}"),
            Self::IdentityDrift {
                clause_id,
                frozen,
                readmitted,
            } => write!(
                formatter,
                "clause {clause_id} was frozen as {frozen} and re-admitted as {readmitted}"
            ),
            Self::ClauseNotInterned { clause_id } => write!(
                formatter,
                "frozen clause {clause_id} is not interned in the run's catalog"
            ),
            Self::LevelDrift {
                clause_id,
                frozen,
                rebuilt,
            } => write!(
                formatter,
                "clause {clause_id} is frozen at level {frozen} and rebuilt at level {rebuilt}"
            ),
            Self::OrderDrift => write!(
                formatter,
                "the rebuilt Core's canonical order is not the frozen order"
            ),
            Self::PartitionDrift => {
                write!(formatter, "the rebuilt Core is not the frozen partition")
            }
            Self::PrivateTreeExists(path) => write!(
                formatter,
                "the private certification tree {} already exists",
                path.display()
            ),
            Self::ConditionCount { expected, found } => write!(
                formatter,
                "certification re-proved {found} conditions, not the frozen Core's exact {expected}"
            ),
            Self::DuplicateJobOrdinal(ordinal) => {
                write!(formatter, "two certificate jobs claim ordinal {ordinal}")
            }
            Self::MissingJobOrdinal(ordinal) => {
                write!(formatter, "no certificate job carries ordinal {ordinal}")
            }
            Self::JobRoleDrift {
                ordinal,
                expected,
                found,
            } => write!(
                formatter,
                "certificate job {ordinal} has role {found:?}, not {expected:?}"
            ),
            Self::JobSubjectDrift {
                ordinal,
                expected_clause,
                found_clause,
            } => write!(
                formatter,
                "certificate job {ordinal} names clause {found_clause:?}, not {expected_clause:?}"
            ),
            Self::ProfileDrift { ordinal } => write!(
                formatter,
                "certificate job {ordinal} was solved under a profile other than its frozen label"
            ),
            Self::Freeze(error) => write!(formatter, "{error}"),
            Self::Build(error) => write!(formatter, "{error}"),
            Self::DeadlineExpired(limit) => {
                write!(formatter, "the certification deadline of {limit:?} expired")
            }
            Self::Interrupted => write!(formatter, "the certification was cancelled"),
            Self::Io(detail) => write!(formatter, "{detail}"),
        }
    }
}

impl std::error::Error for AggregateCertificationError {}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use serde_json::{Value, json};

    use super::super::leancheck::LeancheckProfile;
    use super::super::production::ProofSearchProfile;
    use super::super::proof_transform::canonical::SolverMeasurements;
    use super::*;

    fn frozen(rows: usize) -> FrozenLeveledCore {
        let rows = (0..rows)
            .map(|index| {
                json!({
                    "clause_id": index as u64,
                    "level": index as u64,
                    "identity_sha256": format!("{index:064}"),
                    "canonical_source": format!("(clause_{index} = empty[1])"),
                    "initialization_profile": if index == 0 { "casc_2025" } else { "direct" },
                    "step_profile": "direct",
                })
            })
            .collect::<Vec<_>>();
        frozen_from_rows(rows)
    }

    /// One frozen record over hand-written rows, signed so the decoder's
    /// freeze-digest check passes and the fixture exercises the rule it is
    /// about rather than the digest.
    fn frozen_from_rows(rows: Vec<Value>) -> FrozenLeveledCore {
        FrozenLeveledCore::from_payload(&FrozenLeveledCore::signed_payload(&json!({
            "kind": super::super::freeze::FROZEN_CORE_KIND,
            "version": super::super::freeze::FROZEN_CORE_VERSION,
            "task_canonical_id": "Example0001",
            "task_namespace": "Whiel.Benchmark.Example0001",
            "task_identity": Value::Null,
            "scope_identity": Value::Null,
            "scope_identity_sha256": "a".repeat(64),
            "core_digest": "b".repeat(64),
            "partition_digest": "c".repeat(64),
            "max_level": Value::Null,
            "snapshot_identity": Value::Null,
            "rows": rows,
            "termination_profile": "direct",
            "termination_request_digest": "d".repeat(64),
            "termination_evidence_identity": "e".repeat(64),
        })))
        .expect("the fixture payload is well formed")
    }

    fn job(
        ordinal: u64,
        role: &str,
        clause: Option<u64>,
        profile: ProofSearchProfile,
    ) -> CertificateJobReceipt {
        CertificateJobReceipt {
            id: format!("job_{ordinal}"),
            role: role.to_string(),
            ordinal,
            clause_id: clause,
            level: clause,
            profile: LeancheckProfile::new(profile),
            invocation_identity: Value::Null,
            raw_sha256: "0".repeat(64),
            canonical_sha256: "0".repeat(64),
            transformed_sha256: "0".repeat(64),
            transforms: Vec::new(),
            packaged_sha256: "1".repeat(64),
            elapsed: Duration::from_millis(1),
            measurements: SolverMeasurements::default(),
            transform_elapsed: Duration::from_millis(1),
            proof_module_lean_elapsed: None,
            reconstruction_lean_elapsed: None,
        }
    }

    fn receipt(jobs: Vec<CertificateJobReceipt>) -> CertificateBuildReceipt {
        CertificateBuildReceipt {
            input_identity: Value::Null,
            scope_identity: Value::Null,
            snapshot_identity: Value::Null,
            jobs,
            lean_binary: PathBuf::from("/fixture/lean"),
            lake_lean_path_digest: "2".repeat(64),
            axioms: vec![
                "Classical.choice".to_string(),
                "Quot.sound".to_string(),
                "propext".to_string(),
            ],
            destination: PathBuf::from("/fixture/Certificate"),
            certificate_module: "Benchmark.Fixture.Certificate.Valid".to_string(),
            certificate_theorem: "Benchmark.Fixture.Certificate.input_hoare_triple_valid"
                .to_string(),
            shape: super::super::certificate_ops::CertificateBundleShape::Valid,
        }
    }

    /// The exact `2N+1` batch of a two-clause Core, with the mixed profile
    /// labels the frozen record assigned: nothing missing, nothing extra,
    /// nothing duplicated, and every job at its own ordinal.
    fn complete_batch() -> Vec<CertificateJobReceipt> {
        vec![
            job(0, "initialization", Some(0), ProofSearchProfile::Casc2025),
            job(1, "initialization", Some(1), ProofSearchProfile::Direct),
            job(2, "maintenance", Some(0), ProofSearchProfile::Direct),
            job(3, "maintenance", Some(1), ProofSearchProfile::Direct),
            job(4, "termination", None, ProofSearchProfile::Direct),
        ]
    }

    #[test]
    fn a_complete_mixed_profile_batch_validates() {
        validate_batch(&frozen(2), &receipt(complete_batch())).unwrap();
    }

    #[test]
    fn a_batch_missing_extra_duplicating_or_reordering_a_job_is_refused() {
        let frozen = frozen(2);

        let mut missing = complete_batch();
        missing.pop();
        let error = validate_batch(&frozen, &receipt(missing)).unwrap_err();
        assert!(
            matches!(
                error,
                AggregateCertificationError::ConditionCount {
                    expected: 5,
                    found: 4
                }
            ),
            "{error}"
        );

        let mut extra = complete_batch();
        extra.push(job(5, "termination", None, ProofSearchProfile::Direct));
        let error = validate_batch(&frozen, &receipt(extra)).unwrap_err();
        assert!(
            matches!(error, AggregateCertificationError::ConditionCount { .. }),
            "{error}"
        );

        // Five jobs, but one ordinal twice and another absent.
        let mut duplicated = complete_batch();
        duplicated[4] = job(3, "maintenance", Some(1), ProofSearchProfile::Direct);
        let error = validate_batch(&frozen, &receipt(duplicated)).unwrap_err();
        assert!(
            matches!(error, AggregateCertificationError::DuplicateJobOrdinal(3)),
            "{error}"
        );

        // Reordering the ordinals themselves swaps two jobs' roles.
        let mut reordered = complete_batch();
        reordered[0].ordinal = 2;
        reordered[2].ordinal = 0;
        let error = validate_batch(&frozen, &receipt(reordered)).unwrap_err();
        assert!(
            matches!(error, AggregateCertificationError::JobRoleDrift { .. }),
            "{error}"
        );
    }

    #[test]
    fn a_job_naming_another_clause_level_or_profile_is_refused() {
        let frozen = frozen(2);

        let mut wrong_clause = complete_batch();
        wrong_clause[1].clause_id = Some(0);
        let error = validate_batch(&frozen, &receipt(wrong_clause)).unwrap_err();
        assert!(
            matches!(error, AggregateCertificationError::JobSubjectDrift { .. }),
            "{error}"
        );

        let mut wrong_level = complete_batch();
        wrong_level[3].level = Some(7);
        let error = validate_batch(&frozen, &receipt(wrong_level)).unwrap_err();
        assert!(
            matches!(error, AggregateCertificationError::JobSubjectDrift { .. }),
            "{error}"
        );

        let mut clause_bearing_termination = complete_batch();
        clause_bearing_termination[4].clause_id = Some(1);
        let error = validate_batch(&frozen, &receipt(clause_bearing_termination)).unwrap_err();
        assert!(
            matches!(error, AggregateCertificationError::JobSubjectDrift { .. }),
            "{error}"
        );

        // A job solved under the other schedule is not this Core's job,
        // however well it proved: there is no fallback between profiles.
        let mut wrong_profile = complete_batch();
        wrong_profile[0].profile = LeancheckProfile::new(ProofSearchProfile::Direct);
        let error = validate_batch(&frozen, &receipt(wrong_profile)).unwrap_err();
        assert!(
            matches!(
                error,
                AggregateCertificationError::ProfileDrift { ordinal: 0 }
            ),
            "{error}"
        );
    }

    /// Canonical order is `(level, registration order key, id)`, so two
    /// clauses at one level registered in different batches can appear with
    /// their ids *descending*. Such a record freezes, and its batch
    /// validates row by row: nothing here reads the row order off the ids.
    #[test]
    fn a_batch_whose_ids_descend_within_one_level_validates() {
        let frozen = frozen_from_rows(
            [5_u64, 2]
                .into_iter()
                .map(|clause_id| {
                    json!({
                        "clause_id": clause_id,
                        "level": 0,
                        "identity_sha256": format!("{clause_id:064}"),
                        "canonical_source": format!("(clause_{clause_id} = empty[1])"),
                        "initialization_profile": "direct",
                        "step_profile": "direct",
                    })
                })
                .collect(),
        );
        assert_eq!(
            frozen
                .rows()
                .iter()
                .map(FrozenCoreRow::clause_id)
                .collect::<Vec<_>>(),
            vec![5, 2]
        );
        let mut jobs = vec![
            job(0, "initialization", Some(5), ProofSearchProfile::Direct),
            job(1, "initialization", Some(2), ProofSearchProfile::Direct),
            job(2, "maintenance", Some(5), ProofSearchProfile::Direct),
            job(3, "maintenance", Some(2), ProofSearchProfile::Direct),
            job(4, "termination", None, ProofSearchProfile::Direct),
        ];
        for job in jobs.iter_mut().take(4) {
            job.level = Some(0);
        }
        validate_batch(&frozen, &receipt(jobs)).unwrap();
    }

    /// The `PrivateTreeExists` refusal never removes the tree it refuses.
    ///
    /// A retained candidate's tree is a directory this certification did not
    /// create, so a second certification of the same frozen Core must fail
    /// closed and leave it exactly as it found it — the removing guard is
    /// built only after the existence check has passed.
    #[test]
    fn a_second_certification_refuses_and_leaves_a_retained_tree_intact() {
        let root = std::env::temp_dir().join(format!(
            "whiel_aggregate_private_tree_{}_{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&root).unwrap();
        let digest = "f".repeat(64);

        let mut first = prepare_private_tree(&root, &digest).unwrap();
        let path = first.path().to_path_buf();
        std::fs::write(path.join("Certificate.lean"), b"-- retained\n").unwrap();
        first.preserve();
        drop(first);
        assert!(path.exists(), "a retained tree survives its own guard");

        let error = prepare_private_tree(&root, &digest).unwrap_err();
        assert!(
            matches!(error, AggregateCertificationError::PrivateTreeExists(ref existing) if *existing == path),
            "{error}"
        );
        drop(error);
        assert!(
            path.join("Certificate.lean").exists(),
            "the refusal left the retained tree in place"
        );

        std::fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn concurrent_private_tree_claims_have_exactly_one_removing_owner() {
        use crate::runtime::owned_path::OwnedDirectory;
        use std::sync::{Arc, Barrier};
        let root = OwnedDirectory::fresh(&std::env::temp_dir(), "whiel-aggregate-race").unwrap();
        let barrier = Arc::new(Barrier::new(2));
        let handles: Vec<_> = (0..2)
            .map(|_| {
                let root = root.path().to_path_buf();
                let barrier = barrier.clone();
                std::thread::spawn(move || {
                    barrier.wait();
                    prepare_private_tree(&root, &"f".repeat(64))
                })
            })
            .collect();
        let mut owners = Vec::new();
        for handle in handles {
            match handle.join().unwrap() {
                Ok(owner) => owners.push(owner),
                Err(AggregateCertificationError::PrivateTreeExists(_)) => (),
                Err(error) => panic!("unexpected failure: {error}"),
            }
        }
        assert_eq!(owners.len(), 1);
        let owner = owners.pop().unwrap();
        let path = owner.path().to_path_buf();
        std::fs::write(path.join("sentinel"), b"owned").unwrap();
        assert!(prepare_private_tree(root.path(), &"f".repeat(64)).is_err());
        assert_eq!(std::fs::read(path.join("sentinel")).unwrap(), b"owned");
        drop(owner);
        assert!(!path.exists());
        drop(prepare_private_tree(root.path(), &"f".repeat(64)).unwrap());
    }

    /// A level-zero-only Core is the smallest complete batch: one
    /// initialization, one step, one termination.
    #[test]
    fn a_level_zero_core_has_exactly_three_conditions() {
        let frozen = frozen(1);
        assert_eq!(frozen.condition_count(), 3);
        validate_batch(
            &frozen,
            &receipt(vec![
                job(0, "initialization", Some(0), ProofSearchProfile::Casc2025),
                job(1, "maintenance", Some(0), ProofSearchProfile::Direct),
                job(2, "termination", None, ProofSearchProfile::Direct),
            ]),
        )
        .unwrap();
    }
}
