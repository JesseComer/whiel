//! Deterministic, untrusted rewrites of the Lean text Vampire emits.
//!
//! Every function here is a pure `&str -> Result<_, _>` rewrite of one
//! leancheck stdout. Nothing in this module is trusted: a transformation
//! changes only *how* a proof is written, never which theorem it states,
//! and a rewritten module is accepted only because a fresh Lean build
//! compiles the unchanged `theorem fullProof` statement and the
//! certificate's own exact-std3 axiom audit still passes. `VampLean/**` is
//! never touched; the rewrites target Whiel-owned or Mathlib tactics
//! (`Whiel.Vampire.ClauseProjection`, `Mathlib.Tactic.Sat.FromLRAT`) or
//! delete text.
//!
//! The pipeline runs in one fixed order — [`TRANSFORM_ORDER`] — between
//! [`super::leancheck::LeancheckRun::execute`] and the Lean worker's
//! `package_proof`. The *canonical* text, not the verbatim stdout, is
//! what stays staged beside the problem: a published file may not carry a
//! line whose value changes between two runs of one problem, or the tree
//! stops being something a reviewer can rebuild and compare. Each step
//! records its id, version, outcome and input/output digests in the build
//! receipt, and the receipt keeps the digest of the verbatim stdout too.
//!
//! Four steps are carried today, in this order:
//! [`ProofTransformId::Canonical`] (line endings, the volatile solver
//! lines out, the certificate resource policy in, the hygiene ban and the
//! exact import/section checks), [`ProofTransformId::AvatarKernelSat`],
//! which replaces the `casc_2025` profile's `bv_decide` AVATAR
//! reconstruction by a kernel-checked `lrat_proof`, and then the two
//! optional speed rewrites [`ProofTransformId::ClauseProjection`] and
//! [`ProofTransformId::LocalPrenex`]. The `variable` telescope order is
//! the one thing the canonical step deliberately leaves as Vampire wrote
//! it: that binder order is real Lean the reconstruction modules consume,
//! so no untrusted rewrite touches it.

pub mod canonical;
pub mod lrat;
mod prenex;
mod projection;

use std::fmt;

use serde_json::{Value, json};

use crate::encoding::bytes_sha256;

/// The Whiel-owned Lean module the projected proof text needs. It is
/// passed to `package_proof` as an explicit allow-list entry; the Lean
/// emitter refuses any extra import outside its own pinned set.
pub const CLAUSE_PROJECTION_IMPORT: &str = "Whiel.Vampire.ClauseProjection";

/// One version-pinned rewrite of Vampire's emitted Lean text.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProofTransformId {
    /// Line-ending normalization, the exact import/section checks the
    /// later rewrites depend on, the volatile solver lines out, the
    /// certificate resource policy in, and the hygiene token ban.
    Canonical,
    /// Targeted clause projection: the global `prenexify`/`cnfify`
    /// package is deleted and each of its assumption-only targets is
    /// proved by `vampire_project_ordered using stepN` instead.
    ClauseProjection,
    /// Dependency-sliced local prenex: a global skolemisation block whose
    /// live witnesses all come from its formula's first conjunct and are
    /// nullary introduces only those witnesses, by prenexing a projected
    /// slice of that conjunct instead of the whole formula.
    LocalPrenex,
    /// Kernel-checked LRAT for AVATAR refutations: each Boolean helper
    /// the `casc_2025` profile closes by `bv_decide` — which reconstructs
    /// natively and adds a `_native.bv_decide.ax…` axiom — is replaced by
    /// Mathlib's `lrat_proof` over a validated RUP-only trace, so the
    /// kernel checks the refutation term.
    AvatarKernelSat,
}

/// The one order every certificate build applies these in.
///
/// Two steps are *mandatory*: the canonical form every later recognizer
/// reads, and the kernel-SAT replacement of a `bv_decide` reconstruction,
/// which is the only reason an AVATAR proof may be published at all. The
/// two that follow are *optional* speed rewrites, and they are last for
/// that reason: a compile-gate rejection then walks back a suffix of this
/// order (see [`TransformedProof::fallback_candidates`]), and every
/// candidate it can reach still carries the kernel-checked refutation.
///
/// The kernel-SAT step edits the `inf_sN'` Boolean helpers, which stand
/// outside `fullProof`; the two optional steps edit lines inside it. The
/// regions are disjoint, so running kernel SAT first changes no output —
/// and it is also the order the legacy `_render_vampire_proofs` used
/// (`rewrite_avatar_kernel_sat`, then `normalize_raw_proof`'s projection).
pub const TRANSFORM_ORDER: [ProofTransformId; 4] = [
    ProofTransformId::Canonical,
    ProofTransformId::AvatarKernelSat,
    ProofTransformId::ClauseProjection,
    ProofTransformId::LocalPrenex,
];

/// How many leading entries of [`TRANSFORM_ORDER`] a published proof must
/// keep: the canonical form and, where it applied, the kernel-checked
/// AVATAR refutation. A compile-gate candidate never drops these.
const MANDATORY_TRANSFORMS: usize = 2;

impl ProofTransformId {
    /// The durable id recorded in receipts. Never reused for another
    /// rewrite; a changed rewrite bumps [`Self::version`] instead.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Canonical => "canonical",
            Self::ClauseProjection => "clause_projection",
            Self::LocalPrenex => "local_prenex",
            Self::AvatarKernelSat => lrat::TRANSFORM_ID,
        }
    }

    /// The rewrite's own version. Bumped whenever its output can differ
    /// on an input it already accepted.
    pub const fn version(self) -> u64 {
        match self {
            // 1 -> 2 in Pass 7.9b, which completed the legacy
            // canonicalization: the same input now loses its volatile
            // solver lines and gains the certificate resource policy.
            Self::Canonical => 2,
            Self::ClauseProjection => 1,
            Self::LocalPrenex => 2,
            Self::AvatarKernelSat => lrat::TRANSFORM_VERSION,
        }
    }
}

impl fmt::Display for ProofTransformId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.name())
    }
}

/// What one transformation did to the proof it was handed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofTransformOutcome {
    /// The rewrite recognized its input shape and changed the text.
    Applied,
    /// The rewrite found nothing it owns; the text is unchanged. A miss
    /// is not a failure: an unsupported legacy shape stays as it is.
    Miss,
    /// The rewrite applied, but the compile gate rejected a candidate
    /// carrying it, and the packaged proof is one further down the chain
    /// that does without it.
    Fallback,
}

impl ProofTransformOutcome {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Applied => "applied",
            Self::Miss => "miss",
            Self::Fallback => "fallback",
        }
    }
}

/// Durable evidence of one applied (or missed, or rolled back) rewrite.
#[derive(Clone, Debug)]
pub struct ProofTransformRecord {
    pub id: ProofTransformId,
    pub version: u64,
    pub outcome: ProofTransformOutcome,
    /// Digest of the text this step was handed.
    pub input_sha256: String,
    /// Digest of the text this step produced. On a
    /// [`ProofTransformOutcome::Fallback`] this is still the digest of
    /// the rejected candidate; the packaged text is named by
    /// `transformed_sha256` on the job receipt.
    pub output_sha256: String,
    /// Step-specific counters (recognized blocks, projected targets,
    /// retained legacy steps). Never a classification of the proof.
    pub detail: Value,
}

impl ProofTransformRecord {
    /// The receipt's own JSON shape for one transformation.
    pub fn to_json(&self) -> Value {
        json!({
            "id": self.id.name(),
            "version": self.version,
            "outcome": self.outcome.name(),
            "input_sha256": self.input_sha256,
            "output_sha256": self.output_sha256,
            "detail": self.detail,
        })
    }
}

/// The complete result of running [`TRANSFORM_ORDER`] over one raw proof.
#[derive(Clone, Debug)]
pub struct TransformedProof {
    /// The canonical text: what the raw stdout becomes before any
    /// rewrite that targets a tactic.
    pub canonical: String,
    pub canonical_sha256: String,
    /// The text handed to `package_proof`.
    pub transformed: String,
    pub transformed_sha256: String,
    /// Extra Lean imports the transformed text needs, in a stable order.
    pub extra_imports: Vec<String>,
    pub transforms: Vec<ProofTransformRecord>,
    /// The proofs the compile gate may retreat to, most rewritten first.
    ///
    /// Each is the text after one strictly shorter prefix of
    /// [`TRANSFORM_ORDER`], so the chain drops the optional rewrites one
    /// at a time — `LocalPrenex`, then `ClauseProjection` — instead of
    /// abandoning every rewrite at the first rejection. The kernel-SAT
    /// step is inside every prefix a candidate can be built from
    /// ([`MANDATORY_TRANSFORMS`]), so no candidate here reintroduces a
    /// `bv_decide` reconstruction: the canonical text of an AVATAR job
    /// closes its Boolean helpers natively and adds a
    /// `_native.bv_decide.ax…` axiom, which the build's own exact-std3
    /// audit would refuse — and publishing it would swap kernel trust for
    /// native-runtime trust. Such a job runs out of candidates and fails.
    ///
    /// Candidates whose text repeats one already in the list are left
    /// out: a step that missed produces nothing new to try.
    pub fallback_candidates: Vec<ProofCandidate>,
}

/// One proof the compile gate may package instead of the fully rewritten
/// text, together with the rewrites reaching it gives up.
#[derive(Clone, Debug)]
pub struct ProofCandidate {
    /// The rewrites this candidate drops relative to the full pipeline,
    /// in [`TRANSFORM_ORDER`]. Only steps that actually applied are
    /// listed, and only these are marked rolled back if it is packaged.
    pub dropped: Vec<ProofTransformId>,
    pub text: String,
    pub sha256: String,
    /// Extra Lean imports *this* text needs. A dropped step's import is
    /// dropped with it, so a candidate never asks the emitter to admit an
    /// import nothing in it uses.
    pub extra_imports: Vec<String>,
}

impl TransformedProof {
    /// Whether any rewrite after canonicalization changed the text.
    pub fn rewritten(&self) -> bool {
        self.transformed != self.canonical
    }

    /// Whether [`ProofTransformId::AvatarKernelSat`] replaced at least one
    /// AVATAR refutation in this proof.
    pub fn kernel_sat_applied(&self) -> bool {
        self.transforms.iter().any(|record| {
            record.id == ProofTransformId::AvatarKernelSat
                && record.outcome == ProofTransformOutcome::Applied
        })
    }
}

/// Record the rewrites one packaged fallback candidate gave up as rolled
/// back, and leave every other step's outcome alone.
///
/// Called by the compile gate on the job receipt once a candidate has
/// been staged in place of the rejected text. A step the candidate still
/// carries — the canonical form always, the kernel-checked AVATAR
/// refutation wherever it applied, and any optional rewrite the chain has
/// not yet reached — keeps the outcome it earned.
pub fn mark_rolled_back(records: &mut [ProofTransformRecord], dropped: &[ProofTransformId]) {
    for record in records {
        if dropped.contains(&record.id) && record.outcome == ProofTransformOutcome::Applied {
            record.outcome = ProofTransformOutcome::Fallback;
        }
    }
}

/// One fail-closed refusal by a proof transformation.
///
/// Every variant means the emitted text did not have the exact shape the
/// rewrite pins. Nothing is guessed and nothing partial is emitted: the
/// certificate build fails instead.
#[derive(Clone, Debug)]
pub struct ProofTransformError {
    pub transform: ProofTransformId,
    pub job_id: String,
    pub message: String,
}

impl fmt::Display for ProofTransformError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "proof transformation `{}` refused job `{}`: {}",
            self.transform, self.job_id, self.message
        )
    }
}

impl std::error::Error for ProofTransformError {}

/// Everything [`ProofTransformId::AvatarKernelSat`] needs beyond the text:
/// the SAT solver that produces an LRAT trace, and the identity of the
/// binary behind it, which is recorded verbatim in that step's receipt.
///
/// A build resolves this once, from the `kernel_lrat_cadical` role of
/// `toolchain.lock.json`, and lends it to every job. There is no
/// "no solver" mode: a proof carrying an AVATAR refutation with no trace
/// to check fails, it is never packaged as emitted.
pub struct KernelSatContext<'a> {
    solver: &'a dyn lrat::LratSolver,
    invocation_identity: Value,
}

impl<'a> KernelSatContext<'a> {
    pub fn new(solver: &'a dyn lrat::LratSolver, invocation_identity: Value) -> Self {
        Self {
            solver,
            invocation_identity,
        }
    }
}

/// The kernel-SAT step's own receipt evidence.
///
/// `probe_sha256` names the isolated per-helper probe module the rewrite
/// can render (each replaced helper alone, with `#print axioms` of both of
/// its declarations). The probe is *not* compiled: the gate on the whole
/// question is the build's own exact-std3 audit of `Check.lean`, which
/// covers every helper that the published theorem actually depends on, and
/// compiling a second module per helper would only re-ask a question that
/// audit already answers. The digest is recorded so the probe text of a
/// given build is reproducible if one is ever wanted by hand.
fn kernel_sat_detail(transform: &lrat::KernelSatTransform, identity: &Value) -> Value {
    json!({
        "helper_count": transform.helpers.len(),
        "already_applied": transform.outcome == lrat::KernelSatOutcome::AlreadyApplied,
        "cadical": identity.clone(),
        "probe_sha256": transform
            .probe_source
            .as_ref()
            .map(|source| Value::String(bytes_sha256(source.as_bytes())))
            .unwrap_or(Value::Null),
        "helpers": transform
            .helpers
            .iter()
            .map(|helper| {
                json!({
                    "step_id": helper.problem.step_id,
                    "kind": helper.problem.kind.name(),
                    "clauses": helper.problem.clause_count(),
                    "variables": helper.problem.variable_count(),
                    "lrat_additions": helper.lrat_additions,
                    "lrat_deletions": helper.lrat_deletions,
                    "lrat_max_clause_id": helper.lrat_max_clause_id,
                    "lrat_sha256": bytes_sha256(helper.lrat_source.as_bytes()),
                })
            })
            .collect::<Vec<_>>(),
    })
}

/// Run [`TRANSFORM_ORDER`] over one raw leancheck stdout.
///
/// The raw bytes themselves are never modified in place; the caller
/// records their digest, stages the canonical text, and packages the
/// selected transformed candidate.
pub fn apply_proof_transforms(
    job_id: &str,
    raw: &str,
    kernel_sat: &KernelSatContext<'_>,
) -> Result<TransformedProof, ProofTransformError> {
    let raw_sha256 = bytes_sha256(raw.as_bytes());
    let mut current = raw.to_string();
    let mut current_sha256 = raw_sha256;
    let mut extra_imports = Vec::new();
    let mut transforms = Vec::new();
    let mut canonical: Option<(String, String)> = None;
    // The text, digest and cumulative import list after each step, so the
    // compile gate's candidate chain is read off the run rather than
    // recomputed by replaying a shorter pipeline.
    let mut prefixes: Vec<(String, String, Vec<String>)> =
        Vec::with_capacity(TRANSFORM_ORDER.len());

    for id in TRANSFORM_ORDER {
        let input_sha256 = current_sha256.clone();
        let (output, outcome, detail, imports) = match id {
            ProofTransformId::Canonical => {
                let rendered =
                    canonical::canonicalize(&current).map_err(|message| ProofTransformError {
                        transform: id,
                        job_id: job_id.to_string(),
                        message,
                    })?;
                let outcome = if rendered == current {
                    ProofTransformOutcome::Miss
                } else {
                    ProofTransformOutcome::Applied
                };
                (rendered, outcome, json!({}), Vec::new())
            }
            ProofTransformId::ClauseProjection => {
                let summary =
                    projection::rewrite_projection_blocks(&current).map_err(|message| {
                        ProofTransformError {
                            transform: id,
                            job_id: job_id.to_string(),
                            message,
                        }
                    })?;
                let outcome = if summary.block_count() == 0 {
                    ProofTransformOutcome::Miss
                } else {
                    ProofTransformOutcome::Applied
                };
                let imports = if summary.block_count() == 0 {
                    Vec::new()
                } else {
                    vec![CLAUSE_PROJECTION_IMPORT.to_string()]
                };
                (summary.source.clone(), outcome, summary.detail(), imports)
            }
            ProofTransformId::LocalPrenex => {
                let summary = prenex::rewrite_prenex_slices(&current).map_err(|message| {
                    ProofTransformError {
                        transform: id,
                        job_id: job_id.to_string(),
                        message,
                    }
                })?;
                let outcome = if summary.block_count() == 0 {
                    ProofTransformOutcome::Miss
                } else {
                    ProofTransformOutcome::Applied
                };
                // A slice proves its conjunct by `vampire_project_ordered`
                // too, so it needs the same Whiel-owned import; the
                // projection step has normally asked for it already, and
                // the list deduplicates.
                let imports = if summary.block_count() == 0 {
                    Vec::new()
                } else {
                    vec![CLAUSE_PROJECTION_IMPORT.to_string()]
                };
                (summary.source.clone(), outcome, summary.detail(), imports)
            }
            ProofTransformId::AvatarKernelSat => {
                let transform =
                    lrat::transform_avatar_kernel_sat(&current, job_id, kernel_sat.solver)
                        .map_err(|error| ProofTransformError {
                            transform: id,
                            job_id: job_id.to_string(),
                            // An `Unsupported` trace is a *refusal*, not a
                            // skip: the reason is recorded and the job
                            // fails. Packaging the emitted text instead
                            // would publish a `bv_decide` reconstruction,
                            // which is exactly what this step exists to
                            // remove.
                            message: match &error {
                                lrat::KernelSatError::Unsupported(reason) => format!(
                                    "the AVATAR refutation is outside the RUP-only fragment, so \
                                     no kernel-checked replacement exists and the emitted \
                                     `bv_decide` reconstruction may not be published: {reason}"
                                ),
                                other => other.to_string(),
                            },
                        })?;
                let outcome = match transform.outcome {
                    lrat::KernelSatOutcome::NoHelpers => ProofTransformOutcome::Miss,
                    lrat::KernelSatOutcome::Applied | lrat::KernelSatOutcome::AlreadyApplied => {
                        ProofTransformOutcome::Applied
                    }
                };
                let imports = if transform.requires_from_lrat_import() {
                    vec![lrat::FROM_LRAT_IMPORT.to_string()]
                } else {
                    Vec::new()
                };
                let detail = kernel_sat_detail(&transform, &kernel_sat.invocation_identity);
                (transform.text.clone(), outcome, detail, imports)
            }
        };
        let output_sha256 = bytes_sha256(output.as_bytes());
        transforms.push(ProofTransformRecord {
            id,
            version: id.version(),
            outcome,
            input_sha256,
            output_sha256: output_sha256.clone(),
            detail,
        });
        for import in imports {
            if !extra_imports.contains(&import) {
                extra_imports.push(import);
            }
        }
        current = output;
        current_sha256 = output_sha256;
        if id == ProofTransformId::Canonical {
            canonical = Some((current.clone(), current_sha256.clone()));
        }
        prefixes.push((
            current.clone(),
            current_sha256.clone(),
            extra_imports.clone(),
        ));
    }

    let (canonical, canonical_sha256) = canonical.expect("the canonical step always runs");
    let fallback_candidates = fallback_candidates(&transforms, &prefixes);
    Ok(TransformedProof {
        canonical,
        canonical_sha256,
        transformed: current,
        transformed_sha256: current_sha256,
        extra_imports,
        transforms,
        fallback_candidates,
    })
}

/// Plan the mandatory SAT work before entering the pure transformation
/// pipeline. Use the identical canonical input that precedes AvatarKernelSat.
pub(super) fn plan_proof_sat(
    job_id: &str,
    raw: &str,
) -> Result<Vec<lrat::KernelSatProblem>, ProofTransformError> {
    let canonical = canonical::canonicalize(raw).map_err(|message| ProofTransformError {
        transform: ProofTransformId::Canonical,
        job_id: job_id.to_string(),
        message,
    })?;
    lrat::plan_native_avatar_kernel_sat(&canonical, job_id).map_err(|error| ProofTransformError {
        transform: ProofTransformId::AvatarKernelSat,
        job_id: job_id.to_string(),
        message: error.to_string(),
    })
}

/// Read the compile gate's candidate chain off one finished run.
///
/// Candidate `i` is the text after `TRANSFORM_ORDER[..=i]`, offered most
/// rewritten first, down to the shortest prefix a published proof may
/// have: [`MANDATORY_TRANSFORMS`] steps where the kernel-SAT rewrite
/// applied, and the canonical text alone where it did not.
fn fallback_candidates(
    transforms: &[ProofTransformRecord],
    prefixes: &[(String, String, Vec<String>)],
) -> Vec<ProofCandidate> {
    let kernel_sat_applied = transforms.iter().any(|record| {
        record.id == ProofTransformId::AvatarKernelSat
            && record.outcome == ProofTransformOutcome::Applied
    });
    let floor = if kernel_sat_applied {
        MANDATORY_TRANSFORMS
    } else {
        1
    };
    let full = prefixes.len();
    let mut seen = vec![prefixes[full - 1].1.clone()];
    let mut candidates = Vec::new();
    for length in (floor..full).rev() {
        let (text, sha256, imports) = &prefixes[length - 1];
        if seen.contains(sha256) {
            continue;
        }
        seen.push(sha256.clone());
        candidates.push(ProofCandidate {
            dropped: TRANSFORM_ORDER[length..]
                .iter()
                .copied()
                .filter(|id| {
                    transforms.iter().any(|record| {
                        record.id == *id && record.outcome == ProofTransformOutcome::Applied
                    })
                })
                .collect(),
            text: text.clone(),
            sha256: sha256.clone(),
            extra_imports: imports.clone(),
        });
    }
    candidates
}

#[cfg(test)]
mod tests;
