//! Kernel-checked LRAT for AVATAR SAT/SMT refutations.
//!
//! Port of the legacy Tier-1 transformations 2 (AVATAR kernel SAT) and 6
//! (LRAT name qualification) of `CERTIFICATE_PROOF_TRANSFORMATIONS.md`,
//! whose Python originals are `rewrite_avatar_kernel_sat`,
//! `validate_avatar_kernel_sat_lrat`, `_render_avatar_lrat_helper`,
//! `_render_kernel_sat_probe` and `_qualify_vamplean_lrat_collisions` in
//! `whiel_synth/verification/tier1_bundle.py`.
//!
//! Under the `casc_2025` profile the pinned leancheck Vampire closes every
//! AVATAR refutation with a Boolean helper
//!
//! ```text
//! -- step N avatar sat refutation
//! set_option maxHeartbeats 200000000 in
//! -- this is probably due to a suboptimal encoding
//! theorem inf_sN' (sA2' sA3' : Bool) : (sA2' || sA3') → … → False := by
//!   intro h
//!   bv_decide
//! ```
//!
//! paired with a `Prop` bridge that discharges itself from the Boolean
//! helper. In the pinned Lean, `bv_decide` (like `native_decide`) compiles
//! and natively evaluates the reflected check and **adds** an axiom named
//! `_native.bv_decide.ax…` asserting the result, so a proof that goes
//! through it is not kernel-checked and cannot audit to std3.
//!
//! This module replaces each such pair by a `lrat_proof` command of
//! Mathlib's `Mathlib.Tactic.Sat.FromLRAT`, which builds an explicit proof
//! term the kernel checks, plus a bridge built from the original clauses by
//! ordinary `Or.elim`. The DIMACS is derived from the helper's own Boolean
//! clause signature; the LRAT trace comes from the CaDiCaL pinned in
//! `toolchain.lock.json` under the `kernel_lrat_cadical` role and is
//! accepted only when it is canonical and RUP-only — a RAT step is a
//! recorded miss, never a widened acceptance rule.
//!
//! The transformation is outside the trust boundary: the theorem statement
//! (the `Prop` bridge's own type) is unchanged, and acceptance still comes
//! from a fresh Lean build plus the exact-std3 audit.
//!
//! The solver seam can be exercised with recorded traces or a fake executable.
//! Production scratch ownership uses the shared runtime directory primitive;
//! the transformation itself still operates only on proof text and evidence.

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::runtime::owned_path::OwnedDirectory;

/// Version-pinned identity of this transformation, for build receipts.
pub const TRANSFORM_ID: &str = "avatar_kernel_sat_lrat";
/// Bumped whenever the emitted text of an applied rewrite changes.
pub const TRANSFORM_VERSION: u64 = 1;

/// The Mathlib module providing the `lrat_proof` command. A rewritten proof
/// needs it, but this module never writes an import line into the proof
/// text: the caller passes this *module name* to
/// `CertificateEmitter.packageProof` as an extra import, and `packageProof`
/// writes the line itself, after its own `import VampLean`. The probe
/// module below, which is not packaged, spells the line out.
pub const FROM_LRAT_IMPORT: &str = "Mathlib.Tactic.Sat.FromLRAT";

/// `Mathlib.Tactic.Sat.FromLRAT` transitively imports root declarations
/// that duplicate these four names of the pinned `VampLean.Runtime`. Raw
/// leancheck proofs are emitted under `open VampLean` and therefore mean
/// the VampLean declarations, so every executable occurrence is qualified.
const VAMPLEAN_LRAT_COLLISIONS: [&str; 4] = ["Xor'", "imp_iff_not_or", "not_and_or", "not_imp_not"];

// ------------------------------------------------------------
// Outcomes
// ------------------------------------------------------------

/// Why a rewrite was refused.
///
/// [`Self::Shape`] is fail-closed: the emitted text did not match the
/// pinned shape, or the SAT evidence was malformed, partial, or
/// inconsistent with the theorem it is supposed to discharge. Nothing is
/// rewritten and the job fails.
///
/// [`Self::Unsupported`] is a recorded miss: the evidence is well formed
/// but outside the accepted fragment (a RAT step). The caller records the
/// reason; it never widens the acceptance rule to admit it.
///
/// [`Self::Solver`] is an environment fault (CaDiCaL missing, failing, or
/// producing no trace).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KernelSatError {
    Shape(String),
    Unsupported(String),
    Solver(String),
}

impl std::fmt::Display for KernelSatError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Shape(message) => write!(formatter, "{message}"),
            Self::Unsupported(message) => write!(formatter, "{message}"),
            Self::Solver(message) => write!(formatter, "{message}"),
        }
    }
}

impl std::error::Error for KernelSatError {}

/// What one call to [`transform_avatar_kernel_sat`] did to the text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KernelSatOutcome {
    /// The proof carries no AVATAR refutation (every `direct`-profile
    /// proof, and any `casc_2025` proof whose winning strategy ran without
    /// AVATAR). The text is returned unchanged.
    NoHelpers,
    /// Every helper was replaced by a kernel-checked LRAT helper.
    Applied,
    /// The proof already carried kernel-checked LRAT helpers, and every one
    /// of them re-rendered byte-identically from its own embedded evidence.
    /// The text is returned unchanged.
    AlreadyApplied,
}

/// The rewritten proof text and the evidence behind it.
#[derive(Clone, Debug)]
pub struct KernelSatTransform {
    pub outcome: KernelSatOutcome,
    /// The proof text to hand to `packageProof`.
    pub text: String,
    /// One entry per AVATAR refutation, in emitted order.
    pub helpers: Vec<ValidatedKernelSat>,
    /// A standalone module that declares every rewritten helper in
    /// isolation and `#print axioms` of both its declarations, for the
    /// per-helper compile-and-audit probe. `None` when nothing was
    /// rewritten.
    pub probe_source: Option<String>,
}

impl KernelSatTransform {
    /// Whether [`Self::text`] needs the extra Mathlib import admitted by
    /// `packageProof`'s allow-list.
    ///
    /// The text itself never carries the import line; the caller passes
    /// [`FROM_LRAT_IMPORT`] to `packageProof` when this is true, and
    /// `packageProof` inserts it after `import VampLean`.
    pub fn requires_from_lrat_import(&self) -> bool {
        !self.helpers.is_empty()
    }
}

// ------------------------------------------------------------
// The Pinned Helper Shape
// ------------------------------------------------------------

/// Which emitter marker introduced the refutation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AvatarKind {
    Sat,
    Smt,
}

impl AvatarKind {
    pub fn name(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Smt => "smt",
        }
    }

    fn parse(text: &str) -> Option<Self> {
        match text {
            "sat" => Some(Self::Sat),
            "smt" => Some(Self::Smt),
            _ => None,
        }
    }
}

/// One AVATAR refutation's SAT problem, as read out of the emitted text.
///
/// `clauses` holds the emitted clause signature: a clause is a list of
/// `(sA` id`, positive)` literals in strictly increasing id order, and the
/// helper's statement is the implication of all clauses to `False`. The
/// Boolean helper and its `Prop` bridge must produce the same signature.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelSatProblem {
    pub step_id: u64,
    pub kind: AvatarKind,
    pub variable_ids: Vec<u64>,
    pub clauses: Vec<Vec<(u64, bool)>>,
    pub prop_formula: String,
    pub cnf_source: String,
}

impl KernelSatProblem {
    pub fn clause_count(&self) -> usize {
        self.clauses.len()
    }

    pub fn variable_count(&self) -> usize {
        self.variable_ids.len()
    }
}

/// A problem together with a validated canonical RUP-only LRAT trace.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidatedKernelSat {
    pub problem: KernelSatProblem,
    pub lrat_source: String,
    pub lrat_additions: u64,
    pub lrat_deletions: u64,
    pub lrat_max_clause_id: u64,
}

// ------------------------------------------------------------
// The Solver Seam
// ------------------------------------------------------------

/// Produces an LRAT refutation trace for one DIMACS problem.
///
/// The seam exists so the rewrite itself stays a pure function of text: the
/// production implementation is [`CadicalLratSolver`] over the binary
/// pinned by the `kernel_lrat_cadical` toolchain-lock role, and tests
/// supply recorded traces instead.
/// The bound is `Send + Sync` because a concurrent certificate build lends
/// one solver to every job task; an implementation therefore keeps no
/// shared working files: each invocation reserves its own directory, even
/// when another invocation has the same root and `step_id`.
pub trait LratSolver: Send + Sync {
    /// Refute `cnf_source` and return the LRAT trace as text.
    ///
    /// `step_id` identifies the AVATAR step for diagnostics and for laying
    /// out per-helper working files. An implementation returns
    /// [`KernelSatError::Solver`] when it cannot produce a trace at all;
    /// whether the trace is acceptable is decided here, not by the solver.
    fn refute(&self, step_id: u64, cnf_source: &str) -> Result<String, KernelSatError>;
}

/// Recorded traces keyed by AVATAR step id, for tests and for replaying a
/// sealed receipt without rerunning the solver.
pub struct RecordedLratSolver {
    traces: Vec<(u64, String)>,
}

/// Traces produced asynchronously for exact planned CNF bytes. Replaying
/// the pure transformation cannot start another process or use a trace for
/// a different problem that happens to share a step identifier.
pub(crate) struct PreparedLratSolver {
    traces: Vec<(KernelSatProblem, String)>,
}

impl PreparedLratSolver {
    pub(crate) fn new(traces: Vec<(KernelSatProblem, String)>) -> Self {
        Self { traces }
    }
}

impl LratSolver for PreparedLratSolver {
    fn refute(&self, step_id: u64, cnf_source: &str) -> Result<String, KernelSatError> {
        self.traces
            .iter()
            .find(|(problem, _)| problem.step_id == step_id && problem.cnf_source == cnf_source)
            .map(|(_, trace)| trace.clone())
            .ok_or_else(|| {
                KernelSatError::Solver(format!(
                    "no prepared LRAT trace for the exact CNF of AVATAR step {step_id}"
                ))
            })
    }
}

impl RecordedLratSolver {
    pub fn new(traces: Vec<(u64, String)>) -> Self {
        Self { traces }
    }
}

impl LratSolver for RecordedLratSolver {
    fn refute(&self, step_id: u64, _cnf_source: &str) -> Result<String, KernelSatError> {
        self.traces
            .iter()
            .find(|(recorded, _)| *recorded == step_id)
            .map(|(_, trace)| trace.clone())
            .ok_or_else(|| {
                KernelSatError::Solver(format!("no recorded LRAT trace for AVATAR step {step_id}"))
            })
    }
}

/// The pinned CaDiCaL, invoked with exactly the locked arguments.
///
/// The binary and its argument vector come from the `kernel_lrat_cadical`
/// role of `toolchain.lock.json`; see
/// [`crate::framework2::PinnedKernelLratCadical`], which resolves and
/// digest-checks it. The environment contract mirrors the legacy campaign's
/// `inherit-without-cadical-options-locale-c-v1`: the host environment
/// without any `CADICAL_*` override, and `LANG`/`LC_ALL` forced to `C`, so
/// a host option can never change the trace.
pub struct CadicalLratSolver {
    executable: PathBuf,
    arguments: Vec<String>,
    working_root: PathBuf,
}

/// The environment contract this solver runs CaDiCaL under, recorded in
/// the build receipt beside the binary's identity.
pub const CADICAL_ENVIRONMENT_CONTRACT: &str = "inherit-without-cadical-options-locale-c-v1";

impl CadicalLratSolver {
    /// `working_root` receives an exclusively created `step-<id>-<attempt>/`
    /// directory per invocation, holding its `input.cnf` and `proof.lrat`.
    /// Evidence remains until the owner of `working_root` removes that tree.
    pub fn new(executable: PathBuf, arguments: Vec<String>, working_root: PathBuf) -> Self {
        Self {
            executable,
            arguments,
            working_root,
        }
    }

    pub fn executable(&self) -> &Path {
        &self.executable
    }
}

impl LratSolver for CadicalLratSolver {
    fn refute(&self, step_id: u64, cnf_source: &str) -> Result<String, KernelSatError> {
        let directory = OwnedDirectory::fresh(&self.working_root, &format!("step-{step_id}"))
            .map_err(|error| {
                KernelSatError::Solver(format!("reserve AVATAR step {step_id} directory: {error}"))
            })?
            .retain();
        let cnf_path = directory.join("input.cnf");
        let lrat_path = directory.join("proof.lrat");
        // Both paths are new inside this invocation's exclusively owned
        // directory. A prior attempt's trace is never read, removed, or reused.
        std::fs::write(&cnf_path, cnf_source).map_err(|error| {
            KernelSatError::Solver(format!("write {}: {error}", cnf_path.display()))
        })?;

        let mut command = Command::new(&self.executable);
        command.arg(&cnf_path);
        command.arg(&lrat_path);
        command.args(&self.arguments);
        command.current_dir(&directory);
        for (name, _) in std::env::vars_os() {
            if name
                .to_string_lossy()
                .to_uppercase()
                .starts_with("CADICAL_")
            {
                command.env_remove(&name);
            }
        }
        command.env("LANG", "C");
        command.env("LC_ALL", "C");

        let output = command.output().map_err(|error| {
            KernelSatError::Solver(format!(
                "run {} on AVATAR step {step_id}: {error}",
                self.executable.display()
            ))
        })?;
        // CaDiCaL reports unsatisfiability as exit status 20; 10 is a model
        // (which would mean the emitted helper is not a refutation at all)
        // and anything else is a fault.
        match output.status.code() {
            Some(20) => {}
            Some(10) => {
                return Err(KernelSatError::Shape(format!(
                    "AVATAR step {step_id} clause set is satisfiable"
                )));
            }
            other => {
                return Err(KernelSatError::Solver(format!(
                    "CaDiCaL exited with {other:?} on AVATAR step {step_id}"
                )));
            }
        }
        std::fs::read_to_string(&lrat_path).map_err(|error| {
            KernelSatError::Solver(format!("read {}: {error}", lrat_path.display()))
        })
    }
}

// ------------------------------------------------------------
// Entry Point
// ------------------------------------------------------------

/// Replace every AVATAR refutation of `raw` by a kernel-checked LRAT
/// helper and qualify the names Mathlib's LRAT checker would shadow.
///
/// No import line is written: a caller whose result reports
/// [`KernelSatTransform::requires_from_lrat_import`] hands
/// [`FROM_LRAT_IMPORT`] to `packageProof` as an extra import instead, and
/// `packageProof` inserts it after its own `import VampLean`.
///
/// `raw` is the emitted leancheck text exactly as Vampire printed it; the
/// returned text differs from it only inside the replaced blocks and in the
/// qualified name occurrences. Trailing
/// whitespace is tolerated when matching the pinned shape (the emitter
/// leaves some) but never rewritten: whitespace normalization is
/// transformation 1's business, not this one's.
pub fn transform_avatar_kernel_sat(
    raw: &str,
    job_id: &str,
    solver: &dyn LratSolver,
) -> Result<KernelSatTransform, KernelSatError> {
    let lines: Vec<String> = raw.split('\n').map(str::to_string).collect();
    let trimmed: Vec<String> = lines
        .iter()
        .map(|line| line.trim_end().to_string())
        .collect();
    let markers = avatar_markers(&trimmed, job_id)?;
    if markers.is_empty() {
        // Missing markers do not authorize native closers or external
        // LRAT commands, including unused helpers outside fullProof.
        verify_rewritten(raw, &[], job_id)?;
        return Ok(KernelSatTransform {
            outcome: KernelSatOutcome::NoHelpers,
            text: raw.to_string(),
            helpers: Vec::new(),
            probe_source: None,
        });
    }

    let mut parsed: Vec<ParsedHelper> = Vec::with_capacity(markers.len());
    for marker in &markers {
        parsed.push(if marker.embedded {
            parse_embedded_lrat_helper(&trimmed, marker, job_id)?
        } else {
            parse_native_helper(&trimmed, marker, job_id)?
        });
    }
    for pair in parsed.windows(2) {
        if pair[0].end_line > pair[1].marker_line {
            return Err(KernelSatError::Shape(format!(
                "{job_id} has overlapping AVATAR refutation blocks"
            )));
        }
    }
    let embedded_count = parsed
        .iter()
        .filter(|helper| helper.validated.is_some())
        .count();
    if embedded_count != 0 && embedded_count != parsed.len() {
        return Err(KernelSatError::Shape(format!(
            "{job_id} mixes native and kernel-checked AVATAR refutations"
        )));
    }
    let already_applied = embedded_count == parsed.len();

    let mut helpers: Vec<ValidatedKernelSat> = Vec::with_capacity(parsed.len());
    for helper in &parsed {
        match &helper.validated {
            Some(validated) => helpers.push(validated.clone()),
            None => {
                let trace = solver.refute(helper.problem.step_id, &helper.problem.cnf_source)?;
                helpers.push(validate_lrat(helper.problem.clone(), &trace, job_id)?);
            }
        }
    }

    let text = if already_applied {
        raw.to_string()
    } else {
        let mut rewritten = lines.clone();
        for (helper, validated) in parsed.iter().zip(helpers.iter()).rev() {
            let block = render_lrat_helper(validated);
            rewritten.splice(helper.marker_line..helper.end_line, block);
        }
        qualify_lrat_collisions(&rewritten.join("\n"), job_id)?
    };

    verify_rewritten(&text, &helpers, job_id)?;

    Ok(KernelSatTransform {
        outcome: if already_applied {
            KernelSatOutcome::AlreadyApplied
        } else {
            KernelSatOutcome::Applied
        },
        text,
        probe_source: Some(render_kernel_sat_probe(&helpers)),
        helpers,
    })
}

/// Read the AVATAR refutations of `raw` without solving anything.
///
/// This is the solver-free half of [`transform_avatar_kernel_sat`]: it
/// applies the same pinned-shape checks and returns the DIMACS each helper
/// needs, for a caller that wants to plan (or test) the rewrite before
/// launching CaDiCaL.
pub fn plan_avatar_kernel_sat(
    raw: &str,
    job_id: &str,
) -> Result<Vec<KernelSatProblem>, KernelSatError> {
    let trimmed: Vec<String> = raw
        .split('\n')
        .map(|line| line.trim_end().to_string())
        .collect();
    let markers = avatar_markers(&trimmed, job_id)?;
    let mut problems = Vec::with_capacity(markers.len());
    for marker in &markers {
        let helper = if marker.embedded {
            parse_embedded_lrat_helper(&trimmed, marker, job_id)?
        } else {
            parse_native_helper(&trimmed, marker, job_id)?
        };
        problems.push(helper.problem);
    }
    Ok(problems)
}

/// Only native helpers need a solver. Embedded helpers already contain
/// their checked trace; preparation must preserve their idempotent path.
pub(super) fn plan_native_avatar_kernel_sat(
    raw: &str,
    job_id: &str,
) -> Result<Vec<KernelSatProblem>, KernelSatError> {
    let trimmed: Vec<String> = raw
        .lines()
        .map(|line| line.trim_end().to_string())
        .collect();
    let markers = avatar_markers(&trimmed, job_id)?;
    let problems = plan_avatar_kernel_sat(raw, job_id)?;
    let embedded = markers.iter().filter(|marker| marker.embedded).count();
    if embedded != 0 && embedded != markers.len() {
        return Err(KernelSatError::Shape(format!(
            "{job_id} mixes native and kernel-checked AVATAR refutations"
        )));
    }
    Ok(problems
        .into_iter()
        .zip(markers)
        .filter_map(|(problem, marker)| (!marker.embedded).then_some(problem))
        .collect())
}

// ------------------------------------------------------------
// Marker Recognition
// ------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
struct AvatarMarker {
    line: usize,
    step_id: u64,
    kind: AvatarKind,
    embedded: bool,
}

struct ParsedHelper {
    problem: KernelSatProblem,
    marker_line: usize,
    end_line: usize,
    /// `Some` when the block already carried its own validated LRAT.
    validated: Option<ValidatedKernelSat>,
}

const NATIVE_MARKER_SUFFIX: &str = " refutation";
const LRAT_MARKER_SUFFIX: &str = " refutation via kernel-checked LRAT";

/// Parse `-- step <n> avatar <kind><suffix>` as a full line.
fn parse_avatar_marker(line: &str, suffix: &str) -> Option<(u64, AvatarKind)> {
    let rest = line.strip_prefix("-- step ")?;
    let (step, rest) = split_number(rest)?;
    let rest = rest.strip_prefix(" avatar ")?;
    let kind_text = rest.strip_suffix(suffix)?;
    Some((step, AvatarKind::parse(kind_text)?))
}

/// Any comment that looks like an AVATAR refutation marker but is not one
/// of the two exact shapes; recognizing it is what keeps an emitter change
/// from being silently skipped.
fn is_avatar_marker_like(line: &str) -> bool {
    let Some(rest) = line.strip_prefix("-- step ") else {
        return false;
    };
    let Some((_, rest)) = split_number(rest) else {
        return false;
    };
    let Some(rest) = rest.strip_prefix(" avatar ") else {
        return false;
    };
    rest.contains("refutation")
}

fn avatar_markers(trimmed: &[String], job_id: &str) -> Result<Vec<AvatarMarker>, KernelSatError> {
    let source: Vec<char> = format!("{}\n", trimmed.join("\n")).chars().collect();
    let comment_lines = line_comment_lines(&source);
    let mut markers: Vec<AvatarMarker> = Vec::new();
    for line_number in comment_lines {
        let Some(line) = trimmed.get(line_number) else {
            continue;
        };
        if let Some((step_id, kind)) = parse_avatar_marker(line, LRAT_MARKER_SUFFIX) {
            markers.push(AvatarMarker {
                line: line_number,
                step_id,
                kind,
                embedded: true,
            });
        } else if let Some((step_id, kind)) = parse_avatar_marker(line, NATIVE_MARKER_SUFFIX) {
            markers.push(AvatarMarker {
                line: line_number,
                step_id,
                kind,
                embedded: false,
            });
        } else if is_avatar_marker_like(line) {
            return Err(KernelSatError::Shape(format!(
                "{job_id} has an unrecognized AVATAR refutation marker"
            )));
        }
    }
    markers.sort_by_key(|marker| marker.line);
    let mut seen: Vec<u64> = markers.iter().map(|marker| marker.step_id).collect();
    seen.sort_unstable();
    let unique = {
        let mut unique = seen.clone();
        unique.dedup();
        unique
    };
    if unique.len() != markers.len() {
        return Err(KernelSatError::Shape(format!(
            "{job_id} repeats an AVATAR refutation step"
        )));
    }
    Ok(markers)
}

// ------------------------------------------------------------
// The Native Helper Shape
// ------------------------------------------------------------

fn parse_native_helper(
    lines: &[String],
    marker: &AvatarMarker,
    job_id: &str,
) -> Result<ParsedHelper, KernelSatError> {
    let step_id = marker.step_id;
    let mut cursor = marker.line + 1;
    let shape_error = || {
        KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} differs from the pinned {} emitter shape",
            marker.kind.name()
        ))
    };
    let require = |cursor: &mut usize, expected: &str| -> Result<(), KernelSatError> {
        if lines.get(*cursor).map(String::as_str) != Some(expected) {
            return Err(shape_error());
        }
        *cursor += 1;
        Ok(())
    };

    if marker.kind == AvatarKind::Sat {
        require(&mut cursor, "set_option maxHeartbeats 200000000 in")?;
        require(
            &mut cursor,
            "-- this is probably due to a suboptimal encoding",
        )?;
    }

    let bool_header = lines.get(cursor).ok_or_else(|| {
        KernelSatError::Shape(format!("{job_id} AVATAR step {step_id} is truncated"))
    })?;
    let (bool_step, variables, bool_formula) = parse_bool_header(bool_header).ok_or_else(|| {
        KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} has a mismatched Boolean helper"
        ))
    })?;
    if bool_step != step_id {
        return Err(KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} has a mismatched Boolean helper"
        )));
    }
    let variable_ids: Vec<u64> = variables
        .iter()
        .map(|variable| {
            variable
                .strip_prefix("sA")
                .and_then(|digits| digits.parse::<u64>().ok())
                .ok_or_else(|| {
                    KernelSatError::Shape(format!(
                        "{job_id} AVATAR step {step_id} has a malformed Boolean binder"
                    ))
                })
        })
        .collect::<Result<_, _>>()?;
    if !strictly_increasing(&variable_ids) {
        return Err(KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} has noncanonical Boolean variables"
        )));
    }
    let bool_clauses = formula_signature(&bool_formula, true, job_id, step_id)?;
    let mut mentioned: Vec<u64> = bool_clauses
        .iter()
        .flat_map(|clause| clause.iter().map(|(variable, _)| *variable))
        .collect();
    mentioned.sort_unstable();
    mentioned.dedup();
    if mentioned != variable_ids {
        return Err(KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} Boolean binders do not match its clauses"
        )));
    }
    cursor += 1;
    require(&mut cursor, "  intro h")?;
    if lines.get(cursor).map(String::as_str) != Some("  bv_decide") {
        return Err(KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} has an unexpected Boolean closer"
        )));
    }
    cursor += 1;
    require(&mut cursor, "")?;

    let prop_header = lines.get(cursor).ok_or_else(|| {
        KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} is missing its Prop bridge"
        ))
    })?;
    let (prop_step, prop_formula) = parse_prop_header(prop_header).ok_or_else(|| {
        KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} has a mismatched Prop bridge"
        ))
    })?;
    if prop_step != step_id {
        return Err(KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} has a mismatched Prop bridge"
        )));
    }
    let prop_clauses = formula_signature(&prop_formula, false, job_id, step_id)?;
    if prop_clauses != bool_clauses {
        return Err(KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} Boolean and Prop clauses differ"
        )));
    }
    cursor += 1;
    require(&mut cursor, "  classical")?;
    let decides = variables
        .iter()
        .map(|variable| format!("(decide {variable})"))
        .collect::<Vec<_>>()
        .join(" ");
    let names = variables.join(" ");
    require(
        &mut cursor,
        &format!("  have satProof := inf_s{step_id}' {decides}"),
    )?;
    require(&mut cursor, &format!("  rewrite_decide_eq [{names} ]"))?;
    require(&mut cursor, "  sat_norm")?;
    require(&mut cursor, "  exact satProof")?;
    require(&mut cursor, "")?;

    let cnf_source = render_dimacs(&variable_ids, &bool_clauses);
    Ok(ParsedHelper {
        problem: KernelSatProblem {
            step_id,
            kind: marker.kind,
            variable_ids,
            clauses: bool_clauses,
            prop_formula,
            cnf_source,
        },
        marker_line: marker.line,
        end_line: cursor,
        validated: None,
    })
}

/// `theorem inf_sN' (sA2' sA3' : Bool) : <formula> := by`
fn parse_bool_header(line: &str) -> Option<(u64, Vec<String>, String)> {
    let rest = line.strip_prefix("theorem inf_s")?;
    let (step, rest) = split_number(rest)?;
    let rest = rest.strip_prefix("' (")?;
    let (binder, rest) = rest.split_once(" : Bool) : ")?;
    let formula = rest.strip_suffix(" := by")?;
    if formula.is_empty() {
        return None;
    }
    // The binder is primed (`sA2'`); the names carried on are the
    // unprimed `Prop` spellings the bridge applies, as in the legacy
    // Python's `removesuffix("'")`.
    let mut variables: Vec<String> = Vec::new();
    for primed in binder.split(' ') {
        let digits = primed
            .strip_prefix("sA")
            .and_then(|rest| rest.strip_suffix('\''))
            .filter(|digits| is_digits(digits))?;
        variables.push(format!("sA{digits}"));
    }
    if variables.is_empty() {
        return None;
    }
    Some((step, variables, formula.to_string()))
}

/// `theorem inf_sN : <formula> := by`
fn parse_prop_header(line: &str) -> Option<(u64, String)> {
    let rest = line.strip_prefix("theorem inf_s")?;
    let (step, rest) = split_number(rest)?;
    let rest = rest.strip_prefix(" : ")?;
    let formula = rest.strip_suffix(" := by")?;
    if formula.is_empty() {
        return None;
    }
    Some((step, formula.to_string()))
}

/// Parse the exact SAT-clause fragment the pinned emitter prints: a chain
/// of parenthesized clauses implying `False`.
fn formula_signature(
    formula: &str,
    boolean: bool,
    job_id: &str,
    step_id: u64,
) -> Result<Vec<Vec<(u64, bool)>>, KernelSatError> {
    let parts: Vec<&str> = formula.split(" → ").collect();
    if parts.len() < 2 || parts[parts.len() - 1] != "False" {
        return Err(KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} does not end in False"
        )));
    }
    let mut clauses = Vec::with_capacity(parts.len() - 1);
    for clause in &parts[..parts.len() - 1] {
        let body = clause
            .strip_prefix('(')
            .and_then(|rest| rest.strip_suffix(')'))
            .filter(|body| !body.is_empty())
            .ok_or_else(|| {
                KernelSatError::Shape(format!(
                    "{job_id} AVATAR step {step_id} has a malformed clause"
                ))
            })?;
        let separator = if boolean { " || " } else { " ∨ " };
        let mut literals: Vec<(u64, bool)> = Vec::new();
        for literal in body.split(separator) {
            let parsed = if boolean {
                parse_bool_literal(literal)
            } else {
                parse_prop_literal(literal)
            };
            literals.push(parsed.ok_or_else(|| {
                KernelSatError::Shape(format!(
                    "{job_id} AVATAR step {step_id} has a malformed literal"
                ))
            })?);
        }
        let ids: Vec<u64> = literals.iter().map(|(variable, _)| *variable).collect();
        if !strictly_increasing(&ids) {
            return Err(KernelSatError::Shape(format!(
                "{job_id} AVATAR step {step_id} has noncanonical literal order or duplicates"
            )));
        }
        clauses.push(literals);
    }
    Ok(clauses)
}

/// `sA12'` or `!sA12'`
fn parse_bool_literal(literal: &str) -> Option<(u64, bool)> {
    let (positive, rest) = match literal.strip_prefix('!') {
        Some(rest) => (false, rest),
        None => (true, literal),
    };
    let digits = rest.strip_prefix("sA")?.strip_suffix('\'')?;
    Some((parse_number(digits)?, positive))
}

/// `sA12` or `(¬sA12)`
fn parse_prop_literal(literal: &str) -> Option<(u64, bool)> {
    if let Some(rest) = literal.strip_prefix("(¬sA") {
        return Some((parse_number(rest.strip_suffix(')')?)?, false));
    }
    Some((parse_number(literal.strip_prefix("sA")?)?, true))
}

fn render_dimacs(variable_ids: &[u64], clauses: &[Vec<(u64, bool)>]) -> String {
    let mut rendered = format!("p cnf {} {}\n", variable_ids.len(), clauses.len());
    for clause in clauses {
        for (variable, positive) in clause {
            let dense = variable_ids
                .iter()
                .position(|candidate| candidate == variable)
                .expect("clause literal is one of the helper's own binders")
                + 1;
            if *positive {
                rendered.push_str(&dense.to_string());
            } else {
                rendered.push('-');
                rendered.push_str(&dense.to_string());
            }
            rendered.push(' ');
        }
        rendered.push_str("0\n");
    }
    rendered
}

// ------------------------------------------------------------
// LRAT Validation
// ------------------------------------------------------------

/// Accept one complete canonical RUP-only LRAT trace, fail closed.
///
/// The trace must be ASCII, newline-terminated, free of carriage returns,
/// and structurally exact: additions are numbered consecutively from the
/// last input clause, deletions carry the current step id, every hint names
/// a live earlier clause, and the trace ends with exactly one empty-clause
/// addition and nothing after it. A well-formed trace that uses RAT hints
/// is a [`KernelSatError::Unsupported`] miss, not an acceptance.
pub fn validate_lrat(
    problem: KernelSatProblem,
    lrat_source: &str,
    job_id: &str,
) -> Result<ValidatedKernelSat, KernelSatError> {
    let step_id = problem.step_id;
    let shape = |message: String| KernelSatError::Shape(message);
    if !lrat_source.is_ascii() {
        return Err(shape(format!(
            "{job_id} AVATAR step {step_id} LRAT is not ASCII"
        )));
    }
    if lrat_source.is_empty() || lrat_source.contains('\r') || !lrat_source.ends_with('\n') {
        return Err(shape(format!(
            "{job_id} AVATAR step {step_id} LRAT is not canonical text"
        )));
    }

    let clause_count = problem.clause_count() as u64;
    let variable_count = problem.variable_count() as u64;
    let mut live: Vec<u64> = (1..=clause_count).collect();
    let mut last_addition = clause_count;
    let mut additions = 0u64;
    let mut deletions = 0u64;
    let mut empty_additions = 0u64;
    let mut has_rat_hints = false;
    let source_lines: Vec<&str> = lrat_source
        .strip_suffix('\n')
        .unwrap_or(lrat_source)
        .split('\n')
        .collect();

    for (index, line) in source_lines.iter().enumerate() {
        let line_number = index + 1;
        let tokens: Vec<&str> = line.split(' ').collect();
        if line.is_empty()
            || tokens.iter().any(|token| token.is_empty())
            || !tokens.iter().all(|token| is_lrat_token(token))
        {
            return Err(shape(format!(
                "{job_id} AVATAR step {step_id} has malformed LRAT line {line_number}"
            )));
        }
        if !is_positive_number(tokens[0]) {
            return Err(shape(format!(
                "{job_id} AVATAR step {step_id} has an invalid LRAT step id on line {line_number}"
            )));
        }
        let step = parse_number(tokens[0]).ok_or_else(|| {
            shape(format!(
                "{job_id} AVATAR step {step_id} has an invalid LRAT step id on line {line_number}"
            ))
        })?;

        if tokens.len() >= 2 && tokens[1] == "d" {
            if step != last_addition
                || tokens.len() < 4
                || tokens[tokens.len() - 1] != "0"
                || tokens[2..tokens.len() - 1].contains(&"0")
            {
                return Err(shape(format!(
                    "{job_id} AVATAR step {step_id} has malformed LRAT deletion line {line_number}"
                )));
            }
            let mut deleted: Vec<i64> = Vec::new();
            for token in &tokens[2..tokens.len() - 1] {
                deleted.push(parse_signed(token).ok_or_else(|| {
                    shape(format!(
                        "{job_id} AVATAR step {step_id} has malformed LRAT deletion line \
                         {line_number}"
                    ))
                })?);
            }
            let mut unique = deleted.clone();
            unique.sort_unstable();
            unique.dedup();
            if deleted.iter().any(|clause| *clause <= 0)
                || unique.len() != deleted.len()
                || deleted
                    .iter()
                    .any(|clause| !live.contains(&(*clause as u64)))
            {
                return Err(shape(format!(
                    "{job_id} AVATAR step {step_id} deletes an invalid LRAT clause on line \
                     {line_number}"
                )));
            }
            live.retain(|clause| !deleted.contains(&(*clause as i64)));
            deletions += deleted.len() as u64;
            continue;
        }

        if step != last_addition + 1 {
            return Err(shape(format!(
                "{job_id} AVATAR step {step_id} has a nonsequential LRAT addition on line \
                 {line_number}"
            )));
        }
        let first_zero = tokens[1..]
            .iter()
            .position(|token| *token == "0")
            .map(|position| position + 1);
        let (first_zero, second_zero) = match first_zero {
            Some(first) => match tokens[first + 1..].iter().position(|token| *token == "0") {
                Some(second) => (first, first + 1 + second),
                None => {
                    return Err(shape(format!(
                        "{job_id} AVATAR step {step_id} has an unterminated LRAT addition on line \
                         {line_number}"
                    )));
                }
            },
            None => {
                return Err(shape(format!(
                    "{job_id} AVATAR step {step_id} has an unterminated LRAT addition on line \
                     {line_number}"
                )));
            }
        };
        if second_zero != tokens.len() - 1 {
            return Err(shape(format!(
                "{job_id} AVATAR step {step_id} has trailing LRAT tokens on line {line_number}"
            )));
        }
        let literal_tokens = &tokens[1..first_zero];
        let hint_tokens = &tokens[first_zero + 1..second_zero];
        if literal_tokens.contains(&"d") || hint_tokens.contains(&"d") {
            return Err(shape(format!(
                "{job_id} AVATAR step {step_id} has malformed LRAT tokens on line {line_number}"
            )));
        }
        let mut literals: Vec<i64> = Vec::with_capacity(literal_tokens.len());
        for token in literal_tokens {
            literals.push(parse_signed(token).ok_or_else(|| {
                shape(format!(
                    "{job_id} AVATAR step {step_id} has malformed LRAT tokens on line {line_number}"
                ))
            })?);
        }
        let mut hints: Vec<i64> = Vec::with_capacity(hint_tokens.len());
        for token in hint_tokens {
            hints.push(parse_signed(token).ok_or_else(|| {
                shape(format!(
                    "{job_id} AVATAR step {step_id} has malformed LRAT tokens on line {line_number}"
                ))
            })?);
        }
        let mut variables: Vec<u64> = literals
            .iter()
            .map(|literal| literal.unsigned_abs())
            .collect();
        variables.sort_unstable();
        variables.dedup();
        if literals
            .iter()
            .any(|literal| *literal == 0 || literal.unsigned_abs() > variable_count)
            || variables.len() != literals.len()
        {
            return Err(shape(format!(
                "{job_id} AVATAR step {step_id} has an invalid LRAT clause on line {line_number}"
            )));
        }
        if hints.is_empty() {
            return Err(shape(format!(
                "{job_id} AVATAR step {step_id} has an invalid RUP hint on line {line_number}"
            )));
        }
        let first_rat = hints
            .iter()
            .position(|hint| *hint < 0)
            .unwrap_or(hints.len());
        if hints[..first_rat]
            .iter()
            .any(|hint| *hint <= 0 || *hint >= step as i64 || !live.contains(&(*hint as u64)))
        {
            return Err(shape(format!(
                "{job_id} AVATAR step {step_id} has an invalid RUP hint on line {line_number}"
            )));
        }
        let rat_hints = &hints[first_rat..];
        if !rat_hints.is_empty() {
            if literals.is_empty() {
                return Err(shape(format!(
                    "{job_id} AVATAR step {step_id} has RAT hints on an empty clause on line \
                     {line_number}"
                )));
            }
            has_rat_hints = true;
            let mut cursor = 0usize;
            while cursor < rat_hints.len() {
                let resolution = rat_hints[cursor];
                if resolution >= 0
                    || -resolution >= step as i64
                    || !live.contains(&((-resolution) as u64))
                {
                    return Err(shape(format!(
                        "{job_id} AVATAR step {step_id} has an invalid RAT group on line \
                         {line_number}"
                    )));
                }
                cursor += 1;
                while cursor < rat_hints.len() && rat_hints[cursor] > 0 {
                    let hint = rat_hints[cursor];
                    if hint >= step as i64 || !live.contains(&(hint as u64)) {
                        return Err(shape(format!(
                            "{job_id} AVATAR step {step_id} has an invalid RAT hint on line \
                             {line_number}"
                        )));
                    }
                    cursor += 1;
                }
            }
        }
        if literals.is_empty() {
            empty_additions += 1;
            if line_number != source_lines.len() {
                return Err(shape(format!(
                    "{job_id} AVATAR step {step_id} has LRAT steps after the empty clause"
                )));
            }
        }
        live.push(step);
        last_addition = step;
        additions += 1;
    }

    if empty_additions != 1 {
        return Err(shape(format!(
            "{job_id} AVATAR step {step_id} LRAT does not end in exactly one empty-clause proof"
        )));
    }
    if has_rat_hints {
        return Err(KernelSatError::Unsupported(format!(
            "{job_id} AVATAR step {step_id} requires RAT hints"
        )));
    }
    Ok(ValidatedKernelSat {
        problem,
        lrat_source: lrat_source.to_string(),
        lrat_additions: additions,
        lrat_deletions: deletions,
        lrat_max_clause_id: last_addition,
    })
}

fn is_lrat_token(token: &str) -> bool {
    if token == "d" || token == "0" {
        return true;
    }
    let digits = token.strip_prefix('-').unwrap_or(token);
    is_digits(digits) && !digits.starts_with('0')
}

fn is_positive_number(token: &str) -> bool {
    is_digits(token) && !token.starts_with('0')
}

// ------------------------------------------------------------
// Rendering
// ------------------------------------------------------------

/// Which component of the LRAT theorem's falsification tuple refutes the
/// `index`-th literal of a clause of width `width`.
fn falsification_access(width: usize, index: usize) -> String {
    if width == 1 {
        return "hf".to_string();
    }
    if index == width - 1 {
        return format!("hf.{}2", "2.".repeat(width - 2));
    }
    format!("hf.{}1", "2.".repeat(index))
}

/// Eliminate one original disjunction against the LRAT falsification.
fn render_clause_refutation(clause: &[(u64, bool)], hypothesis: &str) -> String {
    fn visit(clause: &[(u64, bool)], index: usize, remaining: &str) -> String {
        let access = falsification_access(clause.len(), index);
        let branch = if clause[index].1 {
            access
        } else {
            format!("(fun hn => hn {access})")
        };
        if index == clause.len() - 1 {
            return format!("{branch} {remaining}");
        }
        format!(
            "Or.elim {remaining} {branch} (fun hr => {})",
            visit(clause, index + 1, "hr")
        )
    }
    visit(clause, 0, hypothesis)
}

fn render_balanced_clause_elimination(
    clauses: &[Vec<(u64, bool)>],
    start: usize,
    stop: usize,
) -> String {
    let length = stop - start;
    if length == 1 {
        return format!(
            "(fun hf => {})",
            render_clause_refutation(&clauses[start], &format!("h{}", start + 1))
        );
    }
    let midpoint = start + length / 2;
    format!(
        "(fun hs => Or.elim hs {} {})",
        render_balanced_clause_elimination(clauses, start, midpoint),
        render_balanced_clause_elimination(clauses, midpoint, stop)
    )
}

/// The exact replacement block for one AVATAR refutation.
pub fn render_lrat_helper(validated: &ValidatedKernelSat) -> Vec<String> {
    let problem = &validated.problem;
    let step_id = problem.step_id;
    let variables = problem
        .variable_ids
        .iter()
        .map(|variable| format!("sA{variable}"))
        .collect::<Vec<_>>()
        .join(" ");
    let hypotheses = (1..=problem.clause_count())
        .map(|index| format!("h{index}"))
        .collect::<Vec<_>>()
        .join(" ");
    let elimination =
        render_balanced_clause_elimination(&problem.clauses, 0, problem.clause_count());
    vec![
        format!(
            "-- step {step_id} avatar {} refutation via kernel-checked LRAT",
            problem.kind.name()
        ),
        format!("lrat_proof inf_s{step_id}_lrat"),
        format!("  {}", json_string(&problem.cnf_source)),
        format!("  {}", json_string(&validated.lrat_source)),
        String::new(),
        format!("theorem inf_s{step_id} : {} := by", problem.prop_formula),
        format!("  intro {hypotheses}"),
        format!("  have h := inf_s{step_id}_lrat {variables}"),
        format!("  exact {elimination} h"),
        String::new(),
    ]
}

/// A standalone module declaring every rewritten helper in isolation, with
/// `#print axioms` of both its declarations.
///
/// The certificate build does **not** compile this. The gate on whether a
/// helper smuggled an axiom into the certificate is the build's own
/// exact-std3 audit of `Check.lean`, taken over the axiom closure of the
/// published theorem and therefore covering every helper the proof
/// actually depends on; a second compile per helper would re-ask a
/// question that audit has already answered, at the cost of one Mathlib
/// LRAT-checker import each. The rendering is kept, and its digest is
/// recorded in the receipt, so the isolated module of any given build can
/// be reproduced by hand when one helper needs to be studied alone.
pub fn render_kernel_sat_probe(helpers: &[ValidatedKernelSat]) -> String {
    let mut lines: Vec<String> = vec![
        format!("import {FROM_LRAT_IMPORT}"),
        String::new(),
        "set_option linter.style.setOption false".to_string(),
        "set_option maxHeartbeats 400000000".to_string(),
        "set_option maxRecDepth 1048576".to_string(),
        String::new(),
    ];
    for validated in helpers {
        let step_id = validated.problem.step_id;
        let variables = validated
            .problem
            .variable_ids
            .iter()
            .map(|variable| format!("sA{variable}"))
            .collect::<Vec<_>>()
            .join(" ");
        lines.push(format!("namespace KernelSatStep{step_id}"));
        lines.push(format!("variable ({variables} : Prop)"));
        lines.push(String::new());
        lines.extend(render_lrat_helper(validated));
        lines.push(format!("#print axioms inf_s{step_id}_lrat"));
        lines.push(format!("#print axioms inf_s{step_id}"));
        lines.push(String::new());
        lines.push(format!("end KernelSatStep{step_id}"));
        lines.push(String::new());
    }
    format!("{}\n", lines.join("\n").trim())
}

/// JSON string literal, matching Python's `json.dumps` on ASCII text; the
/// embedded DIMACS and LRAT are ASCII with newlines and nothing else that
/// needs escaping.
fn json_string(value: &str) -> String {
    let mut rendered = String::with_capacity(value.len() + 2);
    rendered.push('"');
    for character in value.chars() {
        match character {
            '"' => rendered.push_str("\\\""),
            '\\' => rendered.push_str("\\\\"),
            '\n' => rendered.push_str("\\n"),
            '\r' => rendered.push_str("\\r"),
            '\t' => rendered.push_str("\\t"),
            control if (control as u32) < 0x20 => {
                rendered.push_str(&format!("\\u{:04x}", control as u32));
            }
            other => rendered.push(other),
        }
    }
    rendered.push('"');
    rendered
}

fn parse_json_string(literal: &str) -> Option<String> {
    let body = literal.strip_prefix('"')?.strip_suffix('"')?;
    let mut decoded = String::with_capacity(body.len());
    let mut characters = body.chars();
    while let Some(character) = characters.next() {
        match character {
            '"' => return None,
            '\\' => match characters.next()? {
                '"' => decoded.push('"'),
                '\\' => decoded.push('\\'),
                '/' => decoded.push('/'),
                'b' => decoded.push('\u{8}'),
                'f' => decoded.push('\u{c}'),
                'n' => decoded.push('\n'),
                'r' => decoded.push('\r'),
                't' => decoded.push('\t'),
                'u' => {
                    let mut digits = String::new();
                    for _ in 0..4 {
                        digits.push(characters.next()?);
                    }
                    let code = u32::from_str_radix(&digits, 16).ok()?;
                    decoded.push(char::from_u32(code)?);
                }
                _ => return None,
            },
            other => decoded.push(other),
        }
    }
    Some(decoded)
}

// ------------------------------------------------------------
// Idempotence: Reading An Already Rewritten Block
// ------------------------------------------------------------

/// Parse and byte-validate one already embedded LRAT helper.
///
/// The block must re-render byte-identically from its own embedded CNF and
/// LRAT — an altered proof term, a CNF that disagrees with the `Prop`
/// bridge, or a trace that no longer validates is a fail-closed shape
/// error, not a silent re-solve.
fn parse_embedded_lrat_helper(
    lines: &[String],
    marker: &AvatarMarker,
    job_id: &str,
) -> Result<ParsedHelper, KernelSatError> {
    let step_id = marker.step_id;
    if marker.line + 10 > lines.len() {
        return Err(KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} embedded LRAT is truncated"
        )));
    }
    if lines[marker.line + 1] != format!("lrat_proof inf_s{step_id}_lrat") {
        return Err(KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} has a mismatched LRAT theorem"
        )));
    }
    let mut decoded: Vec<String> = Vec::with_capacity(2);
    for (offset, label) in [(2usize, "CNF"), (3usize, "LRAT")] {
        let line = &lines[marker.line + offset];
        let malformed = || {
            KernelSatError::Shape(format!(
                "{job_id} AVATAR step {step_id} has malformed embedded {label}"
            ))
        };
        let literal = line.strip_prefix("  ").ok_or_else(malformed)?;
        let value = parse_json_string(literal).ok_or_else(malformed)?;
        if *line != format!("  {}", json_string(&value)) {
            return Err(KernelSatError::Shape(format!(
                "{job_id} AVATAR step {step_id} has noncanonical embedded {label}"
            )));
        }
        decoded.push(value);
    }
    if !lines[marker.line + 4].is_empty() {
        return Err(KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} has malformed LRAT spacing"
        )));
    }
    let (prop_step, prop_formula) =
        parse_prop_header(&lines[marker.line + 5]).ok_or_else(|| {
            KernelSatError::Shape(format!(
                "{job_id} AVATAR step {step_id} has a mismatched Prop bridge"
            ))
        })?;
    if prop_step != step_id {
        return Err(KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} has a mismatched Prop bridge"
        )));
    }
    let clauses = formula_signature(&prop_formula, false, job_id, step_id)?;
    let mut variable_ids: Vec<u64> = clauses
        .iter()
        .flat_map(|clause| clause.iter().map(|(variable, _)| *variable))
        .collect();
    variable_ids.sort_unstable();
    variable_ids.dedup();
    let cnf_source = render_dimacs(&variable_ids, &clauses);
    if decoded[0] != cnf_source {
        return Err(KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} embedded CNF differs from its Prop bridge"
        )));
    }
    let validated = validate_lrat(
        KernelSatProblem {
            step_id,
            kind: marker.kind,
            variable_ids,
            clauses,
            prop_formula,
            cnf_source,
        },
        &decoded[1],
        job_id,
    )?;
    let expected = render_lrat_helper(&validated);
    let end_line = marker.line + expected.len();
    if end_line > lines.len() || lines[marker.line..end_line] != expected[..] {
        return Err(KernelSatError::Shape(format!(
            "{job_id} AVATAR step {step_id} embedded LRAT bridge was altered"
        )));
    }
    Ok(ParsedHelper {
        problem: validated.problem.clone(),
        marker_line: marker.line,
        end_line,
        validated: Some(validated),
    })
}

// ------------------------------------------------------------
// Name Qualification (Transformation 6)
// ------------------------------------------------------------

/// Qualify the four executable VampLean names that Mathlib's LRAT checker
/// shadows once `Mathlib.Tactic.Sat.FromLRAT` is imported.
///
/// Comments, strings and already-qualified names stay byte-identical. The
/// pinned emitter never quotes or redeclares these names, so a quoted or
/// redeclared spelling fails closed rather than being interpreted.
pub fn qualify_lrat_collisions(source: &str, job_id: &str) -> Result<String, KernelSatError> {
    let characters: Vec<char> = source.chars().collect();
    let code = mask_comments_and_strings(&characters, job_id)?;
    let mut replacements: Vec<(usize, usize)> = Vec::new();
    for name in VAMPLEAN_LRAT_COLLISIONS {
        let quoted: Vec<char> = format!("«{name}»").chars().collect();
        if find_all(&code, &quoted).next().is_some() {
            return Err(KernelSatError::Shape(format!(
                "{job_id} quotes LRAT/VampLean collision {name}"
            )));
        }
        if declares_name(&code, name) {
            return Err(KernelSatError::Shape(format!(
                "{job_id} redeclares LRAT/VampLean collision {name}"
            )));
        }
        let needle: Vec<char> = name.chars().collect();
        for start in find_all(&code, &needle) {
            let end = start + needle.len();
            let before = start.checked_sub(1).map(|index| code[index]);
            let after = code.get(end).copied();
            if before.is_some_and(is_qualification_boundary_before)
                || after.is_some_and(is_qualification_boundary_after)
            {
                continue;
            }
            replacements.push((start, end));
        }
    }
    replacements.sort_unstable();
    if replacements.windows(2).any(|pair| pair[0].1 > pair[1].0) {
        return Err(KernelSatError::Shape(format!(
            "{job_id} has overlapping LRAT/VampLean collision tokens"
        )));
    }
    let mut rewritten = String::with_capacity(source.len());
    let mut cursor = 0usize;
    for (start, end) in &replacements {
        rewritten.extend(&characters[cursor..*start]);
        rewritten.push_str("VampLean.");
        rewritten.extend(&characters[*start..*end]);
        cursor = *end;
    }
    rewritten.extend(&characters[cursor..]);

    let rewritten_characters: Vec<char> = rewritten.chars().collect();
    let rewritten_code = mask_comments_and_strings(&rewritten_characters, job_id)?;
    let prefix: Vec<char> = "VampLean.".chars().collect();
    for name in VAMPLEAN_LRAT_COLLISIONS {
        let needle: Vec<char> = name.chars().collect();
        for start in find_all(&rewritten_code, &needle) {
            let end = start + needle.len();
            let before = start.checked_sub(1).map(|index| rewritten_code[index]);
            let after = rewritten_code.get(end).copied();
            // Unlike the replacement scan above, a `.` before the name does
            // not make this occurrence somebody else's: every surviving
            // occurrence must be qualified by `VampLean.` and nothing else.
            if before.is_some_and(is_qualification_boundary_after)
                || after.is_some_and(is_qualification_boundary_after)
            {
                continue;
            }
            let qualified = start >= prefix.len()
                && rewritten_code[start - prefix.len()..start] == prefix[..]
                && (start == prefix.len()
                    || !is_qualification_boundary_before(rewritten_code[start - prefix.len() - 1]));
            if !qualified {
                return Err(KernelSatError::Shape(format!(
                    "{job_id} retained externally qualified LRAT/VampLean collision {name}"
                )));
            }
        }
    }
    Ok(rewritten)
}

/// A character that, immediately before an occurrence, means it is part of
/// a longer or already-qualified name.
fn is_qualification_boundary_before(character: char) -> bool {
    is_word_character(character) || matches!(character, '.' | '\'' | '«' | '»')
}

/// A character that, immediately after an occurrence, means it is part of
/// a longer name.
fn is_qualification_boundary_after(character: char) -> bool {
    is_word_character(character) || matches!(character, '\'' | '«' | '»')
}

fn declares_name(code: &[char], name: &str) -> bool {
    let needle: Vec<char> = name.chars().collect();
    for (start, end) in line_spans(code) {
        let line = &code[start..end];
        let mut cursor = 0usize;
        while cursor < line.len() && line[cursor].is_whitespace() {
            cursor += 1;
        }
        for keyword in ["abbrev", "def", "lemma", "theorem"] {
            let keyword: Vec<char> = keyword.chars().collect();
            if line.len() < cursor + keyword.len()
                || line[cursor..cursor + keyword.len()] != keyword[..]
            {
                continue;
            }
            let mut after = cursor + keyword.len();
            let whitespace_start = after;
            while after < line.len() && line[after].is_whitespace() {
                after += 1;
            }
            if after == whitespace_start {
                continue;
            }
            if line.len() >= after + needle.len()
                && line[after..after + needle.len()] == needle[..]
                && !line
                    .get(after + needle.len())
                    .copied()
                    .is_some_and(|next| is_word_character(next) || next == '\'')
            {
                return true;
            }
        }
    }
    false
}

// ------------------------------------------------------------
// Post-Rewrite Verification
// ------------------------------------------------------------

/// Refuse to hand on any text that still carries native trust, an unpaired
/// helper, or an externally supplied LRAT.
fn verify_rewritten(
    text: &str,
    helpers: &[ValidatedKernelSat],
    job_id: &str,
) -> Result<(), KernelSatError> {
    let characters: Vec<char> = text.chars().collect();
    let code = mask_comments_and_strings(&characters, job_id)?;
    for closer in ["bv_decide", "native_decide"] {
        if find_word(&code, closer).is_some() {
            return Err(KernelSatError::Shape(format!(
                "{job_id} has executable {closer} outside a pinned AVATAR helper"
            )));
        }
    }
    if find_word(&code, "include_str").is_some() {
        return Err(KernelSatError::Shape(format!(
            "{job_id} has an unpaired or external AVATAR LRAT helper"
        )));
    }
    let mut lrat_commands = 0usize;
    let mut lrat_steps: Vec<u64> = Vec::new();
    let mut primed: Vec<u64> = Vec::new();
    for (start, end) in line_spans(&code) {
        let line: String = code[start..end].iter().collect();
        let body = line.trim_start();
        if body.trim_end().starts_with("lrat_proof")
            && body
                .trim_end()
                .strip_prefix("lrat_proof")
                .is_some_and(|rest| rest.is_empty() || rest.starts_with(char::is_whitespace))
        {
            lrat_commands += 1;
            if let Some(step) = body
                .trim_end()
                .strip_prefix("lrat_proof")
                .map(str::trim_start)
                .and_then(|rest| rest.strip_prefix("inf_s"))
                .and_then(|rest| rest.strip_suffix("_lrat"))
                .and_then(parse_number)
            {
                lrat_steps.push(step);
            }
        }
        if let Some(step) = parse_primed_theorem_line(body) {
            primed.push(step);
        }
    }
    let expected: Vec<u64> = helpers
        .iter()
        .map(|helper| helper.problem.step_id)
        .collect();
    if !primed.is_empty() {
        return Err(KernelSatError::Shape(format!(
            "{job_id} has an unpaired AVATAR Boolean helper"
        )));
    }
    if lrat_steps != expected || lrat_commands != expected.len() {
        return Err(KernelSatError::Shape(format!(
            "{job_id} has an unpaired or external AVATAR LRAT helper"
        )));
    }
    for helper in helpers {
        let step_id = helper.problem.step_id;
        let occurrences = count_word(&code, &format!("inf_s{step_id}_lrat"));
        if occurrences != 2 {
            return Err(KernelSatError::Shape(format!(
                "{job_id} has a colliding or external AVATAR LRAT theorem inf_s{step_id}_lrat"
            )));
        }
        if count_primed_reference(&code, step_id) != 0 {
            return Err(KernelSatError::Shape(format!(
                "{job_id} has an external reference to AVATAR Boolean helper inf_s{step_id}'"
            )));
        }
    }
    Ok(())
}

// ------------------------------------------------------------
// Lean Lexical Helpers
// ------------------------------------------------------------

/// Blank every Lean comment and string literal, preserving code-point
/// count and line structure, so token scans never see a comment or a
/// string. Port of `_lean_code_without_comments_or_strings`.
fn mask_comments_and_strings(source: &[char], job_id: &str) -> Result<Vec<char>, KernelSatError> {
    let mut output: Vec<char> = Vec::with_capacity(source.len());
    let mut index = 0usize;
    let mut block_depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    while index < source.len() {
        let character = source[index];
        let next = source.get(index + 1).copied();
        let opens_block = character == '/' && next == Some('-');
        let closes_block = character == '-' && next == Some('/');
        if block_depth > 0 {
            if opens_block {
                block_depth += 1;
                output.extend([' ', ' ']);
                index += 2;
            } else if closes_block {
                block_depth -= 1;
                output.extend([' ', ' ']);
                index += 2;
            } else {
                output.push(if character == '\n' { '\n' } else { ' ' });
                index += 1;
            }
            continue;
        }
        if in_string {
            output.push(if character == '\n' { '\n' } else { ' ' });
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '"' {
                in_string = false;
            }
            index += 1;
            continue;
        }
        if character == '-' && next == Some('-') {
            let newline = source[index..].iter().position(|value| *value == '\n');
            match newline {
                Some(offset) => {
                    output.extend(std::iter::repeat_n(' ', offset));
                    index += offset;
                }
                None => {
                    output.extend(std::iter::repeat_n(' ', source.len() - index));
                    break;
                }
            }
            continue;
        }
        if opens_block {
            block_depth = 1;
            output.extend([' ', ' ']);
            index += 2;
            continue;
        }
        if character == '"' {
            in_string = true;
            output.push(' ');
        } else {
            output.push(character);
        }
        index += 1;
    }
    if block_depth > 0 || in_string {
        return Err(KernelSatError::Shape(format!(
            "{job_id} raw leancheck source has an unterminated comment or string"
        )));
    }
    Ok(output)
}

/// Zero-based lines whose Lean line comment starts in code position. Port
/// of `_lean_line_comment_lines`.
fn line_comment_lines(source: &[char]) -> Vec<usize> {
    let mut lines: Vec<usize> = Vec::new();
    let mut index = 0usize;
    let mut line = 0usize;
    let mut block_depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    while index < source.len() {
        let character = source[index];
        let next = source.get(index + 1).copied();
        let opens_block = character == '/' && next == Some('-');
        let closes_block = character == '-' && next == Some('/');
        if block_depth > 0 {
            if opens_block {
                block_depth += 1;
                index += 2;
            } else if closes_block {
                block_depth -= 1;
                index += 2;
            } else {
                if character == '\n' {
                    line += 1;
                }
                index += 1;
            }
            continue;
        }
        if in_string {
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '"' {
                in_string = false;
            }
            if character == '\n' {
                line += 1;
            }
            index += 1;
            continue;
        }
        if character == '-' && next == Some('-') {
            lines.push(line);
            match source[index..].iter().position(|value| *value == '\n') {
                Some(offset) => {
                    line += 1;
                    index += offset + 1;
                }
                None => break,
            }
            continue;
        }
        if opens_block {
            block_depth = 1;
            index += 2;
            continue;
        }
        if character == '"' {
            in_string = true;
        } else if character == '\n' {
            line += 1;
        }
        index += 1;
    }
    lines.sort_unstable();
    lines.dedup();
    lines
}

fn line_spans(code: &[char]) -> Vec<(usize, usize)> {
    let mut spans = Vec::new();
    let mut start = 0usize;
    for (index, character) in code.iter().enumerate() {
        if *character == '\n' {
            spans.push((start, index));
            start = index + 1;
        }
    }
    spans.push((start, code.len()));
    spans
}

fn is_word_character(character: char) -> bool {
    character.is_alphanumeric() || character == '_'
}

fn find_all<'a>(haystack: &'a [char], needle: &'a [char]) -> impl Iterator<Item = usize> + 'a {
    (0..haystack
        .len()
        .saturating_sub(needle.len().saturating_sub(1)))
        .filter(move |start| {
            !needle.is_empty() && haystack[*start..*start + needle.len()] == *needle
        })
}

/// Whole-word occurrence, with Python's `\b` semantics.
fn find_word(code: &[char], word: &str) -> Option<usize> {
    word_occurrences(code, word).next()
}

fn count_word(code: &[char], word: &str) -> usize {
    word_occurrences(code, word).count()
}

fn word_occurrences<'a>(code: &'a [char], word: &'a str) -> impl Iterator<Item = usize> + 'a {
    let needle: Vec<char> = word.chars().collect();
    let length = needle.len();
    find_all_owned(code, needle).filter(move |start| {
        let before = start.checked_sub(1).map(|index| code[index]);
        let after = code.get(start + length).copied();
        !before.is_some_and(is_word_character) && !after.is_some_and(is_word_character)
    })
}

fn find_all_owned(haystack: &[char], needle: Vec<char>) -> impl Iterator<Item = usize> + '_ {
    (0..haystack
        .len()
        .saturating_sub(needle.len().saturating_sub(1)))
        .filter(move |start| {
            !needle.is_empty() && haystack[*start..*start + needle.len()] == needle[..]
        })
}

/// `theorem inf_s<step>'` followed by whitespace or `(`, the legacy scan
/// for a surviving Boolean helper declaration. `body` is one code line
/// with its leading whitespace already removed.
fn parse_primed_theorem_line(body: &str) -> Option<u64> {
    let rest = body.strip_prefix("theorem")?;
    let name = rest.trim_start();
    if rest.len() == name.len() {
        return None;
    }
    let digits = name.strip_prefix("inf_s")?;
    let position = digits.find('\'')?;
    let step = parse_number(&digits[..position])?;
    let follows = digits[position + 1..].chars().next();
    if follows.is_some_and(|next| !next.is_whitespace() && next != '(') {
        return None;
    }
    Some(step)
}

/// `\binf_s<step>'(?=\s|\()`, the legacy scan for a Boolean helper still
/// referenced somewhere.
fn count_primed_reference(code: &[char], step_id: u64) -> usize {
    let needle: Vec<char> = format!("inf_s{step_id}'").chars().collect();
    let length = needle.len();
    find_all_owned(code, needle.clone())
        .filter(|start| {
            let before = start.checked_sub(1).map(|index| code[index]);
            let after = code.get(start + length).copied();
            !before.is_some_and(is_word_character)
                && after.is_some_and(|next| next.is_whitespace() || next == '(')
        })
        .count()
}

fn is_digits(text: &str) -> bool {
    !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit())
}

fn parse_number(text: &str) -> Option<u64> {
    if !is_digits(text) {
        return None;
    }
    text.parse().ok()
}

fn parse_signed(text: &str) -> Option<i64> {
    if text == "0" {
        return Some(0);
    }
    let digits = text.strip_prefix('-').unwrap_or(text);
    if !is_digits(digits) || digits.starts_with('0') {
        return None;
    }
    text.parse().ok()
}

/// Split a leading run of digits from `text`.
fn split_number(text: &str) -> Option<(u64, &str)> {
    let end = text
        .find(|character: char| !character.is_ascii_digit())
        .unwrap_or(text.len());
    if end == 0 {
        return None;
    }
    Some((text[..end].parse().ok()?, &text[end..]))
}

fn strictly_increasing(values: &[u64]) -> bool {
    values.windows(2).all(|pair| pair[0] < pair[1])
}

#[cfg(test)]
pub(crate) mod tests;
