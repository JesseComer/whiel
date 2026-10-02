//! Live durable fixed-ambient certificate-build coverage.
//!
//! Every test binds the checked-in `Example0001` fixture through the Lean
//! `fixed_ambient_encoding_worker` executable (see `framework2_fixed_ambient.rs`
//! for the same pattern), stabilizes the real two-clause invariant already
//! checked in at `Benchmark/Example0001/Certificate` with a fake, fast
//! Vampire, and then exercises [`build_certificate`] against that frozen
//! Core with the real pinned leancheck Vampire or a scripted stand-in.

mod support;

use std::collections::BTreeMap;
use std::fs;
use std::num::NonZeroUsize;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use serde_json::{Value, json};

use whiel_runner::encoding::{FixedAmbientWorkerCommand, FixedAmbientWorkerPoolConfig};
use whiel_runner::framework2::{
    AggregateCertificationError, CERTIFICATE_RESOURCE_POLICY, CertificateBuildError,
    CertificateBuildHooks, CertificateBuildRequest, CertificateBundleShape, CertificateJob,
    CertificateJobReceipt, CertificateModuleHook, CertificateRevalidationRequest,
    CertifyFrozenCoreRequest, CoreFreezeError, DEFAULT_CERTIFICATION_CONCURRENCY,
    FrozenLeveledCore, LeancheckProfile, PinnedLeancheckVampire, ProofTransformId,
    ProofTransformOutcome, PublicationError, PublishValidRequest, SearchProfileProvenance,
    VOLATILE_LINE_PREFIXES, build_certificate, certify_frozen_core, normalize_telescope_order,
    publish_valid, revalidate_certificate_tree,
};
use whiel_runner::{
    AgentToolPolicy, ArtifactStoreConfig, BoundFixedAmbientFrameworkII, CancellationToken,
    CascPortfolioPolicy, ClauseId, ExtendedClauseOrigin, FmbOptions,
    FrameworkIICertificationProfiles, FrameworkIICheckRole, FrameworkIIEpochOutcome,
    FrameworkIILevel, FrameworkIIProductionCheckConfig, FrameworkIIProductionChecker,
    FrameworkIIProposalEpoch, FrameworkIISolverContext, HostLimits, LeancheckCertificationProfile,
    LeveledCandidateSnapshot, LeveledHoudiniState, LeveledStabilizationOutcome, ProofCascShare,
    ProofSearchProfile, RuntimeResourcePolicy, SolverAdmission, SolverInvocationIdentity,
    VampireSearchBudget, VampireWorkerCommand, bind_fixed_ambient_framework_ii,
    create_general_solver_admission, new_artifact_store, run_framework_ii_proposal_epoch,
    stabilize_leveled_houdini, stabilize_leveled_houdini_with_system_clauses,
};

// ------------------------------------------------------------
// Fixture Sources (the real Example0001 invariant)
// ------------------------------------------------------------

const LEVEL_ZERO_CLAUSE: &str = "(op_zS = (op_zE ∪ π[0,3] (σ[#1 = #2] ((op_zE × op_zT)))))";
const LEVEL_ONE_CLAUSE: &str = "(π[0,3] (σ[#1 = #2] ((op_zT × yp_zT))) ⊆ yp_zT)";
const JOB_IDS: [&str; 5] = [
    "init_clause_0",
    "init_clause_1",
    "maint_clause_0",
    "maint_clause_1",
    "term_check",
];

static FIXED_AMBIENT_WORKER: OnceLock<PathBuf> = OnceLock::new();
static FIXTURE_DESCRIPTOR: OnceLock<Value> = OnceLock::new();

fn fixed_ambient_worker() -> &'static Path {
    FIXED_AMBIENT_WORKER
        .get_or_init(|| {
            let repository = support::repository_root();
            let build = Command::new("lake")
                .args(["build", "fixed_ambient_encoding_worker"])
                .current_dir(&repository)
                .output()
                .expect("build fixed-ambient encoding worker");
            assert!(
                build.status.success(),
                "Lean fixed-ambient worker build failed\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&build.stdout),
                String::from_utf8_lossy(&build.stderr)
            );
            repository.join(".lake/build/bin/fixed_ambient_encoding_worker")
        })
        .as_path()
}

fn fixture_descriptor() -> Value {
    FIXTURE_DESCRIPTOR
        .get_or_init(|| {
            let output = Command::new(fixed_ambient_worker())
                .arg("manifest")
                .current_dir(support::repository_root())
                .output()
                .expect("run the fixed-ambient fixture manifest");
            assert!(
                output.status.success(),
                "fixture manifest failed: {}",
                String::from_utf8_lossy(&output.stderr)
            );
            serde_json::from_slice(&output.stdout).expect("fixture manifest emits one JSON value")
        })
        .clone()
}

fn worker_pool(workers: usize) -> FixedAmbientWorkerPoolConfig {
    FixedAmbientWorkerPoolConfig::new(
        FixedAmbientWorkerCommand::new(fixed_ambient_worker(), support::repository_root()),
        workers,
    )
    .expect("positive worker count")
}

fn agent_admission(vampire_processes: usize, workers: usize) -> SolverAdmission {
    create_general_solver_admission(
        RuntimeResourcePolicy::agent_only(vampire_processes, workers).unwrap(),
    )
    .unwrap()
}

async fn bind(
    pool: FixedAmbientWorkerPoolConfig,
    catalog_digit: char,
    max_level: Option<FrameworkIILevel>,
    admission: &SolverAdmission,
    cancellation: &CancellationToken,
) -> BoundFixedAmbientFrameworkII {
    let bound = bind_fixed_ambient_framework_ii(
        fixture_descriptor(),
        pool,
        catalog_digit.to_string().repeat(64),
        // The run's host limits are its single source; this suite declares
        // only the level bound it wants and leaves every other limit unset.
        HostLimits {
            level_bound: max_level.map(FrameworkIILevel::get),
            ..HostLimits::UNBOUNDED
        },
        false,
        AgentToolPolicy::default(),
        admission,
        cancellation,
    )
    .await
    .expect("bind the checked-in fixed-ambient fixture");
    assert_eq!(bound.task().identity().canonical_id(), "Example0001");
    // Pass 7.5d: every live suite runs the differential safety net, so a
    // controller-assembled problem that differs from the worker's own
    // `prepare_exact_obligation` output fails the run.
    bound.solver().set_assembly_differential(true);
    bound
}

async fn admit(
    admission: &whiel_runner::FrameworkIIAdmissionContext,
    sources: &[&str],
    solver_admission: &SolverAdmission,
    cancellation: &CancellationToken,
) -> Vec<whiel_runner::ExtendedClause> {
    let sources = sources
        .iter()
        .map(|source| (*source).to_owned())
        .collect::<Vec<_>>();
    admission
        .admit_clauses(&sources, None, solver_admission, cancellation)
        .await
        .expect("live admission is not cancelled")
        .accepted()
        .expect("Example0001's own checked-in clauses are accepted")
        .to_vec()
}

fn register_and_enqueue(
    houdini: &mut LeveledHoudiniState,
    clauses: &[whiel_runner::ExtendedClause],
) -> Vec<ClauseId> {
    let registered = houdini
        .catalog()
        .register_batch(
            0,
            clauses
                .iter()
                .cloned()
                .map(|clause| (clause, ExtendedClauseOrigin::Submitted)),
        )
        .unwrap();
    houdini.enqueue_registered(&registered).unwrap();
    registered.ids().to_vec()
}

fn certification_profiles() -> FrameworkIICertificationProfiles {
    let invocation = |profile: &str| {
        SolverInvocationIdentity::from_parts(
            Arc::from("vampire"),
            Arc::from("fixture-leancheck"),
            Arc::from("/fixture/pinned-vampire"),
            Arc::from("a".repeat(64)),
            Arc::from(std::env::consts::OS),
            Arc::from(std::env::consts::ARCH),
            vec![Arc::from(profile)],
        )
        .unwrap()
    };
    let profile = |kind, name: &str| {
        LeancheckCertificationProfile::new(
            kind,
            format!("fixture-{name}-v1"),
            invocation(name),
            None,
            "b".repeat(64),
            "c".repeat(64),
            "d".repeat(64),
            "e".repeat(64),
            "f".repeat(64),
        )
        .unwrap()
    };
    FrameworkIICertificationProfiles::new(
        profile(ProofSearchProfile::Direct, "direct"),
        profile(ProofSearchProfile::Casc2025, "casc-2025"),
    )
    .unwrap()
}

/// Stabilize the real Example0001 invariant (levels 0 and 1) with a fast,
/// content-agnostic fake Vampire and hand back a bound solver context, its
/// admission, and the frozen Core snapshot. The worker pool and solver
/// context stay alive; the caller must `solver.shutdown()` when finished.
/// As [`fixed_core_snapshot`], but also hands back the stabilized
/// [`LeveledHoudiniState`] itself, which the plain wrapper below drops.
async fn fixed_core_snapshot_with_state(
    directory: &support::TestDir,
    catalog_digit: char,
) -> (
    FrameworkIISolverContext,
    SolverAdmission,
    Arc<LeveledCandidateSnapshot>,
    LeveledHoudiniState,
) {
    let solver_admission = agent_admission(2, 1);
    let cancellation = CancellationToken::new();
    let bound = bind(
        worker_pool(1),
        catalog_digit,
        Some(FrameworkIILevel::ONE),
        &solver_admission,
        &cancellation,
    )
    .await;
    let (task, admission, solver, mut houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();

    let clauses = admit(
        &admission,
        &[LEVEL_ZERO_CLAUSE, LEVEL_ONE_CLAUSE],
        &solver_admission,
        &cancellation,
    )
    .await;
    assert_eq!(clauses.len(), 2);
    register_and_enqueue(&mut houdini, &clauses);

    let command = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args(["--fixture", "race-proof-fast"])
        .unwrap();
    let config = FrameworkIIProductionCheckConfig::new(
        artifacts.clone(),
        solver_admission.clone(),
        VampireSearchBudget::finite(Duration::from_secs(5)),
        FmbOptions::default(),
        command,
        cancellation.clone(),
        "fixture-vampire",
        certification_profiles(),
    )
    .unwrap();
    let mut checker = solver.clone().production_checker(config);
    let outcome = stabilize_leveled_houdini_with_system_clauses(&mut houdini, &mut checker)
        .await
        .unwrap();
    let LeveledStabilizationOutcome::Stabilized(core) = outcome else {
        panic!(
            "live fixed-ambient stabilization of Example0001's own invariant did not close: {outcome:?}"
        )
    };
    let snapshot = core.snapshot().clone();
    drop(checker);
    owner.settle().unwrap();

    (solver, solver_admission, snapshot, houdini)
}

async fn fixed_core_snapshot(
    directory: &support::TestDir,
    catalog_digit: char,
) -> (
    FrameworkIISolverContext,
    SolverAdmission,
    Arc<LeveledCandidateSnapshot>,
) {
    let (solver, solver_admission, snapshot, _houdini) =
        fixed_core_snapshot_with_state(directory, catalog_digit).await;
    (solver, solver_admission, snapshot)
}

/// As [`fixed_core_snapshot_with_state`], but hands the live production
/// checker back too, so a caller can read the run's own search-profile
/// provenance off the checker that produced the Core. The artifact owner
/// is deliberately leaked to the test's `TestDir`, which removes the whole
/// tree, because the checker outlives the settlement point.
async fn fixed_core_snapshot_with_checker(
    directory: &support::TestDir,
    catalog_digit: char,
) -> (
    FrameworkIISolverContext,
    SolverAdmission,
    Arc<LeveledCandidateSnapshot>,
    LeveledHoudiniState,
    FrameworkIIProductionChecker<FrameworkIISolverContext>,
) {
    let solver_admission = agent_admission(2, 1);
    let cancellation = CancellationToken::new();
    let bound = bind(
        worker_pool(1),
        catalog_digit,
        Some(FrameworkIILevel::ONE),
        &solver_admission,
        &cancellation,
    )
    .await;
    let (task, admission, solver, mut houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();

    let clauses = admit(
        &admission,
        &[LEVEL_ZERO_CLAUSE, LEVEL_ONE_CLAUSE],
        &solver_admission,
        &cancellation,
    )
    .await;
    register_and_enqueue(&mut houdini, &clauses);

    let command = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args(["--fixture", "race-proof-fast"])
        .unwrap();
    let config = FrameworkIIProductionCheckConfig::new(
        artifacts.clone(),
        solver_admission.clone(),
        VampireSearchBudget::finite(Duration::from_secs(5)),
        FmbOptions::default(),
        command,
        cancellation.clone(),
        "fixture-vampire",
        certification_profiles(),
    )
    .unwrap();
    let mut checker = solver.clone().production_checker(config);
    let outcome = stabilize_leveled_houdini_with_system_clauses(&mut houdini, &mut checker)
        .await
        .unwrap();
    let LeveledStabilizationOutcome::Stabilized(core) = outcome else {
        panic!("live stabilization of Example0001's own invariant did not close: {outcome:?}")
    };
    let snapshot = core.snapshot().clone();
    std::mem::forget(owner);

    (solver, solver_admission, snapshot, houdini, checker)
}

fn direct_profile(_job: &CertificateJob) -> Result<LeancheckProfile, CoreFreezeError> {
    Ok(LeancheckProfile::new(ProofSearchProfile::Direct))
}

/// The coordinator's original strictly sequential bundle-order pass, which
/// every regeneration of a checked-in tree uses.
fn sequential() -> NonZeroUsize {
    NonZeroUsize::new(1).expect("one is nonzero")
}

fn set_executable(path: &Path) {
    let mut permissions = fs::metadata(path).unwrap().permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).unwrap();
}

/// A minimal, dependency-free SHA-256 for hashing scripted fake-Vampire
/// fixtures in tests; the crate's own hasher is `pub(crate)` only.
fn sha256_hex(bytes: &[u8]) -> String {
    #[rustfmt::skip]
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let mut data = bytes.to_vec();
    let bit_len = (data.len() as u64) * 8;
    data.push(0x80);
    while data.len() % 64 != 56 {
        data.push(0);
    }
    data.extend_from_slice(&bit_len.to_be_bytes());

    for chunk in data.chunks(64) {
        let mut w = [0u32; 64];
        for (i, word) in w.iter_mut().take(16).enumerate() {
            *word = u32::from_be_bytes([
                chunk[4 * i],
                chunk[4 * i + 1],
                chunk[4 * i + 2],
                chunk[4 * i + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh) =
            (h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7]);
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }
    h.iter().map(|word| format!("{word:08x}")).collect()
}

fn collect_files(root: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            collect_files(&path, out);
        } else {
            out.push(path);
        }
    }
}

fn staging_is_empty(staging_root: &Path) -> bool {
    fs::read_dir(staging_root).unwrap().next().is_none()
}

fn no_such_process(script: &Path) -> bool {
    let output = Command::new("pgrep")
        .args(["-f"])
        .arg(script)
        .output()
        .expect("run pgrep");
    !output.status.success()
}

// ------------------------------------------------------------
// Sha256 Self-Test
// ------------------------------------------------------------

#[test]
fn sha256_hex_matches_a_known_vector() {
    assert_eq!(
        sha256_hex(b"abc"),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    assert_eq!(
        sha256_hex(b""),
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    );
}

// ------------------------------------------------------------
// Static Absence Of Python
// ------------------------------------------------------------

#[test]
fn certificate_module_never_invokes_python() {
    let source = fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/framework2/certificate.rs"
    ))
    .unwrap();
    assert!(
        !source.to_lowercase().contains("python"),
        "src/framework2/certificate.rs must never mention python"
    );
    // The only external processes this module launches: `lake`, the
    // resolved `lean` binary, the managed pinned CaDiCaL transport, and
    // (indirectly, through `LeancheckRun`) the pinned leancheck Vampire.
    let command_new_sites: Vec<&str> = source
        .lines()
        .filter(|line| line.contains("Command::new"))
        .collect();
    assert!(!command_new_sites.is_empty());
    for line in command_new_sites {
        assert!(
            line.contains("\"lake\"")
                || line.contains("lean_binary")
                || line.trim() == "let mut command = Command::new(executable);",
            "unexpected process launch site in certificate.rs: {line}"
        );
    }
}

/// Every other module on the certificate path — the profile-selection
/// helper, the wire decoder/packager, and Pass 7.5g's publication and
/// revalidation owner — is likewise Python- and `whiel_synth`-free.
#[test]
fn every_other_certificate_module_never_mentions_python() {
    for relative in [
        "src/framework2/certificate_ops.rs",
        "src/framework2/certificate_profiles.rs",
        "src/framework2/publication.rs",
    ] {
        let path = format!(concat!(env!("CARGO_MANIFEST_DIR"), "/{}"), relative);
        let source = fs::read_to_string(&path).unwrap();
        let lowered = source.to_lowercase();
        assert!(
            !lowered.contains("python"),
            "{relative} must never mention python"
        );
        assert!(
            !lowered.contains("whiel_synth"),
            "{relative} must never mention whiel_synth"
        );
    }
}

/// The standalone `certificate build` CLI module never shells out to
/// Python or the legacy `whiel_synth` certification bridge; its only
/// external processes are `lake`, the fixed-ambient worker executable, and
/// (through [`build_certificate`]) `lean` and the pinned leancheck Vampire.
#[test]
fn certificate_cli_module_never_invokes_python() {
    let source = fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/certificate_cli.rs"
    ))
    .unwrap();
    let lowered = source.to_lowercase();
    assert!(
        !lowered.contains("python"),
        "src/certificate_cli.rs must never mention python"
    );
    assert!(
        !lowered.contains("whiel_synth"),
        "src/certificate_cli.rs must never mention whiel_synth"
    );
}

/// `cli.rs` as a whole legitimately mentions Python (the `task`/`suite`
/// certification bridge), but the `certificate build` grammar branch inside
/// `parse_cli_args` — located here by its own distinguishing function calls
/// rather than free-floating scaffolding comments — must not.
#[test]
fn cli_certificate_subcommand_path_never_mentions_python() {
    let source = fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/src/cli.rs")).unwrap();
    let function_start = source
        .find("pub fn parse_cli_args")
        .expect("src/cli.rs defines parse_cli_args");
    let start = source[function_start..]
        .find("if arguments[0] == \"certificate\"")
        .map(|offset| function_start + offset)
        .expect("parse_cli_args carries the certificate-subcommand branch");
    let end = source[start..]
        .find("return Ok(CliAction::CertificateBuild(config));")
        .map(|offset| start + offset)
        .expect("the certificate-subcommand branch calls parse_certificate_build_arguments");
    assert!(start < end);
    let region = &source[start..end];
    let lowered = region.to_lowercase();
    assert!(
        !lowered.contains("python"),
        "the certificate subcommand path in src/cli.rs must never mention python"
    );
    assert!(
        !lowered.contains("whiel_synth"),
        "the certificate subcommand path in src/cli.rs must never mention whiel_synth"
    );
}

// ------------------------------------------------------------
// Live Certificate Build
// ------------------------------------------------------------

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn build_certificate_succeeds_with_the_real_pinned_vampire() {
    let directory = support::TestDir::new("certificate_success");
    let (solver, solver_admission, snapshot) = fixed_core_snapshot(&directory, '1').await;
    let repository_root = support::repository_root();
    let pinned = PinnedLeancheckVampire::from_lock(&repository_root)
        .expect("the repository-pinned leancheck Vampire resolves");
    let cancellation = CancellationToken::new();
    let staging_root = directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    let destination = directory.path().join("Certificate");
    let evidence = directory.path().join("Evidence");

    let receipt = build_certificate(CertificateBuildRequest {
        solver: &solver,
        admission: &solver_admission,
        snapshot,
        pinned: &pinned,
        profiles: &direct_profile,
        concurrency: sequential(),
        time_limit_seconds: 30,
        repository_root: repository_root.clone(),
        staging_root: staging_root.clone(),
        destination: destination.clone(),
        evidence_destination: Some(evidence.clone()),
        cancellation: &cancellation,
        hooks: CertificateBuildHooks::default(),
    })
    .await
    .expect("a live certificate build of Example0001's own checked-in invariant succeeds");

    let mut axioms = receipt.axioms.clone();
    axioms.sort();
    assert_eq!(axioms, vec!["Classical.choice", "Quot.sound", "propext"]);
    assert_eq!(receipt.jobs.len(), 5);
    assert_eq!(receipt.destination, destination);
    for job in &receipt.jobs {
        assert_eq!(
            job.invocation_identity["profile_id"],
            json!("direct-then-casc-2025-single-core-v4"),
            "job {} did not record the pinned profile version",
            job.id
        );
    }

    // Debugging evidence leaves the published tree. Kernel CNF/LRAT
    // resources and the timing record remain part of the portable result.
    assert!(!destination.join("VampireArtifacts").exists());
    assert!(destination.join("timing.csv").is_file());
    let settings: Value = serde_json::from_slice(
        &fs::read(destination.join("certificate-build-settings.json")).unwrap(),
    )
    .unwrap();
    let configured_jobs = std::env::var("WHIEL_CERTIFICATE_SOLVER_JOBS")
        .map(|value| value.parse::<NonZeroUsize>().unwrap())
        .unwrap_or_else(|_| sequential());
    assert_eq!(settings["solver_jobs"], json!(configured_jobs.get()));
    assert_eq!(settings["preparation_packaging_cpu_worker_limit"], json!(1));
    assert_eq!(settings["pipeline"], "solve-and-package-then-compile");

    let mut files = Vec::new();
    collect_files(&destination, &mut files);
    let lean_files: Vec<&PathBuf> = files
        .iter()
        .filter(|path| path.extension().is_some_and(|ext| ext == "lean"))
        .collect();
    // 14 emitted certificate modules + 5 packaged proofs. The 5 raw
    // leancheck outputs are evidence: moved to `--evidence` instead of
    // riding along in the published tree.
    assert_eq!(lean_files.len(), 19, "{files:?}");

    let non_empty = |path: &Path| fs::metadata(path).map(|metadata| metadata.len() > 0);
    for job_id in JOB_IDS {
        let problem = evidence.join(format!("jobs/{job_id}/problem.p"));
        assert!(
            non_empty(&problem).unwrap_or(false),
            "job {job_id} evidence problem.p is not kept, and not empty, under {evidence:?}"
        );
        let leancheck = evidence.join(format!("jobs/{job_id}/leancheck.lean"));
        assert!(
            non_empty(&leancheck).unwrap_or(false),
            "job {job_id} evidence leancheck.lean is not kept, and not empty, under {evidence:?}"
        );
    }
    // Only the `term_check` job's problem text is pinned against a small
    // tracked fixture; every other job's evidence is checked above only for
    // presence. Regenerate `tests/fixtures/example0001_term_check_problem.p`
    // from a build — never by hand — if the emitter's problem text for this
    // job legitimately changes.
    let term_check_problem = fs::read(evidence.join("jobs/term_check/problem.p")).unwrap();
    let term_check_fixture = fs::read(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/example0001_term_check_problem.p"),
    )
    .unwrap();
    assert_eq!(
        term_check_problem, term_check_fixture,
        "term_check problem.p diverges from the tracked fixture"
    );
    // Every symbol in that text is named by its own carrier, so none of the
    // renamed spellings the renderer used to invent can appear. The needle is
    // the old `ofRepr` prefix over a qualified Lean name rather than a bare
    // `r_`, because a legitimate constant encoding (a string constant `"r "`
    // escapes to `ksr_000020`) can otherwise contain `r_` incidentally.
    assert!(
        !String::from_utf8_lossy(&term_check_problem).contains("r_Whiel"),
        "the emitted problem text still carries a renamed symbol"
    );

    // The frozen Core is recorded beside the tree, as the rows file
    // `certificate build --core` consumes, and it is the checked-in one.
    let record = directory.path().join("Core.json");
    let written: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&record).expect("Core.json is written")).unwrap();
    let checked_in: serde_json::Value = serde_json::from_str(
        &fs::read_to_string(repository_root.join("Benchmark/Example0001/Core.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(
        written, checked_in,
        "the recorded Core differs from the checked-in rows"
    );

    check_portable_empty_resources(&directory, &destination, &staging_root, &cancellation).await;
    assert!(staging_is_empty(&staging_root));

    solver.shutdown().await.unwrap();
}

/// Exercise the real emitted resources after stripping solver evidence and
/// moving the tree. Transport hashes and the Lean replay are separate gates.
async fn check_portable_empty_resources(
    directory: &support::TestDir,
    destination: &Path,
    staging_root: &Path,
    cancellation: &CancellationToken,
) {
    let manifest_path = "EmptyCexCheck/Resources/manifest.json";
    let manifest: Value =
        serde_json::from_slice(&fs::read(destination.join(manifest_path)).unwrap()).unwrap();
    assert_eq!(manifest["kind"], "whiel_empty_domain_certificate_resources");
    assert_eq!(manifest["version"], 1);
    let jobs = manifest["jobs"].as_array().unwrap();
    assert_eq!(jobs.len(), JOB_IDS.len());
    for (job, expected) in jobs.iter().zip(JOB_IDS) {
        assert_eq!(job["job_id"], expected);
        assert_eq!(job["encoding_version"], 1);
        for (path, digest) in [
            ("cnf_relative_path", "cnf_sha256"),
            ("lrat_relative_path", "lrat_sha256"),
        ] {
            let bytes = fs::read(destination.join(job[path].as_str().unwrap())).unwrap();
            assert_eq!(sha256_hex(&bytes), job[digest]);
        }
        assert!(
            destination
                .join(job["module_relative_path"].as_str().unwrap())
                .is_file()
        );
    }
    assert!(!destination.join("EmptyCexCheck.lean").exists());
    let moved = directory.path().join("moved-source-only");
    fs::rename(destination, &moved).unwrap();
    fn request<'a>(
        tree: &'a Path,
        staging_root: &Path,
        cancellation: &'a CancellationToken,
    ) -> CertificateRevalidationRequest<'a> {
        CertificateRevalidationRequest {
            tree,
            canonical_id: "Example0001",
            input_namespace: "Whiel.Benchmark.Example0001",
            certificate_module: "Benchmark.Example0001.Certificate.Valid",
            certificate_theorem: "Whiel.Benchmark.Example0001.Certificate.input_hoare_triple_valid",
            shape: CertificateBundleShape::Valid,
            repository_root: support::repository_root(),
            staging_root: staging_root.to_path_buf(),
            cancellation,
        }
    }
    let checked = revalidate_certificate_tree(request(&moved, staging_root, cancellation))
        .await
        .expect("moved certificate replays its own persistent resources");
    assert_eq!(checked.axioms.len(), 3);
    let first = &jobs[0];
    let cnf = first["cnf_relative_path"].as_str().unwrap();
    let lrat = first["lrat_relative_path"].as_str().unwrap();
    for (index, missing) in [manifest_path, cnf, lrat].into_iter().enumerate() {
        let broken = directory.path().join(format!("missing-resource-{index}"));
        copy_tree(&moved, &broken);
        fs::remove_file(broken.join(missing)).unwrap();
        let error = revalidate_certificate_tree(request(&broken, staging_root, cancellation))
            .await
            .unwrap_err();
        assert!(matches!(error, CertificateBuildError::Io(_)), "{error}");
    }
    for (index, changed) in [cnf, lrat].into_iter().enumerate() {
        let broken = directory.path().join(format!("changed-resource-{index}"));
        copy_tree(&moved, &broken);
        let mut bytes = fs::read(broken.join(changed)).unwrap();
        bytes.push(b'\n');
        fs::write(broken.join(changed), bytes).unwrap();
        let error = revalidate_certificate_tree(request(&broken, staging_root, cancellation))
            .await
            .unwrap_err();
        assert!(
            matches!(error, CertificateBuildError::Tampered { .. }),
            "{error}"
        );
    }
    // Matching a rewritten manifest cannot authorize a different CNF or a
    // truncated/trailing-garbage LRAT trace. Lean still checks exact binding
    // and consumes the complete proof resource.
    let trailing_trace = format!(
        "{}trailing-garbage\n",
        fs::read_to_string(moved.join(lrat)).unwrap()
    );
    for (index, (changed, hash_key, replacement)) in [
        (cnf, "cnf_sha256", "p cnf 1 1\n1 0\n".to_string()),
        (lrat, "lrat_sha256", String::new()),
        (lrat, "lrat_sha256", trailing_trace),
    ]
    .into_iter()
    .enumerate()
    {
        let broken = directory
            .path()
            .join(format!("invalid-bound-resource-{index}"));
        copy_tree(&moved, &broken);
        fs::write(broken.join(changed), &replacement).unwrap();
        let mut updated = manifest.clone();
        updated["jobs"][0][hash_key] = json!(sha256_hex(replacement.as_bytes()));
        fs::write(
            broken.join(manifest_path),
            serde_json::to_vec_pretty(&updated).unwrap(),
        )
        .unwrap();
        let error = revalidate_certificate_tree(request(&broken, staging_root, cancellation))
            .await
            .unwrap_err();
        assert!(
            matches!(error, CertificateBuildError::Build { .. }),
            "{error}"
        );
    }
    assert!(staging_is_empty(staging_root));
    fs::rename(&moved, destination).unwrap();
}

/// P3 with no `--evidence`: the published tree still carries no evidence
/// subtree and still carries `timing.csv`, and nothing under the evidence
/// name survives anywhere in the test's own directory either — dropped, not
/// merely left unpromoted somewhere else.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn build_certificate_drops_evidence_when_none_is_named() {
    let directory = support::TestDir::new("certificate_evidence_dropped");
    let (solver, solver_admission, snapshot) = fixed_core_snapshot(&directory, '1').await;
    let repository_root = support::repository_root();
    let pinned = PinnedLeancheckVampire::from_lock(&repository_root)
        .expect("the repository-pinned leancheck Vampire resolves");
    let cancellation = CancellationToken::new();
    let staging_root = directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    let destination = directory.path().join("Certificate");

    build_certificate(CertificateBuildRequest {
        solver: &solver,
        admission: &solver_admission,
        snapshot,
        pinned: &pinned,
        profiles: &direct_profile,
        concurrency: sequential(),
        time_limit_seconds: 30,
        repository_root,
        staging_root: staging_root.clone(),
        destination: destination.clone(),
        evidence_destination: None,
        cancellation: &cancellation,
        hooks: CertificateBuildHooks::default(),
    })
    .await
    .expect("a build with no evidence destination still succeeds");

    assert!(!destination.join("VampireArtifacts").exists());
    assert!(destination.join("timing.csv").is_file());
    assert!(staging_is_empty(&staging_root));
    let mut files = Vec::new();
    collect_files(directory.path(), &mut files);
    assert!(
        files.iter().all(|path| !path
            .components()
            .any(|component| component.as_os_str() == "VampireArtifacts")),
        "no evidence subtree survives anywhere under the test directory: {files:?}"
    );

    solver.shutdown().await.unwrap();
}

/// P3's refusal cases: an evidence destination this build cannot use fails
/// the build before any staging directory is even created.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn build_certificate_refuses_an_unusable_evidence_destination() {
    let directory = support::TestDir::new("certificate_evidence_refused");
    let (solver, solver_admission, snapshot) = fixed_core_snapshot(&directory, '1').await;
    let script = directory.path().join("unused-leancheck.sh");
    fs::write(&script, "#!/bin/sh\nexit 1\n").unwrap();
    set_executable(&script);
    let sha256 = sha256_hex(&fs::read(&script).unwrap());
    let pinned = PinnedLeancheckVampire::unverified_for_tests(script, sha256);
    let cancellation = CancellationToken::new();
    let staging_root = directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    let destination = directory.path().join("Certificate");

    // Already exists: evidence is moved out, never merged into or
    // overwritten at a caller-supplied destination.
    let occupied = directory.path().join("Occupied");
    fs::create_dir_all(&occupied).unwrap();
    let error = build_certificate(CertificateBuildRequest {
        solver: &solver,
        admission: &solver_admission,
        snapshot: snapshot.clone(),
        pinned: &pinned,
        profiles: &direct_profile,
        concurrency: sequential(),
        time_limit_seconds: 10,
        repository_root: support::repository_root(),
        staging_root: staging_root.clone(),
        destination: destination.clone(),
        evidence_destination: Some(occupied.clone()),
        cancellation: &cancellation,
        hooks: CertificateBuildHooks::default(),
    })
    .await
    .unwrap_err();
    assert!(
        matches!(
            &error,
            CertificateBuildError::EvidenceDestinationExists(path) if path == &occupied
        ),
        "{error:?}"
    );
    assert!(staging_is_empty(&staging_root));

    // Inside the staging tree, or inside (or containing) the certificate
    // destination: either is refused as a conflict, and neither check
    // requires the conflicting path to exist first.
    for evidence in [staging_root.join("evidence"), destination.join("evidence")] {
        let error = build_certificate(CertificateBuildRequest {
            solver: &solver,
            admission: &solver_admission,
            snapshot: snapshot.clone(),
            pinned: &pinned,
            profiles: &direct_profile,
            concurrency: sequential(),
            time_limit_seconds: 10,
            repository_root: support::repository_root(),
            staging_root: staging_root.clone(),
            destination: destination.clone(),
            evidence_destination: Some(evidence.clone()),
            cancellation: &cancellation,
            hooks: CertificateBuildHooks::default(),
        })
        .await
        .unwrap_err();
        assert!(
            matches!(
                &error,
                CertificateBuildError::EvidenceDestinationConflict {
                    evidence_destination,
                    ..
                } if evidence_destination == &evidence
            ),
            "{error:?}"
        );
    }
    assert!(staging_is_empty(&staging_root));
    assert!(!destination.exists(), "a refused build promotes nothing");

    solver.shutdown().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_rewritten_module_lean_rejects_falls_back_to_the_emitted_proof() {
    // The end-to-end shape of the compile gate. Every one of
    // Example0001's five proofs is rewritten by the targeted clause
    // projection, so overwriting one staged module with text Lean refuses
    // exercises the gate on a job that really was rewritten: the build
    // must give up that projection while retaining the mandatory
    // kernel-SAT replacement, and record the selected fallback.
    const JOB: &str = "init_clause_0";
    const MODULE: &str = "Benchmark/Example0001/Certificate/VampireProofJobs/InitClause0.lean";

    let directory = support::TestDir::new("certificate_transform_fallback");
    let (solver, solver_admission, snapshot) = fixed_core_snapshot(&directory, '1').await;
    let repository_root = support::repository_root();
    let pinned = PinnedLeancheckVampire::from_lock(&repository_root)
        .expect("the repository-pinned leancheck Vampire resolves");
    let cancellation = CancellationToken::new();
    let staging_root = directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    let destination = directory.path().join("Certificate");

    let hooks = CertificateBuildHooks {
        after_solve: Some(Box::new(|stage: &Path| {
            let staged = stage.join("src").join(MODULE);
            let packaged = fs::read_to_string(&staged).expect("the rewritten module is staged");
            assert!(
                packaged.contains("vampire_project_ordered"),
                "the fixture job must have been rewritten by the projection"
            );
            fs::write(
                &staged,
                "import VampLean\n\ntheorem staged_candidate : False := trivial\n",
            )
            .unwrap();
        })),
        ..CertificateBuildHooks::default()
    };

    let receipt = build_certificate(CertificateBuildRequest {
        solver: &solver,
        admission: &solver_admission,
        snapshot,
        pinned: &pinned,
        profiles: &direct_profile,
        concurrency: sequential(),
        time_limit_seconds: 30,
        repository_root: repository_root.clone(),
        staging_root: staging_root.clone(),
        destination: destination.clone(),
        evidence_destination: None,
        cancellation: &cancellation,
        hooks,
    })
    .await
    .expect("the gate retains the kernel-safe proof when projection is rejected");

    let mut axioms = receipt.axioms.clone();
    axioms.sort();
    assert_eq!(axioms, vec!["Classical.choice", "Quot.sound", "propext"]);

    let job = receipt
        .jobs
        .iter()
        .find(|job| job.id == JOB)
        .expect("the rewritten job has a receipt");
    let projection = job
        .transforms
        .iter()
        .find(|record| record.id == ProofTransformId::ClauseProjection)
        .expect("the projection step ran");
    assert_eq!(projection.outcome, ProofTransformOutcome::Fallback);
    let kernel_sat = job
        .transforms
        .iter()
        .find(|record| record.id == ProofTransformId::AvatarKernelSat)
        .expect("the AVATAR-on fixture requires the kernel-SAT step");
    assert_eq!(kernel_sat.outcome, ProofTransformOutcome::Applied);
    assert_eq!(kernel_sat.input_sha256, job.canonical_sha256);
    assert_eq!(
        job.transformed_sha256, kernel_sat.output_sha256,
        "a rejected projection retains the mandatory kernel-SAT replacement"
    );
    assert_ne!(job.transformed_sha256, job.canonical_sha256);
    assert_ne!(job.canonical_sha256, projection.output_sha256);

    // The unsupported XOR ancestor is now declined before compilation.
    // It retains projection without trying the known-bad local slice.
    const GATED: [&str; 2] = [JOB, "maint_clause_0"];
    let sliced = receipt
        .jobs
        .iter()
        .find(|job| job.id == "maint_clause_0")
        .expect("the sliced job has a receipt");
    let outcome_of = |job: &CertificateJobReceipt, id| {
        job.transforms
            .iter()
            .find(|record| record.id == id)
            .unwrap_or_else(|| panic!("job {} records every step", job.id))
            .outcome
    };
    assert_eq!(
        outcome_of(sliced, ProofTransformId::LocalPrenex),
        ProofTransformOutcome::Miss,
        "maint_clause_0's unsupported XOR lineage is a structural miss"
    );
    assert_eq!(
        outcome_of(sliced, ProofTransformId::ClauseProjection),
        ProofTransformOutcome::Applied,
        "maint_clause_0 keeps its projection: the chain drops one rewrite, not all of them"
    );
    assert_ne!(
        sliced.transformed_sha256, sliced.canonical_sha256,
        "maint_clause_0 publishes the projected candidate, not the canonical text"
    );
    let sliced_module = fs::read_to_string(
        destination
            .join("VampireProofJobs")
            .join("MaintClause0.lean"),
    )
    .unwrap();
    assert!(
        sliced_module.contains("vampire_project_ordered"),
        "the published maint_clause_0 module keeps the projection it did not give up"
    );

    // `init_clause_0`, whose module the hook clobbered, has no slice of
    // its own, so its chain is one candidate long and lands on the
    // kernel-SAT text, without the optional projection.
    assert_eq!(
        outcome_of(job, ProofTransformId::LocalPrenex),
        ProofTransformOutcome::Miss
    );
    assert_eq!(
        outcome_of(job, ProofTransformId::ClauseProjection),
        ProofTransformOutcome::Fallback
    );

    // Every other job kept its rewrite: the gate is per module and closes
    // once, it does not disable the transformation for the build.
    for other in receipt
        .jobs
        .iter()
        .filter(|other| !GATED.contains(&other.id.as_str()))
    {
        let projection = other
            .transforms
            .iter()
            .find(|record| record.id == ProofTransformId::ClauseProjection)
            .expect("the projection step ran");
        assert_eq!(
            projection.outcome,
            ProofTransformOutcome::Applied,
            "job {} must keep its rewrite",
            other.id
        );
    }

    // The published module is the fallback packaging the receipt names,
    // with the emitted proof body and the mandatory kernel-SAT helper.
    let published = fs::read(
        destination
            .join("VampireProofJobs")
            .join("InitClause0.lean"),
    )
    .unwrap();
    assert_eq!(sha256_hex(&published), job.packaged_sha256);
    let published = String::from_utf8(published).unwrap();
    assert!(!published.contains("vampire_project_ordered"));
    assert!(!published.contains("theorem staged_candidate"));
    assert!(published.contains("import VampLean"));
    assert!(published.contains("lrat_proof"));
    assert!(!published.contains("bv_decide"));
    assert!(!published.contains("native_decide"));

    assert!(staging_is_empty(&staging_root));

    solver.shutdown().await.unwrap();
}

// A compiling proof with a named axiom must fail the final check without
// fallback. A slow candidate still falls back, retaining mandatory LRAT.
async fn candidate_rejection_policy(slow: bool) {
    const MODULE: &str = "Benchmark.Example0001.Certificate.VampireProofJobs.MaintClause0";
    const RELATIVE: &str = "Benchmark/Example0001/Certificate/VampireProofJobs/MaintClause0.lean";
    let directory = support::TestDir::new(if slow {
        "certificate_candidate_timeout"
    } else {
        "certificate_candidate_axiom"
    });
    let (solver, solver_admission, snapshot) = fixed_core_snapshot(&directory, '1').await;
    let repository_root = support::repository_root();
    let pinned = PinnedLeancheckVampire::from_lock(&repository_root).unwrap();
    let cancellation = CancellationToken::new();
    let staging_root = directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    let destination = directory.path().join("Certificate");
    let attempts = Arc::new(AtomicUsize::new(0));
    let counted = Arc::clone(&attempts);
    let hooks = CertificateBuildHooks {
        before_module_compile: Some(Box::new(move |stage, dotted| {
            if dotted != MODULE || counted.fetch_add(1, Ordering::SeqCst) != 0 {
                return;
            }
            let path = stage.join("src").join(RELATIVE);
            let source = fs::read_to_string(&path).unwrap();
            assert!(source.contains("vampire_project_ordered"));
            assert!(source.contains("lrat_proof"));
            let start = source.find("theorem fullProof :").unwrap();
            let body = start + source[start..].find(" := by").unwrap();
            let end = body + source[body..].find("\nend vamproof").unwrap();
            let mut rewritten = source[..start].to_string();
            // Keep all helper declarations and fullProof's exact header.
            // The named axiom compiles; the final theorem's transitive
            // audit must reject it without selecting another candidate.
            rewritten.push_str("axiom candidateHole : False\n");
            rewritten.push_str(&source[start..body]);
            rewritten.push_str(" := by\n  exact candidateHole.elim\n");
            if slow {
                rewritten.push_str("#eval IO.sleep 10000\n");
            }
            rewritten.push_str(&source[end..]);
            fs::write(&path, rewritten).unwrap();
        })),
        candidate_budget: Some(Box::new(move |dotted, attempt| {
            if slow && dotted == MODULE && attempt == 0 {
                Duration::from_millis(250)
            } else {
                Duration::from_secs(60)
            }
        })),
        ..Default::default()
    };
    let result = build_certificate(CertificateBuildRequest {
        solver: &solver,
        admission: &solver_admission,
        snapshot,
        pinned: &pinned,
        profiles: &direct_profile,
        concurrency: sequential(),
        time_limit_seconds: 30,
        repository_root,
        staging_root: staging_root.clone(),
        destination: destination.clone(),
        evidence_destination: None,
        cancellation: &cancellation,
        hooks,
    })
    .await;
    if !slow {
        let error = result.unwrap_err();
        // The portable final-source guard normally rejects first; the
        // independent Check importer also rejects the same axiom closure.
        let final_rejection = match &error {
            CertificateBuildError::Axioms { found } => {
                found.iter().any(|axiom| axiom.contains("candidateHole"))
            }
            CertificateBuildError::Build {
                module,
                diagnostics,
            } => {
                (module == "Benchmark.Example0001.Certificate.Valid"
                    || module == "Lake certificate build")
                    && diagnostics.contains("candidateHole")
            }
            _ => false,
        };
        assert!(final_rejection, "{error:?}");
        assert_eq!(attempts.load(Ordering::SeqCst), 1);
        assert!(!destination.exists());
        assert!(staging_is_empty(&staging_root));
        solver.shutdown().await.unwrap();
        return;
    }
    let receipt = result.expect("a timed-out candidate retains the kernel-safe fallback");
    assert_eq!(attempts.load(Ordering::SeqCst), 2);
    let job = receipt
        .jobs
        .iter()
        .find(|job| job.id == "maint_clause_0")
        .unwrap();
    for (id, expected) in [
        (ProofTransformId::LocalPrenex, ProofTransformOutcome::Miss),
        (
            ProofTransformId::ClauseProjection,
            ProofTransformOutcome::Fallback,
        ),
        (
            ProofTransformId::AvatarKernelSat,
            ProofTransformOutcome::Applied,
        ),
    ] {
        assert_eq!(
            job.transforms
                .iter()
                .find(|record| record.id == id)
                .unwrap()
                .outcome,
            expected
        );
    }
    let published = fs::read(destination.join("VampireProofJobs/MaintClause0.lean")).unwrap();
    assert_eq!(sha256_hex(&published), job.packaged_sha256);
    let published = String::from_utf8(published).unwrap();
    assert!(!published.contains("vampire_project_ordered"));
    assert!(published.contains("lrat_proof"));
    assert!(!published.contains("candidateHole"));
    assert!(!published.contains("bv_decide"));
    assert!(!published.contains("native_decide"));
    assert!(!destination.join("ProofCandidateAudit.lean").exists());
    let mut axioms = receipt.axioms.clone();
    axioms.sort();
    assert_eq!(axioms, vec!["Classical.choice", "Quot.sound", "propext"]);
    assert!(
        !cancellation.is_cancelled(),
        "candidate rejection does not cancel the build"
    );
    assert!(staging_is_empty(&staging_root));
    solver.shutdown().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_slow_candidate_times_out_and_keeps_the_kernel_safe_fallback() {
    candidate_rejection_policy(true).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_compiling_non_std3_candidate_fails_without_fallback() {
    candidate_rejection_policy(false).await;
}

/// Every file of a promoted certificate tree, keyed by its path relative
/// to the tree root, in one deterministic order.
fn tree_contents(root: &Path) -> BTreeMap<String, Vec<u8>> {
    let mut files = Vec::new();
    collect_files(root, &mut files);
    files
        .into_iter()
        .map(|path| {
            let relative = path
                .strip_prefix(root)
                .expect("every collected file is under the tree")
                .to_string_lossy()
                .into_owned();
            (relative, fs::read(&path).unwrap())
        })
        .collect()
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn two_rebuilds_of_example0001_agree_modulo_the_telescope_order() {
    // The reproducibility canary. Two builds of the same frozen Core by
    // the same pinned toolchain must publish the same tree and move out the
    // same evidence, or the tree is not a thing a reviewer can rebuild and
    // check. Vampire's own wall clock and peak memory used to be written
    // into every retained solver output, which made that false by
    // construction; they are recorded in the tree's own `timing.csv` and
    // the build receipt instead, and nothing else carries them. Each round
    // names its own `--evidence` destination, so the published tree carries
    // none of the solver-evidence subtree, but the moved-out evidence is
    // folded into the same comparison, under a `VampireArtifacts/` key
    // prefix matching where it used to live in the tree, so the telescope
    // and volatile-line checks below still cover `leancheck.lean` and the
    // comparison still catches a `problem.p` that rebuilds differently.
    //
    // One volatility is left, deliberately: Vampire collects the binder
    // names of an equal-type `variable` group from an unordered set, so it
    // can write one telescope two ways. That order is real Lean the
    // reconstruction modules consume, so no rewrite touches it and the
    // comparison — like `run_revalidation`'s own
    // `telescope_normalized_digest` — absorbs it here.
    let directory = support::TestDir::new("certificate_reproducible");
    let repository_root = support::repository_root();
    let pinned = PinnedLeancheckVampire::from_lock(&repository_root)
        .expect("the repository-pinned leancheck Vampire resolves");
    let cancellation = CancellationToken::new();

    let mut trees = Vec::new();
    for round in 0..2 {
        let (solver, solver_admission, snapshot) = fixed_core_snapshot(&directory, '1').await;
        let staging_root = directory.path().join(format!("staging{round}"));
        fs::create_dir_all(&staging_root).unwrap();
        let destination = directory.path().join(format!("Certificate{round}"));
        let evidence = directory.path().join(format!("Evidence{round}"));
        build_certificate(CertificateBuildRequest {
            solver: &solver,
            admission: &solver_admission,
            snapshot,
            pinned: &pinned,
            profiles: &direct_profile,
            concurrency: sequential(),
            time_limit_seconds: 30,
            repository_root: repository_root.clone(),
            staging_root: staging_root.clone(),
            destination: destination.clone(),
            evidence_destination: Some(evidence.clone()),
            cancellation: &cancellation,
            hooks: CertificateBuildHooks::default(),
        })
        .await
        .expect("each rebuild of Example0001's frozen Core succeeds");
        solver.shutdown().await.unwrap();
        let mut combined = tree_contents(&destination);
        for (relative, contents) in tree_contents(&evidence) {
            combined.insert(format!("VampireArtifacts/{relative}"), contents);
        }
        trees.push(combined);
    }

    let (first, second) = (&trees[0], &trees[1]);
    assert_eq!(
        first.keys().collect::<Vec<_>>(),
        second.keys().collect::<Vec<_>>(),
        "the two rebuilds publish or move out different files"
    );
    for (relative, left) in first {
        // `timing.csv` is the one file that *is* the measurements, so it
        // is expected to differ; nothing else may.
        if relative.ends_with("timing.csv") {
            continue;
        }
        let left = String::from_utf8_lossy(left);
        let right = String::from_utf8_lossy(&second[relative]);
        assert_eq!(
            normalize_telescope_order(&left),
            normalize_telescope_order(&right),
            "{relative} differs between two rebuilds of the same frozen Core"
        );
        for prefix in VOLATILE_LINE_PREFIXES {
            assert!(
                !left.contains(prefix),
                "{relative} carries the volatile line `{prefix}`"
            );
        }
    }

    // And the certificate's own resource policy replaced Vampire's, in
    // every published module and every retained solver output.
    for (relative, contents) in first {
        if !relative.ends_with(".lean") {
            continue;
        }
        let contents = String::from_utf8_lossy(contents);
        assert!(
            !contents.contains("set_option maxHeartbeats 0"),
            "{relative} keeps Vampire's unlimited heartbeat budget"
        );
        assert!(
            !contents.contains("set_option maxRecDepth 100000000"),
            "{relative} keeps Vampire's unlimited recursion depth"
        );
        if contents.contains("section vamproof") {
            for policy in CERTIFICATE_RESOURCE_POLICY {
                assert!(
                    contents.contains(policy),
                    "{relative} does not carry the certificate resource policy `{policy}`"
                );
            }
        }
    }

    // The folded-in evidence is real content, not an empty placeholder the
    // byte-for-byte comparison above would happily call identical.
    assert!(
        !first["VampireArtifacts/jobs/term_check/problem.p"].is_empty(),
        "moved-out evidence must not be empty"
    );

    // The timing record is written once, at the certificate tree's own
    // root, with one row per job and the header a reader can check.
    let timing = String::from_utf8(first["timing.csv"].clone()).unwrap();
    let mut rows = timing.lines();
    assert_eq!(
        rows.next(),
        Some(
            "job,profile,vampire_elapsed_s,vampire_peak_mb,transform_s,\
             proof_module_lean_s,reconstruction_lean_s"
        )
    );
    let rows: Vec<&str> = rows.collect();
    assert_eq!(rows.len(), JOB_IDS.len());
    for (row, job_id) in rows.iter().zip(JOB_IDS) {
        let cells: Vec<&str> = row.split(',').collect();
        assert_eq!(cells.len(), 7, "{row}");
        assert_eq!(cells[0], job_id);
        assert_eq!(cells[1], "direct");
        for (column, cell) in cells[2..].iter().enumerate() {
            assert!(
                cell.parse::<f64>().is_ok_and(|value| value >= 0.0),
                "column {column} of `{row}` is not a measurement"
            );
        }
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_module_whose_every_candidate_is_rejected_fails_the_build() {
    // The chain is a retreat, not an escape. When Lean rejects the full
    // rewrite *and* every candidate below it, there is no proof of that
    // job left to publish, so the build fails with the last rejection
    // rather than promoting a tree. The per-module hook is the only seam
    // that reaches a candidate the gate stages itself, so it stands in
    // for a module nothing can compile.
    const MODULE: &str = "Benchmark.Example0001.Certificate.VampireProofJobs.InitClause0";
    const RELATIVE: &str = "Benchmark/Example0001/Certificate/VampireProofJobs/InitClause0.lean";

    let directory = support::TestDir::new("certificate_transform_exhausted");
    let (solver, solver_admission, snapshot) = fixed_core_snapshot(&directory, '1').await;
    let repository_root = support::repository_root();
    let pinned = PinnedLeancheckVampire::from_lock(&repository_root)
        .expect("the repository-pinned leancheck Vampire resolves");
    let cancellation = CancellationToken::new();
    let staging_root = directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    let destination = directory.path().join("Certificate");

    let attempts = Arc::new(AtomicUsize::new(0));
    let counted = Arc::clone(&attempts);
    let hooks = CertificateBuildHooks {
        before_module_compile: Some(Box::new(move |stage: &Path, dotted: &str| {
            if dotted != MODULE {
                return;
            }
            counted.fetch_add(1, Ordering::SeqCst);
            fs::write(
                stage.join("src").join(RELATIVE),
                "import VampLean\n\ntheorem staged_candidate : False := trivial\n",
            )
            .unwrap();
        }) as CertificateModuleHook),
        ..CertificateBuildHooks::default()
    };

    let error = build_certificate(CertificateBuildRequest {
        solver: &solver,
        admission: &solver_admission,
        snapshot,
        pinned: &pinned,
        profiles: &direct_profile,
        concurrency: sequential(),
        time_limit_seconds: 30,
        repository_root: repository_root.clone(),
        staging_root: staging_root.clone(),
        destination: destination.clone(),
        evidence_destination: None,
        cancellation: &cancellation,
        hooks,
    })
    .await
    .expect_err("a module no candidate can compile fails the build");

    match error {
        CertificateBuildError::Build { module, .. } => assert_eq!(module, MODULE),
        other => panic!("expected a build rejection, got {other}"),
    }
    // The full rewrite plus one candidate: `init_clause_0` is projected
    // and has no slice of its own, so its chain is the canonical text
    // alone.
    assert_eq!(attempts.load(Ordering::SeqCst), 2);
    assert!(!destination.exists(), "a failed build promotes nothing");

    solver.shutdown().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn build_certificate_reports_a_solver_failure() {
    let directory = support::TestDir::new("certificate_solver_failure");
    let (solver, solver_admission, snapshot) = fixed_core_snapshot(&directory, '2').await;
    let script = directory.path().join("fake_vampire_exit1.sh");
    fs::write(&script, "#!/bin/sh\nexit 1\n").unwrap();
    set_executable(&script);
    let sha256 = sha256_hex(&fs::read(&script).unwrap());
    let pinned = PinnedLeancheckVampire::unverified_for_tests(script, sha256);
    let cancellation = CancellationToken::new();
    let staging_root = directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    let destination = directory.path().join("Certificate");

    let error = build_certificate(CertificateBuildRequest {
        solver: &solver,
        admission: &solver_admission,
        snapshot,
        pinned: &pinned,
        profiles: &direct_profile,
        concurrency: sequential(),
        time_limit_seconds: 10,
        repository_root: support::repository_root(),
        staging_root: staging_root.clone(),
        destination,
        evidence_destination: None,
        cancellation: &cancellation,
        hooks: CertificateBuildHooks::default(),
    })
    .await
    .unwrap_err();
    assert!(
        matches!(error, CertificateBuildError::Solver { .. }),
        "{error:?}"
    );
    assert!(staging_is_empty(&staging_root));

    solver.shutdown().await.unwrap();
}

/// Malformed solver output is refused before anything is packaged, and a
/// proof that survives the transformation pipeline is still refused by
/// Lean's own packaging. The two refusals are distinct and both leave the
/// staging directory empty.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn build_certificate_refuses_malformed_solver_output_at_both_gates() {
    let directory = support::TestDir::new("certificate_malformed_output");
    let (solver, solver_admission, snapshot) = fixed_core_snapshot(&directory, '3').await;
    let cancellation = CancellationToken::new();
    let staging_root = directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();

    // Text that is not a VampLean proof module at all: the canonical step
    // of the proof-transformation pipeline is the first thing to read it,
    // and it refuses on the missing import.
    let script = directory.path().join("fake_vampire_garbage.sh");
    fs::write(
        &script,
        "#!/bin/sh\nprintf 'theorem fullProof := garbage not a real Lean proof {{{\\nend vamproof\\n'\nexit 0\n",
    )
    .unwrap();
    set_executable(&script);
    let sha256 = sha256_hex(&fs::read(&script).unwrap());
    let pinned = PinnedLeancheckVampire::unverified_for_tests(script, sha256);
    let error = build_certificate(CertificateBuildRequest {
        solver: &solver,
        admission: &solver_admission,
        snapshot: snapshot.clone(),
        pinned: &pinned,
        profiles: &direct_profile,
        concurrency: sequential(),
        time_limit_seconds: 10,
        repository_root: support::repository_root(),
        staging_root: staging_root.clone(),
        destination: directory.path().join("Certificate"),
        evidence_destination: None,
        cancellation: &cancellation,
        hooks: CertificateBuildHooks::default(),
    })
    .await
    .unwrap_err();
    assert!(
        matches!(error, CertificateBuildError::ProofTransform { .. }),
        "{error:?}"
    );
    assert!(staging_is_empty(&staging_root));

    // Text with the right module shape but a namespace of its own: the
    // transformations pass it through unchanged and Lean's `packageProof`
    // refuses it.
    let script = directory.path().join("fake_vampire_namespaced.sh");
    fs::write(
        &script,
        concat!(
            "#!/bin/sh\nprintf '%s' '",
            "-- Lean proof output generated by Vampire\n",
            "import VampLean\n",
            "section vamproof\n",
            "namespace Foreign\n",
            "theorem fullProof : True := trivial\n",
            "end vamproof\n",
            "'\nexit 0\n",
        ),
    )
    .unwrap();
    set_executable(&script);
    let sha256 = sha256_hex(&fs::read(&script).unwrap());
    let pinned = PinnedLeancheckVampire::unverified_for_tests(script, sha256);
    let error = build_certificate(CertificateBuildRequest {
        solver: &solver,
        admission: &solver_admission,
        snapshot,
        pinned: &pinned,
        profiles: &direct_profile,
        concurrency: sequential(),
        time_limit_seconds: 10,
        repository_root: support::repository_root(),
        staging_root: staging_root.clone(),
        destination: directory.path().join("CertificateNamespaced"),
        evidence_destination: None,
        cancellation: &cancellation,
        hooks: CertificateBuildHooks::default(),
    })
    .await
    .unwrap_err();
    assert!(
        matches!(error, CertificateBuildError::Package { .. }),
        "{error:?}"
    );
    assert!(staging_is_empty(&staging_root));

    solver.shutdown().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn build_certificate_times_out_and_then_cancels_cleanly_with_no_surviving_child() {
    let directory = support::TestDir::new("certificate_timeout_and_cancel");
    let (solver, solver_admission, snapshot) = fixed_core_snapshot(&directory, '4').await;
    let script = directory.path().join("fake_vampire_sleep.sh");
    fs::write(&script, "#!/bin/sh\nsleep 60\n").unwrap();
    set_executable(&script);
    let sha256 = sha256_hex(&fs::read(&script).unwrap());
    let pinned = PinnedLeancheckVampire::unverified_for_tests(script.clone(), sha256);
    let repository_root = support::repository_root();

    // Timeout: a 2-second deadline against a 60-second sleeper.
    {
        let cancellation = CancellationToken::new();
        let staging_root = directory.path().join("staging_timeout");
        fs::create_dir_all(&staging_root).unwrap();
        let destination = directory.path().join("Certificate_timeout");
        let error = build_certificate(CertificateBuildRequest {
            solver: &solver,
            admission: &solver_admission,
            snapshot: snapshot.clone(),
            pinned: &pinned,
            profiles: &direct_profile,
            concurrency: sequential(),
            time_limit_seconds: 2,
            repository_root: repository_root.clone(),
            staging_root: staging_root.clone(),
            destination,
            evidence_destination: None,
            cancellation: &cancellation,
            hooks: CertificateBuildHooks::default(),
        })
        .await
        .unwrap_err();
        assert!(
            matches!(
                &error,
                CertificateBuildError::Solver {
                    source: whiel_runner::framework2::LeancheckError::Timeout,
                    ..
                }
            ),
            "{error:?}"
        );
        assert!(staging_is_empty(&staging_root));
        assert!(
            no_such_process(&script),
            "the sleeping fixture must not survive a timeout"
        );
    }

    // Cancellation from another task.
    {
        let cancellation = CancellationToken::new();
        let canceller = cancellation.clone();
        let cancel_after = tokio::spawn(async move {
            tokio::time::sleep(Duration::from_millis(200)).await;
            canceller.cancel();
        });
        let staging_root = directory.path().join("staging_cancel");
        fs::create_dir_all(&staging_root).unwrap();
        let destination = directory.path().join("Certificate_cancel");
        let error = build_certificate(CertificateBuildRequest {
            solver: &solver,
            admission: &solver_admission,
            snapshot,
            pinned: &pinned,
            profiles: &direct_profile,
            concurrency: sequential(),
            time_limit_seconds: 60,
            repository_root,
            staging_root: staging_root.clone(),
            destination,
            evidence_destination: None,
            cancellation: &cancellation,
            hooks: CertificateBuildHooks::default(),
        })
        .await
        .unwrap_err();
        cancel_after.await.unwrap();
        assert!(
            matches!(error, CertificateBuildError::Cancelled),
            "{error:?}"
        );
        assert!(staging_is_empty(&staging_root));
        assert!(
            no_such_process(&script),
            "the sleeping fixture must not survive cancellation"
        );
    }

    solver.shutdown().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn build_certificate_rejects_a_tampered_staged_problem() {
    let directory = support::TestDir::new("certificate_tampered");
    let (solver, solver_admission, snapshot) = fixed_core_snapshot(&directory, '5').await;
    let repository_root = support::repository_root();
    let pinned = PinnedLeancheckVampire::from_lock(&repository_root)
        .expect("the repository-pinned leancheck Vampire resolves");
    let cancellation = CancellationToken::new();
    let staging_root = directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    let destination = directory.path().join("Certificate");

    let hooks = CertificateBuildHooks {
        after_emit: Some(Box::new(|stage: &Path| {
            let path = stage.join(
                "src/Benchmark/Example0001/Certificate/VampireArtifacts/jobs/init_clause_0/problem.p",
            );
            fs::write(&path, b"fof(tampered, axiom, $true).\n").unwrap();
        })),
        ..Default::default()
    };

    let error = build_certificate(CertificateBuildRequest {
        solver: &solver,
        admission: &solver_admission,
        snapshot,
        pinned: &pinned,
        profiles: &direct_profile,
        concurrency: sequential(),
        time_limit_seconds: 10,
        repository_root,
        staging_root: staging_root.clone(),
        destination,
        evidence_destination: None,
        cancellation: &cancellation,
        hooks,
    })
    .await
    .unwrap_err();
    assert!(
        matches!(error, CertificateBuildError::Tampered { .. }),
        "{error:?}"
    );
    assert!(staging_is_empty(&staging_root));

    solver.shutdown().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn build_certificate_reports_a_syntax_error_as_a_build_failure() {
    let directory = support::TestDir::new("certificate_build_failure");
    let (solver, solver_admission, snapshot) = fixed_core_snapshot(&directory, '6').await;
    let repository_root = support::repository_root();
    let pinned = PinnedLeancheckVampire::from_lock(&repository_root)
        .expect("the repository-pinned leancheck Vampire resolves");
    let cancellation = CancellationToken::new();
    let staging_root = directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    let destination = directory.path().join("Certificate");

    let hooks = CertificateBuildHooks {
        before_build: Some(Box::new(|stage: &Path| {
            let path = stage.join("src/Benchmark/Example0001/Certificate/Proposal.lean");
            let mut contents = fs::read_to_string(&path).unwrap();
            contents.push_str("\nsyntax error {{{\n");
            fs::write(&path, contents).unwrap();
        })),
        ..Default::default()
    };

    let error = build_certificate(CertificateBuildRequest {
        solver: &solver,
        admission: &solver_admission,
        snapshot,
        pinned: &pinned,
        profiles: &direct_profile,
        concurrency: sequential(),
        time_limit_seconds: 30,
        repository_root,
        staging_root: staging_root.clone(),
        destination,
        evidence_destination: None,
        cancellation: &cancellation,
        hooks,
    })
    .await
    .unwrap_err();
    match &error {
        CertificateBuildError::Build { module, .. } => {
            assert!(module.ends_with("Proposal"), "{module}");
        }
        other => panic!("expected Build, got {other:?}"),
    }
    assert!(staging_is_empty(&staging_root));

    solver.shutdown().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn build_certificate_rejects_a_theorem_of_the_wrong_type() {
    let directory = support::TestDir::new("certificate_wrong_theorem_type");
    let (solver, solver_admission, snapshot) = fixed_core_snapshot(&directory, '7').await;
    let repository_root = support::repository_root();
    let pinned = PinnedLeancheckVampire::from_lock(&repository_root)
        .expect("the repository-pinned leancheck Vampire resolves");
    let cancellation = CancellationToken::new();
    let staging_root = directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    let destination = directory.path().join("Certificate");

    let hooks = CertificateBuildHooks {
        before_build: Some(Box::new(|stage: &Path| {
            let path = stage.join("src/Benchmark/Example0001/Certificate/Valid.lean");
            let contents = fs::read_to_string(&path).unwrap();
            let marker = "theorem input_hoare_triple_valid :";
            let start = contents
                .find(marker)
                .expect("Valid.lean carries the certificate theorem");
            let mut rewritten = contents[..start].to_string();
            rewritten.push_str("theorem input_hoare_triple_valid : True := trivial\n\n");
            rewritten.push_str("end Whiel.Benchmark.Example0001.Certificate\n");
            fs::write(&path, rewritten).unwrap();
        })),
        ..Default::default()
    };

    let error = build_certificate(CertificateBuildRequest {
        solver: &solver,
        admission: &solver_admission,
        snapshot,
        pinned: &pinned,
        profiles: &direct_profile,
        concurrency: sequential(),
        time_limit_seconds: 30,
        repository_root,
        staging_root: staging_root.clone(),
        destination,
        evidence_destination: None,
        cancellation: &cancellation,
        hooks,
    })
    .await
    .unwrap_err();
    match &error {
        CertificateBuildError::WrongTheoremType { diagnostics } => {
            assert!(
                diagnostics.contains("error:"),
                "expected an elaboration diagnostic in {diagnostics:?}"
            );
        }
        other => panic!("expected WrongTheoremType, got {other:?}"),
    }
    assert!(staging_is_empty(&staging_root));

    solver.shutdown().await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn build_certificate_rejects_a_non_std3_axiom_behind_an_imported_helper() {
    let directory = support::TestDir::new("certificate_non_std3_axiom");
    let (solver, solver_admission, snapshot) = fixed_core_snapshot(&directory, '8').await;
    let repository_root = support::repository_root();
    let pinned = PinnedLeancheckVampire::from_lock(&repository_root)
        .expect("the repository-pinned leancheck Vampire resolves");
    let cancellation = CancellationToken::new();
    let staging_root = directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    let destination = directory.path().join("Certificate");

    let hooks = CertificateBuildHooks {
        before_build: Some(Box::new(|stage: &Path| {
            let dependency =
                stage.join("src/Benchmark/Example0001/Certificate/ProposalBinding.lean");
            let mut source = fs::read_to_string(&dependency).unwrap();
            source.push_str("\naxiom hiddenCertificateHole : False\n");
            source.push_str("theorem importedCertificateHole : False := hiddenCertificateHole\n");
            fs::write(&dependency, source).unwrap();
            let path = stage.join("src/Benchmark/Example0001/Certificate/Valid.lean");
            let contents = fs::read_to_string(&path).unwrap();
            let marker = "theorem input_hoare_triple_valid :";
            let start = contents
                .find(marker)
                .expect("Valid.lean carries the certificate theorem");
            // ProposalBinding is checked independently and is not ordinarily
            // imported by Valid; make this fixture's dependency explicit.
            let mut rewritten =
                "import Benchmark.Example0001.Certificate.ProposalBinding\n".to_string();
            rewritten.push_str(&contents[..start]);
            rewritten.push_str("theorem input_hoare_triple_valid :\n");
            rewritten.push_str("    HoareValid inputPre inputCmd inputPost :=\n");
            rewritten.push_str("  importedCertificateHole.elim\n\n");
            rewritten.push_str("#print axioms input_hoare_triple_valid\n\n");
            rewritten.push_str("end Whiel.Benchmark.Example0001.Certificate\n");
            fs::write(&path, rewritten).unwrap();
        })),
        ..Default::default()
    };

    let error = build_certificate(CertificateBuildRequest {
        solver: &solver,
        admission: &solver_admission,
        snapshot,
        pinned: &pinned,
        profiles: &direct_profile,
        concurrency: sequential(),
        time_limit_seconds: 30,
        repository_root,
        staging_root: staging_root.clone(),
        destination: destination.clone(),
        evidence_destination: None,
        cancellation: &cancellation,
        hooks,
    })
    .await
    .unwrap_err();
    match &error {
        CertificateBuildError::Axioms { found } => {
            assert!(
                found
                    .iter()
                    .any(|axiom| axiom.contains("hiddenCertificateHole")),
                "{found:?}"
            );
        }
        other => panic!("expected Axioms, got {other:?}"),
    }
    assert!(staging_is_empty(&staging_root));
    assert!(!destination.exists());

    solver.shutdown().await.unwrap();
}

// ------------------------------------------------------------
// Search Profile Provenance
// ------------------------------------------------------------

/// The winning schedule of every condition a stabilized Example0001 search
/// proved by a launch of its own is `direct` under the fast fake Vampire,
/// and so is the run's configured profile, so every frozen job's label is
/// `direct`.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn provenance_reports_the_direct_search_winner_for_every_condition() {
    let directory = support::TestDir::new("provenance_direct");
    let (solver, _solver_admission, snapshot, _houdini, checker) =
        fixed_core_snapshot_with_checker(&directory, '9').await;

    let provenance = checker.search_profile_provenance(&snapshot);
    assert_eq!(provenance.configured(), ProofSearchProfile::Direct);
    // Both roles of both clauses, plus the termination conjecture.
    assert!(
        provenance.recorded_winners() >= 2 * snapshot.canonical_order().len(),
        "every launched condition records its winner: {}",
        provenance.recorded_winners()
    );
    for clause in snapshot.canonical_order() {
        let identity = snapshot.records()[clause].formula().identity_sha256();
        for role in [
            FrameworkIICheckRole::Initialization,
            FrameworkIICheckRole::Maintenance,
        ] {
            assert_eq!(
                provenance.clause_profile(role, identity),
                ProofSearchProfile::Direct,
                "clause {clause:?} role {role:?}"
            );
        }
    }
    assert_eq!(provenance.termination_profile(), ProofSearchProfile::Direct);

    drop(checker);
    solver.shutdown().await.unwrap();
}

/// A run whose launches are won by the CASC schedule records `casc_2025`
/// for exactly the conditions those launches closed, and leaves every
/// other condition on the run's configured profile.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn provenance_reports_the_casc_search_winner() {
    let directory = support::TestDir::new("provenance_casc");
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let bound = bind(worker_pool(1), 'a', None, &solver_admission, &cancellation).await;
    let (task, admission, solver, mut houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let clauses = admit(
        &admission,
        &[LEVEL_ZERO_CLAUSE],
        &solver_admission,
        &cancellation,
    )
    .await;
    register_and_enqueue(&mut houdini, &clauses);
    let identity = clauses[0].identity_sha256().to_string();

    let command = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args(["--fixture", "ladder-unknown-casc-proof"])
        .unwrap()
        .with_proof_casc_share(ProofCascShare::CLI_DEFAULT)
        .unwrap();
    let config = FrameworkIIProductionCheckConfig::new_proof_only_not_a_campaign_configuration(
        artifacts.clone(),
        solver_admission.clone(),
        VampireSearchBudget::finite(Duration::from_secs(5)),
        command,
        cancellation.clone(),
        "fixture-vampire",
        certification_profiles(),
    )
    .unwrap();
    // A run that has explicitly enabled the CASC portfolio: this test's
    // subject is what provenance records for a CASC-won launch, and since
    // the Milestone 7.5 review (finding 5) the portfolio is a run option
    // that is disabled by default, which would otherwise clear the CASC
    // share from every launch command of this run.
    let retry_policy = config
        .retry_policy()
        .clone()
        .with_casc_portfolio(CascPortfolioPolicy::Enabled);
    let mut checker = solver
        .clone()
        .production_checker(config.with_retry_policy(retry_policy));
    assert!(matches!(
        stabilize_leveled_houdini(&mut houdini, &mut checker)
            .await
            .unwrap(),
        LeveledStabilizationOutcome::Stabilized(_)
    ));

    let provenance = checker.search_profile_provenance(houdini.core().snapshot());
    assert_eq!(provenance.configured(), ProofSearchProfile::Direct);
    for role in [
        FrameworkIICheckRole::Initialization,
        FrameworkIICheckRole::Maintenance,
    ] {
        assert_eq!(
            provenance.clause_profile(role, &identity),
            ProofSearchProfile::Casc2025,
            "role {role:?}"
        );
    }
    // A clause identity this run never checked carries no winner and takes
    // the configured profile; there is no fallback between profiles.
    assert_eq!(
        provenance.clause_profile(FrameworkIICheckRole::Initialization, &"f".repeat(64)),
        ProofSearchProfile::Direct
    );

    drop(checker);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
    drop(artifacts);
    owner.settle().unwrap();
}

/// A checker that never ran a check records no winner at all, and its
/// configured profile is the run's host option rather than a built-in
/// default.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn provenance_before_any_check_is_the_configured_profile_alone() {
    let directory = support::TestDir::new("provenance_vacuous");
    let solver_admission = agent_admission(1, 1);
    let cancellation = CancellationToken::new();
    let bound = bind(worker_pool(1), 'b', None, &solver_admission, &cancellation).await;
    let (task, admission, solver, houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let config = FrameworkIIProductionCheckConfig::new(
        artifacts.clone(),
        solver_admission.clone(),
        VampireSearchBudget::finite(Duration::from_secs(5)),
        FmbOptions::default(),
        VampireWorkerCommand::new(support::fake_vampire()),
        cancellation.clone(),
        "fixture-vampire",
        certification_profiles(),
    )
    .unwrap()
    .with_search_profile(ProofSearchProfile::Casc2025);
    let checker = solver.clone().production_checker(config);

    // Nothing was ever checked, so the Core this provenance is read against
    // is the run's own empty one.
    let provenance = checker.search_profile_provenance(houdini.core().snapshot());
    assert_eq!(provenance.recorded_winners(), 0);
    assert_eq!(provenance.configured(), ProofSearchProfile::Casc2025);
    assert_eq!(
        provenance.clause_profile(FrameworkIICheckRole::Maintenance, &"a".repeat(64)),
        ProofSearchProfile::Casc2025
    );
    assert_eq!(
        provenance.termination_profile(),
        ProofSearchProfile::Casc2025
    );
    // `SearchProfileProvenance` stays a public, constructible type.
    let configured_only = SearchProfileProvenance::configured_only(ProofSearchProfile::Direct);
    assert_eq!(configured_only.recorded_winners(), 0);

    drop(checker);
    solver.shutdown().await.unwrap();
    drop(solver);
    drop(admission);
    drop(artifacts);
    owner.settle().unwrap();
}

// ------------------------------------------------------------
// Pass 7.5f: Freezing And Certifying The Exact Batch
// ------------------------------------------------------------

/// One live, frozen Example0001 Core with every authority the
/// certification needs still alive.
///
/// The Core is produced by a real proposal epoch, so the termination check
/// that authorizes the freeze is the run's own — there is no way to freeze
/// a Core without one.
struct FrozenFixture {
    solver: FrameworkIISolverContext,
    admission: whiel_runner::FrameworkIIAdmissionContext,
    solver_admission: SolverAdmission,
    houdini: LeveledHoudiniState,
    checker: FrameworkIIProductionChecker<FrameworkIISolverContext>,
    frozen: FrozenLeveledCore,
}

async fn frozen_example0001(directory: &support::TestDir, catalog_digit: char) -> FrozenFixture {
    frozen_example0001_under(directory, catalog_digit, CascPortfolioPolicy::Disabled).await
}

/// [`frozen_example0001`] under an explicit [`CascPortfolioPolicy`].
///
/// The default is `Disabled`, which is the run default; a test whose
/// subject is a `casc_2025`-labelled job passes `Enabled`, so the frozen
/// record it certifies comes from a run that really had the portfolio on.
async fn frozen_example0001_under(
    directory: &support::TestDir,
    catalog_digit: char,
    casc_portfolio: CascPortfolioPolicy,
) -> FrozenFixture {
    let solver_admission = agent_admission(2, 1);
    let cancellation = CancellationToken::new();
    // No level bound at all, exactly as the agent path runs: the scan's
    // halting rule, not a bound, ends stabilization.
    let bound = bind(
        worker_pool(1),
        catalog_digit,
        None,
        &solver_admission,
        &cancellation,
    )
    .await;
    let (task, admission, solver, mut houdini) = bound.into_parts();
    let (owner, artifacts) =
        new_artifact_store(&task, ArtifactStoreConfig::new(directory.path())).unwrap();
    let clauses = admit(
        &admission,
        &[LEVEL_ZERO_CLAUSE, LEVEL_ONE_CLAUSE],
        &solver_admission,
        &cancellation,
    )
    .await;

    let command = VampireWorkerCommand::new(support::fake_vampire())
        .with_extra_args(["--fixture", "race-proof-fast"])
        .unwrap();
    let config = FrameworkIIProductionCheckConfig::new(
        artifacts.clone(),
        solver_admission.clone(),
        VampireSearchBudget::finite(Duration::from_secs(5)),
        FmbOptions::default(),
        command,
        cancellation.clone(),
        "fixture-vampire",
        certification_profiles(),
    )
    .unwrap();
    let retry_policy = config
        .retry_policy()
        .clone()
        .with_casc_portfolio(casc_portfolio);
    let mut checker = solver
        .clone()
        .production_checker(config.with_retry_policy(retry_policy));

    let proposal = FrameworkIIProposalEpoch::new(
        houdini.proposal_context().unwrap(),
        clauses.iter().cloned(),
        [],
    )
    .unwrap();
    let result = run_framework_ii_proposal_epoch(&mut houdini, &mut checker, proposal)
        .await
        .unwrap();
    let FrameworkIIEpochOutcome::Proved { core, termination } = result.into_outcome() else {
        panic!("the fast proof fixture must prove Example0001's termination check");
    };
    let frozen = FrozenLeveledCore::freeze(
        &core,
        admission.scope(),
        &termination,
        &checker.search_profile_provenance(core.snapshot()),
    )
    .expect("a proved termination check freezes its own Core");
    assert_eq!(frozen.core_size(), 2);
    assert_eq!(frozen.condition_count(), 5);
    // The artifact owner outlives its settlement point here; the test
    // directory removes the whole tree.
    std::mem::forget(owner);

    FrozenFixture {
        solver,
        admission,
        solver_admission,
        houdini,
        checker,
        frozen,
    }
}

fn certify_request<'a>(
    fixture: &'a FrozenFixture,
    frozen: &'a FrozenLeveledCore,
    pinned: &'a PinnedLeancheckVampire,
    cancellation: &'a CancellationToken,
    directory: &support::TestDir,
    certification_limit: Duration,
    hooks: CertificateBuildHooks,
) -> CertifyFrozenCoreRequest<'a> {
    certify_request_with_evidence(
        fixture,
        frozen,
        pinned,
        cancellation,
        directory,
        certification_limit,
        hooks,
        None,
    )
}

/// As [`certify_request`], but names where the batch's solver evidence
/// should be moved (`Some`) or dropped (`None`, what every other caller of
/// [`certify_request`] wants).
#[allow(clippy::too_many_arguments)]
fn certify_request_with_evidence<'a>(
    fixture: &'a FrozenFixture,
    frozen: &'a FrozenLeveledCore,
    pinned: &'a PinnedLeancheckVampire,
    cancellation: &'a CancellationToken,
    directory: &support::TestDir,
    certification_limit: Duration,
    hooks: CertificateBuildHooks,
    evidence_destination: Option<PathBuf>,
) -> CertifyFrozenCoreRequest<'a> {
    let staging_root = directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();
    CertifyFrozenCoreRequest {
        frozen,
        admission: &fixture.admission,
        solver: &fixture.solver,
        solver_admission: &fixture.solver_admission,
        catalog: fixture.houdini.catalog(),
        pinned,
        time_limit_seconds: 30,
        certification_limit,
        concurrency: DEFAULT_CERTIFICATION_CONCURRENCY,
        repository_root: support::repository_root(),
        staging_root,
        private_root: directory.path().join("private"),
        evidence_destination,
        cancellation,
        hooks,
    }
}

/// The whole pass, live: a proved termination check freezes the Core, the
/// frozen input and clauses are re-admitted, and all `2N+1` conditions are
/// launched afresh through the Pass-7.4 coordinator under one independent
/// deadline with bounded concurrency. The aggregate elaborates at the exact
/// input-schema Hoare triple and audits to exact std3, and it stays
/// private: nothing is published and no public `Valid` is produced.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn certifying_a_frozen_core_reproves_every_one_of_its_conditions() {
    let directory = support::TestDir::new("certify_frozen_core");
    let fixture = frozen_example0001(&directory, '1').await;
    let pinned = PinnedLeancheckVampire::from_lock(&support::repository_root())
        .expect("the repository-pinned leancheck Vampire resolves");
    let cancellation = CancellationToken::new();

    let candidate = certify_frozen_core(certify_request(
        &fixture,
        &fixture.frozen,
        &pinned,
        &cancellation,
        &directory,
        Duration::from_secs(600),
        CertificateBuildHooks::default(),
    ))
    .await
    .expect("the frozen Example0001 Core certifies");

    // Exactly 2N+1: two initialization, two step, one termination. Nothing
    // is skipped because the search already had evidence for it.
    assert_eq!(candidate.condition_count(), 5);
    assert_eq!(candidate.frozen().condition_count(), 5);
    let receipts = &candidate.receipt().jobs;
    let ids = receipts
        .iter()
        .map(|job| job.id.as_str())
        .collect::<Vec<_>>();
    let mut sorted = ids.clone();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(sorted.len(), 5, "no job is solved twice: {ids:?}");
    for job in JOB_IDS {
        assert!(ids.contains(&job), "job {job} is missing from {ids:?}");
    }
    let mut by_ordinal = receipts.iter().collect::<Vec<_>>();
    by_ordinal.sort_by_key(|job| job.ordinal);
    assert_eq!(
        by_ordinal
            .iter()
            .map(|job| (job.ordinal, job.role.as_str()))
            .collect::<Vec<_>>(),
        vec![
            (0, "initialization"),
            (1, "initialization"),
            (2, "maintenance"),
            (3, "maintenance"),
            (4, "termination"),
        ]
    );
    for (index, row) in fixture.frozen.rows().iter().enumerate() {
        assert_eq!(by_ordinal[index].clause_id, Some(row.clause_id()));
        assert_eq!(by_ordinal[index].level, Some(row.level()));
        assert_eq!(by_ordinal[index + 2].clause_id, Some(row.clause_id()));
        assert_eq!(by_ordinal[index + 2].level, Some(row.level()));
        assert_eq!(
            by_ordinal[index].profile.profile(),
            row.initialization_profile()
        );
        assert_eq!(by_ordinal[index + 2].profile.profile(), row.step_profile());
    }
    assert_eq!(by_ordinal[4].clause_id, None);
    assert_eq!(
        by_ordinal[4].profile.profile(),
        fixture.frozen.termination_profile()
    );

    // The exact std3 closure, and nothing else.
    let mut axioms = candidate.axioms().to_vec();
    axioms.sort();
    assert_eq!(
        axioms,
        vec!["Classical.choice", "Quot.sound", "propext"]
            .into_iter()
            .map(String::from)
            .collect::<Vec<_>>()
    );

    // Private, not published: the tree lives under the caller's private
    // root and is removed when the candidate is dropped.
    let tree = candidate.private_tree().to_path_buf();
    assert!(tree.starts_with(directory.path().join("private")));
    assert!(tree.join("Certificate").is_dir());
    let staging_root = directory.path().join("staging");
    assert!(staging_is_empty(&staging_root));
    drop(candidate);
    assert!(
        !tree.exists(),
        "a dropped candidate removes its private tree"
    );

    drop(fixture.checker);
    fixture.solver.shutdown().await.unwrap();
}

/// A frozen record is frozen: certification never continues onto one that
/// names another task, and every identity, level, and order disagreement
/// with the live catalog fails closed before a single solver runs.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn certification_refuses_a_stale_or_drifted_frozen_record() {
    let directory = support::TestDir::new("certify_drift");
    let fixture = frozen_example0001(&directory, '2').await;
    let pinned = PinnedLeancheckVampire::from_lock(&support::repository_root())
        .expect("the repository-pinned leancheck Vampire resolves");
    let cancellation = CancellationToken::new();

    async fn refuse(
        fixture: &FrozenFixture,
        frozen: &FrozenLeveledCore,
        pinned: &PinnedLeancheckVampire,
        cancellation: &CancellationToken,
        directory: &support::TestDir,
    ) -> AggregateCertificationError {
        certify_frozen_core(certify_request(
            fixture,
            frozen,
            pinned,
            cancellation,
            directory,
            Duration::from_secs(60),
            CertificateBuildHooks::default(),
        ))
        .await
        .expect_err("a stale or drifted frozen record never certifies")
    }

    // A record continued from another run's task.
    let mut payload = fixture.frozen.payload();
    payload["task_canonical_id"] = Value::from("Example0013");
    let payload = FrozenLeveledCore::signed_payload(&payload);
    let stale = FrozenLeveledCore::from_payload(&payload).unwrap();
    let error = refuse(&fixture, &stale, &pinned, &cancellation, &directory).await;
    assert!(
        matches!(error, AggregateCertificationError::StaleFrozenRecord { .. }),
        "{error}"
    );

    // A record whose row claims another Lean-issued identity.
    let mut payload = fixture.frozen.payload();
    payload["rows"][0]["identity_sha256"] = Value::from("e".repeat(64));
    let payload = FrozenLeveledCore::signed_payload(&payload);
    let drifted = FrozenLeveledCore::from_payload(&payload).unwrap();
    let error = refuse(&fixture, &drifted, &pinned, &cancellation, &directory).await;
    assert!(
        matches!(error, AggregateCertificationError::IdentityDrift { .. }),
        "{error}"
    );

    // A record whose row claims another level: the rebuilt Core is not the
    // frozen partition.
    let mut payload = fixture.frozen.payload();
    let bumped = payload["rows"][1]["level"].as_u64().unwrap() + 1;
    payload["rows"][1]["level"] = Value::from(bumped);
    let payload = FrozenLeveledCore::signed_payload(&payload);
    let relevelled = FrozenLeveledCore::from_payload(&payload).unwrap();
    let error = refuse(&fixture, &relevelled, &pinned, &cancellation, &directory).await;
    assert!(
        matches!(
            error,
            AggregateCertificationError::LevelDrift { .. }
                | AggregateCertificationError::PartitionDrift
        ),
        "{error}"
    );

    // Nothing was built for any of them.
    assert!(!directory.path().join("private").exists());

    drop(fixture.checker);
    fixture.solver.shutdown().await.unwrap();
}

/// The certification's own deadline is independent of the run's: when it
/// expires the batch is closed, no leancheck child survives, the
/// coordinator's staging tree is gone, and no private tree is left behind.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn certification_stops_on_its_own_deadline_and_leaves_nothing_behind() {
    let directory = support::TestDir::new("certify_deadline");
    let fixture = frozen_example0001(&directory, '3').await;
    let script = directory.path().join("slow-leancheck.sh");
    fs::write(&script, "#!/bin/sh\nsleep 600\n").unwrap();
    set_executable(&script);
    let sha256 = sha256_hex(&fs::read(&script).unwrap());
    let pinned = PinnedLeancheckVampire::unverified_for_tests(script.clone(), sha256);
    let cancellation = CancellationToken::new();

    let error = certify_frozen_core(certify_request(
        &fixture,
        &fixture.frozen,
        &pinned,
        &cancellation,
        &directory,
        Duration::from_millis(300),
        CertificateBuildHooks::default(),
    ))
    .await
    .unwrap_err();
    assert!(
        matches!(error, AggregateCertificationError::DeadlineExpired(_)),
        "{error}"
    );
    assert!(staging_is_empty(&directory.path().join("staging")));
    assert!(
        fs::read_dir(directory.path().join("private"))
            .unwrap()
            .next()
            .is_none(),
        "a failed certification leaves no private tree"
    );
    assert!(no_such_process(&script));

    drop(fixture.checker);
    fixture.solver.shutdown().await.unwrap();
}

/// The run's own cancellation stops a certification in flight, and it is
/// reported as an interruption rather than as a deadline.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn certification_stops_on_the_runs_cancellation() {
    let directory = support::TestDir::new("certify_cancelled");
    let fixture = frozen_example0001(&directory, '4').await;
    let script = directory.path().join("slow-leancheck.sh");
    fs::write(&script, "#!/bin/sh\nsleep 600\n").unwrap();
    set_executable(&script);
    let sha256 = sha256_hex(&fs::read(&script).unwrap());
    let pinned = PinnedLeancheckVampire::unverified_for_tests(script.clone(), sha256);
    let cancellation = CancellationToken::new();
    let canceller = cancellation.clone();
    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_millis(400)).await;
        canceller.cancel();
    });

    let error = certify_frozen_core(certify_request(
        &fixture,
        &fixture.frozen,
        &pinned,
        &cancellation,
        &directory,
        Duration::from_secs(600),
        CertificateBuildHooks::default(),
    ))
    .await
    .unwrap_err();
    assert!(
        matches!(error, AggregateCertificationError::Interrupted),
        "{error}"
    );
    assert!(staging_is_empty(&directory.path().join("staging")));
    assert!(no_such_process(&script));

    // Restart: the cancelled attempt left the frozen record, the catalog,
    // and the private root exactly as it found them, so a fresh
    // certification of the same frozen Core succeeds.
    let pinned = PinnedLeancheckVampire::from_lock(&support::repository_root())
        .expect("the repository-pinned leancheck Vampire resolves");
    let restart = CancellationToken::new();
    let candidate = certify_frozen_core(certify_request(
        &fixture,
        &fixture.frozen,
        &pinned,
        &restart,
        &directory,
        Duration::from_secs(600),
        CertificateBuildHooks::default(),
    ))
    .await
    .expect("a restart after a cancelled certification certifies the same frozen Core");
    assert_eq!(candidate.condition_count(), 5);
    drop(candidate);

    drop(fixture.checker);
    fixture.solver.shutdown().await.unwrap();
}

/// Every job runs under its own frozen label and no other.
///
/// A mixed batch labels `init_clause_0` and the termination check
/// `casc_2025` and the remaining three `direct`, under a run that has the
/// CASC portfolio enabled. Both labels certify, each under its own
/// schedule, and the certification never retries a job under the other
/// one. Before the toolchain's `0002` patch this test accepted a
/// fail-closed outcome as well, because the pinned emitter rendered the
/// definition symbols the CASC schedule introduces at an arity the
/// generated proof could not elaborate at; it now requires success, which
/// is the live half of the mixed-profile rule for `casc_2025`.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_mixed_profile_batch_runs_each_job_under_its_own_label_and_never_falls_back() {
    let directory = support::TestDir::new("certify_mixed_profile");
    let fixture = frozen_example0001_under(&directory, '6', CascPortfolioPolicy::Enabled).await;
    let pinned = PinnedLeancheckVampire::from_lock(&support::repository_root())
        .expect("the repository-pinned leancheck Vampire resolves");
    let cancellation = CancellationToken::new();

    let mut payload = fixture.frozen.payload();
    payload["rows"][0]["initialization_profile"] = Value::from("casc_2025");
    payload["termination_profile"] = Value::from("casc_2025");
    let payload = FrozenLeveledCore::signed_payload(&payload);
    let mixed = FrozenLeveledCore::from_payload(&payload).unwrap();
    assert_eq!(
        mixed.rows()[0].initialization_profile(),
        ProofSearchProfile::Casc2025
    );
    assert_eq!(mixed.rows()[0].step_profile(), ProofSearchProfile::Direct);
    assert_eq!(mixed.termination_profile(), ProofSearchProfile::Casc2025);

    let outcome = certify_frozen_core(certify_request(
        &fixture,
        &mixed,
        &pinned,
        &cancellation,
        &directory,
        Duration::from_secs(900),
        CertificateBuildHooks::default(),
    ))
    .await;
    let candidate = outcome.expect("a mixed-profile batch certifies under both labels");
    let mut by_ordinal = candidate.receipt().jobs.iter().collect::<Vec<_>>();
    by_ordinal.sort_by_key(|job| job.ordinal);
    assert_eq!(
        by_ordinal
            .iter()
            .map(|job| job.profile.profile())
            .collect::<Vec<_>>(),
        vec![
            ProofSearchProfile::Casc2025,
            ProofSearchProfile::Direct,
            ProofSearchProfile::Direct,
            ProofSearchProfile::Direct,
            ProofSearchProfile::Casc2025,
        ]
    );
    drop(candidate);
    // Published nothing, kept nothing.
    assert!(staging_is_empty(&directory.path().join("staging")));
    assert!(
        fs::read_dir(directory.path().join("private"))
            .unwrap()
            .next()
            .is_none()
    );

    drop(fixture.checker);
    fixture.solver.shutdown().await.unwrap();
}

/// A failing axiom audit is a failed certification: no candidate exists,
/// nothing is published, and the private tree is not left behind.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_failed_axiom_audit_produces_no_candidate() {
    let directory = support::TestDir::new("certify_audit_failure");
    let fixture = frozen_example0001(&directory, '5').await;
    let pinned = PinnedLeancheckVampire::from_lock(&support::repository_root())
        .expect("the repository-pinned leancheck Vampire resolves");
    let cancellation = CancellationToken::new();
    let hooks = CertificateBuildHooks {
        before_build: Some(Box::new(|stage: &Path| {
            let path = stage.join("src/Benchmark/Example0001/Certificate/Valid.lean");
            let contents = fs::read_to_string(&path).unwrap();
            let marker = "theorem input_hoare_triple_valid :";
            let start = contents
                .find(marker)
                .expect("Valid.lean carries the certificate theorem");
            let mut rewritten = contents[..start].to_string();
            rewritten.push_str("axiom certificateHole : False\n\n");
            rewritten.push_str("theorem input_hoare_triple_valid :\n");
            rewritten.push_str("    HoareValid inputPre inputCmd inputPost :=\n");
            rewritten.push_str("  certificateHole.elim\n\n");
            rewritten.push_str("end Whiel.Benchmark.Example0001.Certificate\n");
            fs::write(&path, rewritten).unwrap();
        })),
        ..CertificateBuildHooks::default()
    };

    let error = certify_frozen_core(certify_request(
        &fixture,
        &fixture.frozen,
        &pinned,
        &cancellation,
        &directory,
        Duration::from_secs(600),
        hooks,
    ))
    .await
    .unwrap_err();
    assert!(
        matches!(error, AggregateCertificationError::Build(_)),
        "{error}"
    );
    assert!(staging_is_empty(&directory.path().join("staging")));
    assert!(
        fs::read_dir(directory.path().join("private"))
            .unwrap()
            .next()
            .is_none()
    );

    drop(fixture.checker);
    fixture.solver.shutdown().await.unwrap();
}

// ------------------------------------------------------------
// Pass 7.5g: Revalidation And Atomic Publication
// ------------------------------------------------------------

/// Publish one checked aggregate candidate, from a live frozen Core.
///
/// Everything before the publication is Pass 7.5f's: a real proposal epoch
/// proves the termination check, the proof freezes the Core, and every one
/// of its `2N+1` conditions is re-proved by the real pinned leancheck
/// Vampire into a private tree. This exercises what Pass 7.5g adds on top:
/// a destination is claimed once, the revalidation has to succeed before
/// the tree may authorize a `Valid` result, and the publication itself is
/// one rename.
///
/// It also exercises the evidence side of the same shape (A1): the first
/// certification names an evidence destination and moves its batch's
/// evidence there *before* publication is even attempted, so when the
/// occupied destination refuses that publication, the evidence a failed
/// candidate already wrote would leak and block a second certification of
/// the same frozen Core — unless dropping the never-retained candidate
/// also removes it, which is what is asserted below. The second
/// certification then reuses the very same evidence path and succeeds.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn publishing_a_valid_result_revalidates_the_candidate_before_the_rename() {
    let directory = support::TestDir::new("publish_valid");
    let fixture = frozen_example0001(&directory, '7').await;
    let pinned = PinnedLeancheckVampire::from_lock(&support::repository_root())
        .expect("the repository-pinned leancheck Vampire resolves");
    let cancellation = CancellationToken::new();
    let staging_root = directory.path().join("publish-staging");
    fs::create_dir_all(&staging_root).unwrap();
    let destination = directory.path().join("published").join("Certificate");
    let evidence = directory.path().join("Evidence");

    // A destination that already exists is refused before any Lean runs, so
    // a published result is never silently replaced — and the refused
    // candidate's private tree goes with it, leaving no source behind that
    // a later step could mistake for authority.
    fs::create_dir_all(&destination).unwrap();
    let candidate = certify_frozen_core(certify_request_with_evidence(
        &fixture,
        &fixture.frozen,
        &pinned,
        &cancellation,
        &directory,
        Duration::from_secs(900),
        CertificateBuildHooks::default(),
        Some(evidence.clone()),
    ))
    .await
    .expect("the frozen Example0001 Core certifies");
    // The certification's own build already moved the batch's evidence out,
    // well before publication is ever attempted.
    assert!(fs::metadata(evidence.join("jobs/term_check/problem.p")).is_ok_and(|m| m.len() > 0));
    let refused_tree = candidate.private_tree().to_path_buf();
    let error = publish_valid(PublishValidRequest {
        space_guard: None,
        candidate,
        canonical_id: "Example0001",
        input_namespace: "Whiel.Benchmark.Example0001",
        repository_root: support::repository_root(),
        staging_root: staging_root.clone(),
        destination: destination.clone(),
    })
    .await
    .expect_err("an occupied destination is never published into");
    assert!(
        matches!(&error, PublicationError::DestinationExists(path) if path == &destination),
        "{error}"
    );
    assert!(!refused_tree.exists());
    // The refused candidate was never retained, so dropping it also removed
    // the evidence its own build already wrote — exactly as it removed the
    // private tree — and a second certification of the same frozen Core,
    // reusing the very same evidence path, is not blocked by a leftover.
    assert!(
        !evidence.exists(),
        "a candidate that never published removes the evidence it moved out"
    );
    fs::remove_dir_all(&destination).unwrap();

    let candidate = certify_frozen_core(certify_request_with_evidence(
        &fixture,
        &fixture.frozen,
        &pinned,
        &cancellation,
        &directory,
        Duration::from_secs(900),
        CertificateBuildHooks::default(),
        Some(evidence.clone()),
    ))
    .await
    .expect("the frozen Example0001 Core certifies again, reusing the same evidence path");
    let private_tree = candidate.private_tree().to_path_buf();
    let published = publish_valid(PublishValidRequest {
        space_guard: None,
        candidate,
        canonical_id: "Example0001",
        input_namespace: "Whiel.Benchmark.Example0001",
        repository_root: support::repository_root(),
        staging_root: staging_root.clone(),
        destination: destination.clone(),
    })
    .await
    .expect("a checked candidate revalidates and publishes");

    // The publication is the rename of a complete tree: every module the
    // candidate carried is there, and the private tree is gone.
    assert_eq!(published.certificate(), destination);
    assert!(destination.join("Valid.lean").is_file());
    assert!(!private_tree.join("Certificate").exists());
    // `Check.lean` is a build-time scratch module and never rides along.
    assert!(!destination.join("Check.lean").exists());
    assert!(staging_is_empty(&staging_root));
    // Evidence was retained this time — the publication that used it
    // succeeded — and the published tree itself carries none of it.
    assert!(fs::metadata(evidence.join("jobs/term_check/problem.p")).is_ok_and(|m| m.len() > 0));
    assert!(!destination.join("VampireArtifacts").exists());
    assert!(destination.join("timing.csv").is_file());

    // The revalidation is what authorized it: a fresh Lean build of every
    // module, the theorem elaborated at the exact input-schema type, and an
    // exact-std3 audit.
    let mut axioms = published.revalidation().axioms.clone();
    axioms.sort();
    assert_eq!(axioms, vec!["Classical.choice", "Quot.sound", "propext"]);
    assert!(
        published
            .revalidation()
            .modules
            .contains(&"Benchmark.Example0001.Certificate.Valid".to_string())
    );
    assert_eq!(published.revalidation().source_digest.len(), 64);
    assert_eq!(
        published.receipt().certificate_module,
        "Benchmark.Example0001.Certificate.Valid"
    );
    assert_eq!(published.receipt().shape, CertificateBundleShape::Valid);

    // The published source revalidates again on its own, with no candidate,
    // no receipt, and no private tree behind it: authority is the fresh
    // Lean check, never the bytes' provenance.
    let again = revalidate_certificate_tree(CertificateRevalidationRequest {
        tree: &destination,
        canonical_id: "Example0001",
        input_namespace: "Whiel.Benchmark.Example0001",
        certificate_module: &published.receipt().certificate_module,
        certificate_theorem: &published.receipt().certificate_theorem,
        shape: CertificateBundleShape::Valid,
        repository_root: support::repository_root(),
        staging_root: staging_root.clone(),
        cancellation: &cancellation,
    })
    .await
    .expect("the published source revalidates on its own");
    assert_eq!(
        again.source_digest,
        published.revalidation().source_digest,
        "revalidating the same bytes names the same source"
    );
    assert!(staging_is_empty(&staging_root));

    drop(fixture.checker);
    fixture.solver.shutdown().await.unwrap();
}

/// No written source authorizes a result for the bytes it carries. A
/// certificate tree whose theorem has been replaced by an axiom is refused
/// by the revalidation's own std3 audit, and a tree whose theorem no longer
/// states the input triple is refused by the exact type check — even though
/// both were produced by a build that had already passed once.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn a_tampered_certificate_source_never_revalidates() {
    let directory = support::TestDir::new("revalidate_tampered");
    let cancellation = CancellationToken::new();
    let staging_root = directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();

    // The checked-in Example0001 tree, copied so the checkout is untouched.
    let checked_in = support::repository_root().join("Benchmark/Example0001/Certificate");
    let tree = directory.path().join("Certificate");
    copy_tree(&checked_in, &tree);

    fn request<'a>(
        tree: &'a Path,
        staging_root: &Path,
        cancellation: &'a CancellationToken,
    ) -> CertificateRevalidationRequest<'a> {
        CertificateRevalidationRequest {
            tree,
            canonical_id: "Example0001",
            input_namespace: "Whiel.Benchmark.Example0001",
            certificate_module: "Benchmark.Example0001.Certificate.Valid",
            certificate_theorem: "Whiel.Benchmark.Example0001.Certificate.input_hoare_triple_valid",
            shape: CertificateBundleShape::Valid,
            repository_root: support::repository_root(),
            staging_root: staging_root.to_path_buf(),
            cancellation,
        }
    }

    // Untampered, the checked-in tree revalidates.
    let clean = revalidate_certificate_tree(request(&tree, &staging_root, &cancellation))
        .await
        .expect("the checked-in Example0001 certificate revalidates");
    let mut axioms = clean.axioms.clone();
    axioms.sort();
    assert_eq!(axioms, vec!["Classical.choice", "Quot.sound", "propext"]);

    // An axiom hole in place of the theorem's proof: the type still
    // elaborates, so only the audit catches it.
    let holed = directory.path().join("CertificateHoled");
    copy_tree(&tree, &holed);
    let valid = holed.join("Valid.lean");
    let contents = fs::read_to_string(&valid).unwrap();
    let marker = "theorem input_hoare_triple_valid";
    let start = contents
        .find(marker)
        .expect("Valid.lean carries the certificate theorem");
    let mut rewritten = contents[..start].to_string();
    rewritten.push_str("axiom certificateHole : False\n\n");
    rewritten.push_str("theorem input_hoare_triple_valid :\n");
    rewritten.push_str("    HoareValid inputPre inputCmd inputPost :=\n");
    rewritten.push_str("  certificateHole.elim\n\n");
    rewritten.push_str("end Whiel.Benchmark.Example0001.Certificate\n");
    fs::write(&valid, rewritten).unwrap();
    let error = revalidate_certificate_tree(request(&holed, &staging_root, &cancellation))
        .await
        .expect_err("an axiom hole never revalidates");
    match error {
        CertificateBuildError::Axioms { found } => {
            assert!(
                found.iter().any(|axiom| axiom.contains("certificateHole")),
                "{found:?}"
            );
        }
        other => panic!("expected an axiom audit failure, got {other}"),
    }

    // The whole `Valid` module removed: the tree no longer carries the
    // module the theorem lives in, and nothing is elaborated at all.
    let missing = directory.path().join("CertificateMissing");
    copy_tree(&tree, &missing);
    fs::remove_file(missing.join("Valid.lean")).unwrap();
    let error = revalidate_certificate_tree(request(&missing, &staging_root, &cancellation))
        .await
        .expect_err("a tree without its theorem module never revalidates");
    assert!(
        matches!(&error, CertificateBuildError::Io(detail) if detail.contains("Valid")),
        "{error}"
    );
    assert!(staging_is_empty(&staging_root));
}

/// There is no certificate-source cache that can authorize a result.
///
/// A retained certification tree is the only certificate source a run ever
/// holds across steps, and it cannot be reused: certifying the same frozen
/// Core again under the same private root is refused outright rather than
/// adopting the tree that is already there, and the retained tree itself is
/// left exactly as it was.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn no_retained_certification_tree_is_reused_as_a_second_results_source() {
    let directory = support::TestDir::new("no_certificate_cache");
    let fixture = frozen_example0001(&directory, '9').await;
    let pinned = PinnedLeancheckVampire::from_lock(&support::repository_root())
        .expect("the repository-pinned leancheck Vampire resolves");
    let cancellation = CancellationToken::new();

    let mut candidate = certify_frozen_core(certify_request(
        &fixture,
        &fixture.frozen,
        &pinned,
        &cancellation,
        &directory,
        Duration::from_secs(900),
        CertificateBuildHooks::default(),
    ))
    .await
    .expect("the frozen Example0001 Core certifies");
    candidate.retain();
    let tree = candidate.private_tree().to_path_buf();
    let before = fs::read_to_string(tree.join("Certificate/Valid.lean")).unwrap();
    drop(candidate);
    assert!(tree.exists(), "a retained tree survives its candidate");

    let error = certify_frozen_core(certify_request(
        &fixture,
        &fixture.frozen,
        &pinned,
        &cancellation,
        &directory,
        Duration::from_secs(900),
        CertificateBuildHooks::default(),
    ))
    .await
    .expect_err("a retained tree is never adopted as a second certification");
    assert!(
        matches!(&error, AggregateCertificationError::PrivateTreeExists(path) if path == &tree),
        "{error}"
    );
    assert_eq!(
        fs::read_to_string(tree.join("Certificate/Valid.lean")).unwrap(),
        before,
        "the refusal leaves the retained tree untouched"
    );

    drop(fixture.checker);
    fixture.solver.shutdown().await.unwrap();
}

/// Pass 7.5g review, finding 1: nothing outside the tree may resolve an
/// import in the certificate's own namespace.
///
/// The repository's `.lake` build directory ordinarily carries compiled
/// `olean` files for exactly this namespace, left there by an earlier `lake
/// build`, and it sits on the search path revalidation inherits. A tree
/// missing one of its own non-root reconstruction modules would otherwise
/// compile against that stale artifact and be revalidated on evidence it
/// does not contain. This asserts the stale `olean` is really there, so the
/// test fails if the premise stops holding rather than passing vacuously.
///
/// A symlinked module is the same defect by another route: the entry is
/// neither a directory nor a regular file, so it would silently leave the
/// compiled set. Both are refused, and both before any Lean runs.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn a_tree_that_is_not_its_own_source_never_revalidates() {
    let directory = support::TestDir::new("revalidate_incomplete_tree");
    let cancellation = CancellationToken::new();
    let staging_root = directory.path().join("staging");
    fs::create_dir_all(&staging_root).unwrap();

    let repository_root = support::repository_root();
    let checked_in = repository_root.join("Benchmark/Example0001/Certificate");
    let stale_olean = repository_root
        .join(".lake/build/lib/lean/Benchmark/Example0001/Certificate/Reconstructions")
        .join("InitClause0.olean");
    assert!(
        stale_olean.is_file(),
        "this test is only meaningful while {} exists; run `lake build Benchmark` first",
        stale_olean.display()
    );

    fn request<'a>(
        tree: &'a Path,
        staging_root: &Path,
        cancellation: &'a CancellationToken,
    ) -> CertificateRevalidationRequest<'a> {
        CertificateRevalidationRequest {
            tree,
            canonical_id: "Example0001",
            input_namespace: "Whiel.Benchmark.Example0001",
            certificate_module: "Benchmark.Example0001.Certificate.Valid",
            certificate_theorem: "Whiel.Benchmark.Example0001.Certificate.input_hoare_triple_valid",
            shape: CertificateBundleShape::Valid,
            repository_root: support::repository_root(),
            staging_root: staging_root.to_path_buf(),
            cancellation,
        }
    }

    // One non-root reconstruction module removed. `Valid.lean` still
    // imports it, and no stale `olean` may answer for it.
    let incomplete = directory.path().join("CertificateIncomplete");
    copy_tree(&checked_in, &incomplete);
    fs::remove_file(incomplete.join("Reconstructions/InitClause0.lean")).unwrap();
    let error = revalidate_certificate_tree(request(&incomplete, &staging_root, &cancellation))
        .await
        .expect_err("a tree missing one of its own modules never revalidates");
    assert!(
        matches!(
            &error,
            CertificateBuildError::UnresolvedCertificateImport { importer, module }
                if importer == "Benchmark.Example0001.Certificate.Valid"
                    && module == "Benchmark.Example0001.Certificate.Reconstructions.InitClause0"
        ),
        "{error}"
    );

    // The same module present only as a symlink to the checked-in file.
    let linked = directory.path().join("CertificateLinked");
    copy_tree(&checked_in, &linked);
    let module = linked.join("Reconstructions/InitClause0.lean");
    fs::remove_file(&module).unwrap();
    std::os::unix::fs::symlink(checked_in.join("Reconstructions/InitClause0.lean"), &module)
        .unwrap();
    let error = revalidate_certificate_tree(request(&linked, &staging_root, &cancellation))
        .await
        .expect_err("a symlinked module never revalidates");
    assert!(
        matches!(&error, CertificateBuildError::NonRegularTreeEntry { path }
            if path.ends_with("InitClause0.lean")),
        "{error}"
    );

    // Neither refusal ran Lean at all, so nothing was staged.
    assert!(staging_is_empty(&staging_root));
}

fn copy_tree(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let target = to.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_tree(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target).unwrap();
        }
    }
}
