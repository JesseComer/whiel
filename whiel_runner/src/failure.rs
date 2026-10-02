//! Typed nonlogical failure reports.

use std::fmt;
use std::time::Duration;

use crate::artifact::ArtifactRef;

const MAX_DETAIL_BYTES: usize = 4096;
const MAX_COMBINED_WORKER_DETAIL_BYTES: usize = 1536;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FailureScope {
    LaneLocal,
    RunGlobal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FailureOrigin {
    RunControl,
    ArtifactSettlement,
    AgentConsultation,
    ResponseValidation,
    EncodingPreparation,
    InitializationExecution,
    VampireProofSearch,
    VampireFiniteModelBuilding,
    VampireRace,
    SymbolicRace,
    ModelDecoding,
    TerminationCheck,
    MaintenanceExecution,
    MaintenanceHistory,
    ValidityCertification,
    InvalidityCertification,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FailureKind {
    OverallTimeout,
    Interrupted,
    ConsultationTimeout,
    IterationLimitExhausted,
    SourceExhausted,
    CorrectionExhausted,
    NoResponse,
    TransportFailure,
    ValidationInfrastructureFailure,
    UnsupportedCheck,
    FuelExhausted,
    CheckTimeout,
    SolverUnknown,
    MalformedResult,
    ProcessFailure,
    InfrastructureFailure,
    ConcurrentWorkerFailures,
    CertificateConstructionFailure,
    CertificateRejected,
    CertificateTypecheckFailure,
    ManifestFailure,
    PublicationFailure,
    HistoryLogFailure,
    StateInvariantViolation,
}

impl FailureOrigin {
    fn permits(self, kind: FailureKind) -> bool {
        use FailureKind::*;
        match self {
            Self::RunControl => matches!(
                kind,
                OverallTimeout | Interrupted | IterationLimitExhausted | InfrastructureFailure
            ),
            Self::ArtifactSettlement => matches!(
                kind,
                ManifestFailure | PublicationFailure | InfrastructureFailure
            ),
            Self::AgentConsultation => matches!(
                kind,
                ConsultationTimeout
                    | SourceExhausted
                    | CorrectionExhausted
                    | NoResponse
                    | TransportFailure
            ),
            Self::ResponseValidation => matches!(kind, ValidationInfrastructureFailure),
            Self::EncodingPreparation => matches!(
                kind,
                MalformedResult | ProcessFailure | InfrastructureFailure | PublicationFailure
            ),
            Self::InitializationExecution => matches!(
                kind,
                PublicationFailure | InfrastructureFailure | StateInvariantViolation
            ),
            Self::VampireProofSearch | Self::VampireFiniteModelBuilding => matches!(
                kind,
                SolverUnknown
                    | CheckTimeout
                    | MalformedResult
                    | ProcessFailure
                    | InfrastructureFailure
            ),
            Self::VampireRace | Self::SymbolicRace => {
                matches!(kind, ConcurrentWorkerFailures | CheckTimeout)
            }
            Self::ModelDecoding => matches!(
                kind,
                UnsupportedCheck
                    | CheckTimeout
                    | MalformedResult
                    | ProcessFailure
                    | InfrastructureFailure
            ),
            Self::TerminationCheck => matches!(
                kind,
                CheckTimeout
                    | SolverUnknown
                    | MalformedResult
                    | ProcessFailure
                    | InfrastructureFailure
                    | ConcurrentWorkerFailures
            ),
            Self::MaintenanceExecution => matches!(
                kind,
                PublicationFailure | InfrastructureFailure | StateInvariantViolation
            ),
            Self::MaintenanceHistory => matches!(kind, HistoryLogFailure),
            Self::ValidityCertification => matches!(
                kind,
                CertificateConstructionFailure
                    | CertificateRejected
                    | CertificateTypecheckFailure
                    | ManifestFailure
                    | PublicationFailure
                    | CheckTimeout
                    | ProcessFailure
                    | InfrastructureFailure
            ),
            Self::InvalidityCertification => matches!(
                kind,
                CertificateConstructionFailure
                    | CertificateRejected
                    | CertificateTypecheckFailure
                    | ManifestFailure
                    | PublicationFailure
                    | CheckTimeout
                    | ProcessFailure
                    | InfrastructureFailure
                    | UnsupportedCheck
                    | FuelExhausted
                    | MalformedResult
            ),
        }
    }
}

/// A typed nonlogical failure with bounded diagnostics.
#[derive(Clone, Debug)]
pub struct FailureReport {
    origin: FailureOrigin,
    kind: FailureKind,
    retryable: bool,
    scope: FailureScope,
    detail: Option<String>,
    artifact_references: Vec<ArtifactRef>,
}

impl FailureReport {
    pub(crate) fn try_new(
        origin: FailureOrigin,
        kind: FailureKind,
        retryable: bool,
        scope: FailureScope,
        detail: Option<String>,
        artifact_references: Vec<ArtifactRef>,
    ) -> Result<Self, FailureReportError> {
        if !origin.permits(kind) {
            return Err(FailureReportError { origin, kind });
        }
        Ok(Self {
            origin,
            kind,
            retryable,
            scope,
            detail: detail.map(bound_detail),
            artifact_references,
        })
    }

    pub fn overall_timeout(limit: Duration) -> Self {
        Self::try_new(
            FailureOrigin::RunControl,
            FailureKind::OverallTimeout,
            false,
            FailureScope::RunGlobal,
            Some(format!("overall limit expired after {limit:?}")),
            Vec::new(),
        )
        .expect("the standard overall-timeout pair is valid")
    }

    pub fn interrupted(signal: i32) -> Self {
        Self::try_new(
            FailureOrigin::RunControl,
            FailureKind::Interrupted,
            false,
            FailureScope::RunGlobal,
            Some(format!("interrupted by signal {signal}")),
            Vec::new(),
        )
        .expect("the standard interrupt pair is valid")
    }

    pub(crate) fn admission_authority(detail: impl Into<String>) -> Self {
        Self::try_new(
            FailureOrigin::RunControl,
            FailureKind::InfrastructureFailure,
            false,
            FailureScope::RunGlobal,
            Some(detail.into()),
            Vec::new(),
        )
        .expect("runtime admission failures are run-control infrastructure failures")
    }

    pub(crate) fn artifact(
        kind: FailureKind,
        scope: FailureScope,
        detail: impl Into<String>,
    ) -> Self {
        Self::try_new(
            FailureOrigin::ArtifactSettlement,
            kind,
            false,
            scope,
            Some(detail.into()),
            Vec::new(),
        )
        .expect("artifact helper uses a permitted failure kind")
    }

    pub(crate) fn encoding_preparation(
        kind: FailureKind,
        scope: FailureScope,
        detail: impl Into<String>,
    ) -> Self {
        Self::try_new(
            FailureOrigin::EncodingPreparation,
            kind,
            false,
            scope,
            Some(detail.into()),
            Vec::new(),
        )
        .expect("encoding preparation uses a permitted failure kind")
    }

    pub(crate) fn vampire_worker_failure(
        origin: FailureOrigin,
        detail: impl Into<String>,
        artifact_references: Vec<ArtifactRef>,
    ) -> Self {
        debug_assert!(matches!(
            origin,
            FailureOrigin::VampireProofSearch | FailureOrigin::VampireFiniteModelBuilding
        ));
        Self::try_new(
            origin,
            FailureKind::InfrastructureFailure,
            false,
            FailureScope::LaneLocal,
            Some(detail.into()),
            artifact_references,
        )
        .expect("Vampire worker infrastructure failures are permitted")
    }

    pub(crate) fn maintenance_history(scope: FailureScope, detail: impl Into<String>) -> Self {
        Self::try_new(
            FailureOrigin::MaintenanceHistory,
            FailureKind::HistoryLogFailure,
            false,
            scope,
            Some(detail.into()),
            Vec::new(),
        )
        .expect("maintenance-history failures use the permitted classification")
    }

    pub(crate) fn concurrent_vampire_failures(proof: &FailureReport, fmb: &FailureReport) -> Self {
        let mut artifact_references = proof.artifact_references.clone();
        for reference in &fmb.artifact_references {
            if !artifact_references.contains(reference) {
                artifact_references.push(*reference);
            }
        }
        let proof_detail = bound_detail_to(
            proof.detail.as_deref().unwrap_or("none"),
            MAX_COMBINED_WORKER_DETAIL_BYTES,
        );
        let fmb_detail = bound_detail_to(
            fmb.detail.as_deref().unwrap_or("none"),
            MAX_COMBINED_WORKER_DETAIL_BYTES,
        );
        let detail = format!(
            "proof worker: origin={:?} kind={:?} detail={}\nFMB worker: origin={:?} kind={:?} detail={}",
            proof.origin, proof.kind, proof_detail, fmb.origin, fmb.kind, fmb_detail,
        );
        // Two lanes that each stopped themselves at the limit they were
        // given are this launch's ordinary timeout, not a pair of
        // failures: nothing went wrong, the launch ran out of the time it
        // was allowed. Anything else in either lane makes the pair a
        // failure, as it always was.
        let kind =
            if proof.kind == FailureKind::CheckTimeout && fmb.kind == FailureKind::CheckTimeout {
                FailureKind::CheckTimeout
            } else {
                FailureKind::ConcurrentWorkerFailures
            };
        Self::try_new(
            FailureOrigin::VampireRace,
            kind,
            false,
            FailureScope::LaneLocal,
            Some(detail),
            artifact_references,
        )
        .expect("the combined Vampire failure pair is permitted")
    }

    pub fn origin(&self) -> FailureOrigin {
        self.origin
    }

    pub fn kind(&self) -> FailureKind {
        self.kind
    }

    pub fn retryable(&self) -> bool {
        self.retryable
    }

    pub fn scope(&self) -> FailureScope {
        self.scope
    }

    pub fn detail(&self) -> Option<&str> {
        self.detail.as_deref()
    }

    pub fn artifact_references(&self) -> &[ArtifactRef] {
        &self.artifact_references
    }

    /// This same report with one further sentence of context appended to
    /// its detail.
    ///
    /// Its classification is untouched: this is for a second fact about
    /// the same failure that would otherwise be dropped, not for
    /// reinterpreting the first. The combined detail is bounded like every
    /// other, so a long context cannot make a record unbounded.
    pub fn with_appended_detail(mut self, context: &str) -> Self {
        let detail = match self.detail.take() {
            Some(detail) => format!("{detail}\n{context}"),
            None => context.to_owned(),
        };
        self.detail = Some(bound_detail_to(&detail, MAX_DETAIL_BYTES));
        self
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FailureReportError {
    pub(crate) origin: FailureOrigin,
    pub(crate) kind: FailureKind,
}

impl fmt::Display for FailureReportError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "failure origin {:?} does not permit kind {:?}",
            self.origin, self.kind
        )
    }
}

impl std::error::Error for FailureReportError {}

fn bound_detail(mut detail: String) -> String {
    if detail.len() <= MAX_DETAIL_BYTES {
        return detail;
    }
    let mut boundary = MAX_DETAIL_BYTES;
    while !detail.is_char_boundary(boundary) {
        boundary -= 1;
    }
    detail.truncate(boundary);
    detail.push('…');
    detail
}

fn bound_detail_to(detail: &str, max_bytes: usize) -> String {
    if detail.len() <= max_bytes {
        return detail.to_owned();
    }
    let mut boundary = max_bytes;
    while !detail.is_char_boundary(boundary) {
        boundary -= 1;
    }
    let mut bounded = detail[..boundary].to_owned();
    bounded.push('…');
    bounded
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_invalid_origin_kind_pairs() {
        let result = FailureReport::try_new(
            FailureOrigin::RunControl,
            FailureKind::SolverUnknown,
            false,
            FailureScope::LaneLocal,
            None,
            Vec::new(),
        );
        assert!(result.is_err());
    }

    #[test]
    fn bounds_diagnostic_details() {
        let report = FailureReport::try_new(
            FailureOrigin::ArtifactSettlement,
            FailureKind::InfrastructureFailure,
            false,
            FailureScope::RunGlobal,
            Some("x".repeat(MAX_DETAIL_BYTES * 2)),
            Vec::new(),
        )
        .unwrap();
        assert!(report.detail().unwrap().len() <= MAX_DETAIL_BYTES + 3);
    }

    #[test]
    fn overall_timeout_has_run_global_contract() {
        let report = FailureReport::overall_timeout(Duration::from_secs(7));
        assert_eq!(report.origin(), FailureOrigin::RunControl);
        assert_eq!(report.kind(), FailureKind::OverallTimeout);
        assert!(!report.retryable());
        assert_eq!(report.scope(), FailureScope::RunGlobal);
        assert!(report.artifact_references().is_empty());
    }

    #[test]
    fn interrupted_has_run_global_contract() {
        let report = FailureReport::interrupted(libc::SIGINT);
        assert_eq!(report.origin(), FailureOrigin::RunControl);
        assert_eq!(report.kind(), FailureKind::Interrupted);
        assert!(!report.retryable());
        assert_eq!(report.scope(), FailureScope::RunGlobal);
        assert_eq!(report.detail(), Some("interrupted by signal 2"));
    }

    #[test]
    fn combined_worker_failure_retains_both_bounded_contexts() {
        let proof = FailureReport::vampire_worker_failure(
            FailureOrigin::VampireProofSearch,
            format!("proof-context:{}", "p".repeat(MAX_DETAIL_BYTES * 2)),
            Vec::new(),
        );
        let fmb = FailureReport::vampire_worker_failure(
            FailureOrigin::VampireFiniteModelBuilding,
            format!("fmb-context:{}", "f".repeat(MAX_DETAIL_BYTES * 2)),
            Vec::new(),
        );

        let combined = FailureReport::concurrent_vampire_failures(&proof, &fmb);
        let detail = combined.detail().unwrap();
        assert!(detail.contains("proof worker"));
        assert!(detail.contains("proof-context"));
        assert!(detail.contains("FMB worker"));
        assert!(detail.contains("fmb-context"));
        assert!(detail.len() <= MAX_DETAIL_BYTES);
    }
}
