//! Strict, inert records of comparisons already checked by the run owner.
//!
//! Decoding this log validates its shape, never a mapping or a proof. Only the
//! live correspondence owner may populate it after checking actual constructors.

use serde::{Deserialize, Deserializer, Serialize};

use super::replay_identity::ReplayDivergence;
use super::replay_wire_compare::{ReplayTimingDifference, ReplayWireIdentity};
use super::strict_json::decode_strict_json;
use super::transcript::{TranscriptCoordinates, TranscriptHeader};

pub const REPLAY_COMPARISON_LOG_VERSION: u64 = 2;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(transparent)]
pub struct ReplayAuditDigest(String);

impl ReplayAuditDigest {
    pub fn new(value: impl Into<String>) -> Result<Self, ReplayDivergence> {
        let value = value.into();
        if value.len() != 64
            || !value
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(divergence("digest", "expected a lowercase SHA256 digest"));
        }
        Ok(Self(value))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<'de> Deserialize<'de> for ReplayAuditDigest {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Self::new(String::deserialize(deserializer)?)
            .map_err(|_| serde::de::Error::custom("expected a lowercase SHA256 digest"))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReplayHeaderPair {
    pub old: TranscriptHeader,
    pub live: TranscriptHeader,
}

/// Checks header compatibility only. The caller must separately bind both run
/// identities and task/source/scope/policy pins to its checked actual owners.
pub fn compare_headers(
    old: &TranscriptHeader,
    live: &TranscriptHeader,
) -> Result<ReplayHeaderPair, ReplayDivergence> {
    for (side, header) in [("old", old), ("live", live)] {
        for (field, actual, expected) in [
            ("version", header.version, 3),
            ("proposal_schema", header.proposal_schema, 4),
            (
                "feedback_schema",
                header.feedback_schema,
                super::feedback::AGENT_FEEDBACK_SCHEMA_VERSION,
            ),
            (
                "presentation_schema",
                header.presentation_schema,
                super::feedback::AGENT_PRESENTATION_SCHEMA_VERSION,
            ),
        ] {
            if actual != expected {
                return Err(divergence(
                    &format!("headers/{side}/{field}"),
                    "unsupported replay header version",
                ));
            }
        }
        if header.proposer_identity.is_empty() || header.source_run_identity.is_empty() {
            return Err(divergence(
                &format!("headers/{side}"),
                "provider and source-run identities must be present",
            ));
        }
        let pins = &header.pins;
        for (field, value) in [
            ("task_digest", &pins.task_digest),
            ("source_digest", &pins.source_digest),
            ("scope_digest", &pins.scope_digest),
            ("policy_digest", &pins.policy_digest),
            ("runner_digest", &pins.runner_digest),
            ("worker_digest", &pins.worker_digest),
            ("lean_digest", &pins.lean_digest),
            ("vampire_digest", &pins.vampire_digest),
            ("profile_digest", &pins.profile_digest),
        ] {
            ReplayAuditDigest::new(value.clone()).map_err(|_| {
                divergence(
                    &format!("headers/{side}/pins/{field}"),
                    "malformed identity pin",
                )
            })?;
        }
    }
    if old.proposer_identity != live.proposer_identity {
        return Err(divergence(
            "headers/proposer_identity",
            "provider identity differs",
        ));
    }
    if old.pins != live.pins {
        return Err(divergence("headers/pins", "exact replay pins differ"));
    }
    Ok(ReplayHeaderPair {
        old: old.clone(),
        live: live.clone(),
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ReplayAuditProductionIdentity {
    Catalog,
    Partition,
    CheckRequest,
    Backend,
    ArtifactBackendDigest,
    ContextAllocation,
    PreparedBody,
    SupportBlock,
    Entailment,
    Preparation,
    Job,
    Terminal,
    ProductionReceipt,
    SemanticReuse,
    EvidenceIdentity,
    RouteDisplay,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ReplayHostIdentity {
    FeedbackSession,
    LatestEvent,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ReplayIdentityPairValue {
    Host {
        category: ReplayHostIdentity,
        old: ReplayAuditDigest,
        live: ReplayAuditDigest,
    },
    Catalog {
        old: ReplayAuditDigest,
        live: ReplayAuditDigest,
    },
    ClauseRecord {
        old: ReplayAuditDigest,
        live: ReplayAuditDigest,
    },
    Partition {
        old: ReplayAuditDigest,
        live: ReplayAuditDigest,
    },
    PhysicalAttempt {
        old: u64,
        live: u64,
    },
    Artifact {
        old_backend: String,
        old_local: u64,
        live_backend: String,
        live_local: u64,
    },
    Production {
        category: ReplayAuditProductionIdentity,
        // Some production identities are allocated names, not SHA256 digests.
        old: String,
        live: String,
    },
    Wire {
        category: ReplayWireIdentity,
        old: String,
        live: String,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "constructor", rename_all = "snake_case", deny_unknown_fields)]
pub enum ReplayDerivationConstructor {
    HostOwner {
        category: ReplayHostIdentity,
    },
    CatalogSnapshot {},
    ClauseRecord {},
    PartitionSnapshot {},
    PhysicalAttemptLink {},
    ArtifactAllocation {},
    ProductionOwner {
        category: ReplayAuditProductionIdentity,
    },
    WireOwner {
        category: ReplayWireIdentity,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReplayDerivation {
    pub constructor: ReplayDerivationConstructor,
    pub old_owner_projection_sha256: ReplayAuditDigest,
    pub live_owner_projection_sha256: ReplayAuditDigest,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReplayIdentityPair {
    pub identity: ReplayIdentityPairValue,
    pub derivation: ReplayDerivation,
}

impl ReplayIdentityPair {
    fn validate_shape(&self) -> Result<(), ReplayDivergence> {
        use ReplayDerivationConstructor as D;
        use ReplayIdentityPairValue as I;
        let agrees = match (&self.identity, self.derivation.constructor) {
            (I::Host { category, .. }, D::HostOwner { category: actual }) => *category == actual,
            (I::Catalog { .. }, D::CatalogSnapshot {})
            | (I::ClauseRecord { .. }, D::ClauseRecord {})
            | (I::Partition { .. }, D::PartitionSnapshot {})
            | (I::PhysicalAttempt { .. }, D::PhysicalAttemptLink {})
            | (I::Artifact { .. }, D::ArtifactAllocation {}) => true,
            (I::Production { category, .. }, D::ProductionOwner { category: actual }) => {
                *category == actual
            }
            (I::Wire { category, .. }, D::WireOwner { category: actual }) => *category == actual,
            _ => false,
        };
        if agrees {
            Ok(())
        } else {
            Err(divergence(
                "identity_pairs/derivation",
                "identity and constructor categories differ",
            ))
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ReplayTimingOwner {
    Ledger { row_ordinal: u64 },
    Termination { check_ordinal: u64 },
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ReplayOwnerTimingSlot {
    Solver,
    Preparation,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReplayOwnerTiming {
    pub owner: ReplayTimingOwner,
    pub slot: ReplayOwnerTimingSlot,
    #[serde(deserialize_with = "required_nullable")]
    pub old_ns: Option<String>,
    #[serde(deserialize_with = "required_nullable")]
    pub live_ns: Option<String>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ReplayComparisonRecord {
    FinalState {
        old_owner_projection_sha256: ReplayAuditDigest,
        live_owner_projection_sha256: ReplayAuditDigest,
        semantic_core_digest: ReplayAuditDigest,
        old_ledger_chain_digest: ReplayAuditDigest,
        live_ledger_chain_digest: ReplayAuditDigest,
        owner_timing: Vec<ReplayOwnerTiming>,
    },
    Push {
        coordinates: TranscriptCoordinates,
        old_bytes_sha256: ReplayAuditDigest,
        live_bytes_sha256: ReplayAuditDigest,
        old_owner_projection_sha256: ReplayAuditDigest,
        live_owner_projection_sha256: ReplayAuditDigest,
        semantic_core_digest: ReplayAuditDigest,
        owner_timing: Vec<ReplayOwnerTiming>,
        old_ledger_chain_digest: ReplayAuditDigest,
        live_ledger_chain_digest: ReplayAuditDigest,
        timing: Vec<ReplayTimingDifference>,
    },
    ToolCall {
        coordinates: TranscriptCoordinates,
        call_id: u64,
        name: String,
        old_bytes_sha256: ReplayAuditDigest,
        live_bytes_sha256: ReplayAuditDigest,
    },
    ToolResponse {
        coordinates: TranscriptCoordinates,
        call_id: u64,
        old_bytes_sha256: ReplayAuditDigest,
        live_bytes_sha256: ReplayAuditDigest,
        timing: Vec<ReplayTimingDifference>,
    },
    Correction {
        coordinates: TranscriptCoordinates,
        old_bytes_sha256: ReplayAuditDigest,
        live_bytes_sha256: ReplayAuditDigest,
        timing: Vec<ReplayTimingDifference>,
    },
    ResponseChunks {
        coordinates: TranscriptCoordinates,
        old_complete_bytes_sha256: ReplayAuditDigest,
        live_complete_bytes_sha256: ReplayAuditDigest,
        old_chunk_chain_sha256: ReplayAuditDigest,
        live_chunk_chain_sha256: ReplayAuditDigest,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReplayComparisonLogV2 {
    #[serde(deserialize_with = "log_version")]
    pub version: u64,
    #[serde(deserialize_with = "required_nullable")]
    pub headers: Option<ReplayHeaderPair>,
    pub identity_pairs: Vec<ReplayIdentityPair>,
    pub comparisons: Vec<ReplayComparisonRecord>,
}

impl Default for ReplayComparisonLogV2 {
    fn default() -> Self {
        Self {
            version: REPLAY_COMPARISON_LOG_VERSION,
            headers: None,
            identity_pairs: Vec::new(),
            comparisons: Vec::new(),
        }
    }
}

impl ReplayComparisonLogV2 {
    /// This checks only the log's schema. It does not verify the supplied digest
    /// preimages, bijections, event order, owner authority or compared bytes.
    pub fn validate(&self) -> Result<(), ReplayDivergence> {
        if self.version != REPLAY_COMPARISON_LOG_VERSION {
            return Err(divergence("version", "unsupported comparison log version"));
        }
        if let Some(pair) = &self.headers {
            compare_headers(&pair.old, &pair.live)?;
        }
        for pair in &self.identity_pairs {
            pair.validate_shape()?;
            if let ReplayIdentityPairValue::Wire { old, live, .. } = &pair.identity {
                ReplayAuditDigest::new(old.clone())?;
                ReplayAuditDigest::new(live.clone())?;
            }
        }
        for comparison in &self.comparisons {
            if let ReplayComparisonRecord::Push { owner_timing, .. }
            | ReplayComparisonRecord::FinalState { owner_timing, .. } = comparison
            {
                for timing in owner_timing {
                    if timing.old_ns.is_some() != timing.live_ns.is_some() {
                        return Err(divergence("owner_timing", "duration presence differs"));
                    }
                    for value in [&timing.old_ns, &timing.live_ns].into_iter().flatten() {
                        let nanos = value
                            .parse::<u128>()
                            .map_err(|_| divergence("owner_timing", "invalid nanoseconds"))?;
                        if nanos.to_string() != *value {
                            return Err(divergence("owner_timing", "noncanonical nanoseconds"));
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

pub fn decode_comparison_log(
    bytes: &[u8],
    maximum_bytes: usize,
) -> Result<ReplayComparisonLogV2, ReplayDivergence> {
    let value = decode_strict_json(bytes, Some(maximum_bytes))
        .map_err(|error| divergence("$", &error.to_string()))?;
    let log: ReplayComparisonLogV2 = serde_json::from_value(value)
        .map_err(|_| divergence("$", "unsupported comparison log schema"))?;
    log.validate()?;
    Ok(log)
}

fn log_version<'de, D: Deserializer<'de>>(deserializer: D) -> Result<u64, D::Error> {
    let version = u64::deserialize(deserializer)?;
    if version != REPLAY_COMPARISON_LOG_VERSION {
        return Err(serde::de::Error::custom(
            "unsupported comparison log version",
        ));
    }
    Ok(version)
}

fn required_nullable<'de, D: Deserializer<'de>, T: Deserialize<'de>>(
    deserializer: D,
) -> Result<Option<T>, D::Error> {
    Option::deserialize(deserializer)
}

fn divergence(path: &str, reason: &str) -> ReplayDivergence {
    ReplayDivergence {
        path: path.into(),
        reason: reason.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::super::transcript::TranscriptPins;
    use super::*;
    use serde_json::json;

    fn header(run: &str) -> TranscriptHeader {
        let pin = "a".repeat(64);
        TranscriptHeader::new(
            "exact-provider-config-digest".into(),
            run.into(),
            TranscriptPins {
                task_digest: pin.clone(),
                source_digest: pin.clone(),
                scope_digest: pin.clone(),
                policy_digest: pin.clone(),
                runner_digest: pin.clone(),
                worker_digest: pin.clone(),
                lean_digest: pin.clone(),
                vampire_digest: pin.clone(),
                profile_digest: pin,
            },
        )
    }

    #[test]
    fn header_compatibility_does_not_map_the_fresh_run_identity() {
        let old = header("old-run");
        let live = header("fresh-run");
        let pair = compare_headers(&old, &live).unwrap();
        assert_eq!(pair.old.source_run_identity, "old-run");
        assert_eq!(pair.live.source_run_identity, "fresh-run");
        assert_ne!(pair.old.source_run_identity, pair.live.source_run_identity);
    }

    #[test]
    fn every_header_pin_and_proposer_identity_is_exact() {
        let old = header("old");
        for field in [
            "task_digest",
            "source_digest",
            "scope_digest",
            "policy_digest",
            "runner_digest",
            "worker_digest",
            "lean_digest",
            "vampire_digest",
            "profile_digest",
        ] {
            let mut value = serde_json::to_value(header("live")).unwrap();
            value["pins"][field] = json!("b".repeat(64));
            let changed = serde_json::from_value(value).unwrap();
            assert!(compare_headers(&old, &changed).is_err(), "{field}");
        }
        let mut live = header("live");
        live.proposer_identity.push('x');
        assert!(compare_headers(&old, &live).is_err());
    }

    #[test]
    fn old_header_versions_and_malformed_pins_are_rejected() {
        let old = header("old");
        for field in [
            "version",
            "proposal_schema",
            "feedback_schema",
            "presentation_schema",
        ] {
            let mut value = serde_json::to_value(header("live")).unwrap();
            value[field] = json!(1);
            assert!(compare_headers(&old, &serde_json::from_value(value).unwrap()).is_err());
        }
        let mut live = header("live");
        live.pins.runner_digest = "not-a-pin".into();
        assert!(compare_headers(&live, &live).is_err());
    }

    #[test]
    fn required_null_version_unknown_and_duplicate_fields_are_strict() {
        let good = br#"{"version":2,"headers":null,"identity_pairs":[],"comparisons":[]}"#;
        assert!(decode_comparison_log(good, good.len()).is_ok());
        for bad in [
            br#"{"version":2,"identity_pairs":[],"comparisons":[]}"#.as_slice(),
            br#"{"version":1,"headers":null,"identity_pairs":[],"comparisons":[]}"#,
            br#"{"version":2,"headers":null,"identity_pairs":[],"comparisons":[],"accepted":true}"#,
            br#"{"version":2,"headers":null,"identity_pairs":[],"comparisons":[],"headers":null}"#,
        ] {
            assert!(decode_comparison_log(bad, 4096).is_err());
        }
        assert!(decode_comparison_log(good, good.len() - 1).is_err());
        assert!(decode_comparison_log(good, 0).is_err());
    }

    #[test]
    fn log_cannot_relabel_a_wire_mapping_as_an_artifact_derivation() {
        let pin = ReplayAuditDigest::new("a".repeat(64)).unwrap();
        let pair = ReplayIdentityPair {
            identity: ReplayIdentityPairValue::Wire {
                category: ReplayWireIdentity::Run,
                old: "old".into(),
                live: "live".into(),
            },
            derivation: ReplayDerivation {
                constructor: ReplayDerivationConstructor::ArtifactAllocation {},
                old_owner_projection_sha256: pin.clone(),
                live_owner_projection_sha256: pin,
            },
        };
        let log = ReplayComparisonLogV2 {
            identity_pairs: vec![pair],
            ..Default::default()
        };
        assert!(decode_comparison_log(&serde_json::to_vec(&log).unwrap(), 4096).is_err());
    }

    #[test]
    fn nested_derivation_extensions_and_bad_digest_strings_are_rejected() {
        let pin = "a".repeat(64);
        let mut value = json!({"version":2,"headers":null,"identity_pairs":[{
            "identity":{"kind":"physical_attempt","old":8,"live":13},
            "derivation":{"constructor":{"constructor":"physical_attempt_link"},"old_owner_projection_sha256":pin,"live_owner_projection_sha256":pin}
        }],"comparisons":[]});
        assert!(decode_comparison_log(&serde_json::to_vec(&value).unwrap(), 4096).is_ok());
        value["identity_pairs"][0]["derivation"]["constructor"]["claim"] = json!(true);
        assert!(decode_comparison_log(&serde_json::to_vec(&value).unwrap(), 4096).is_err());
        for bad in [
            "a".repeat(63),
            "a".repeat(65),
            "A".repeat(64),
            "g".repeat(64),
        ] {
            assert!(serde_json::from_value::<ReplayAuditDigest>(json!(bad)).is_err());
        }
    }
}
