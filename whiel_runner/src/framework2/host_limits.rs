//! The run's optional host limits (`houdini.tex` Section 4.7, "Resource
//! limits"; `agent_houdini.tex` Sections "The standing presentation" and
//! "Actions").
//!
//! No functional bound is built into the controller, the worker, or the
//! dictionary. Every limit on the fixed-ambient path is one of two kinds:
//!
//! - a *safety guard* on wall time, generated file space, or total memory,
//!   whose failure is a resource fault (the run and consultation deadlines,
//!   the artifact store's space accounting, and the agent policy's
//!   `max_attempt_history_records`); or
//! - an *optional host limit*, absent by default, stated to the proposer in
//!   the standing presentation when set, whose refusal is reported with the
//!   single correction code `host_limit` naming the limit and never as a
//!   defect of the proposal.
//!
//! [`HostLimits`] is the whole of the second kind. Every field is
//! `Option<u64>` and defaults to `None`; where a limit is unset nothing is
//! truncated and nothing is refused. The value enters the feedback policy's
//! digest, so a run's limits are part of its recorded identity.
//!
//! Solver and kernel cost are optimization targets, not grounds for a bound:
//! nothing here may be given a nonzero default to make a check cheaper.

use std::sync::Arc;

use serde_json::{Value, json};

pub use crate::proposer_api::observation::{HOST_LIMIT_NAMES, HostLimitName};

/// The optional host limits of one run. Every field is absent by default.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HostLimits {
    /// Clauses the catalog may hold after one submission is admitted.
    pub catalog_size: Option<u64>,
    /// Bytes one submitted clause's text may occupy.
    pub clause_text_bytes: Option<u64>,
    /// Total tuples a validated countermodel may carry and still be retained
    /// in full. Beyond it the dictionary records that a refutation exists
    /// with its tuple count, and the `countermodel` tool says so.
    pub countermodel_retention_tuples: Option<u64>,
    /// Drop references one submission may carry.
    pub drop_references: Option<u64>,
    /// Product of drafts and selected instances one `evaluate_clauses` call may ask for.
    pub evaluation_cost: Option<u64>,
    /// Level bound `l_max`: a clause whose minimum level exceeds it is
    /// refused at admission, and no clause is promoted above it. This is the
    /// single source of the bound the controller state carries as
    /// `LeveledHoudiniState::max_level`: the production bootstrap builds the
    /// state's bound from this field, and [`HostLimits::with_level_bound`]
    /// rejects a state that was built some other way and disagrees.
    pub level_bound: Option<u64>,
    /// Clauses one submission may carry.
    pub proposal_size: Option<u64>,
    /// Core clauses one push may carry. Beyond it the pushed Core is
    /// truncated and the push says so in its `truncated` list.
    pub pushed_core: Option<u64>,
    /// Bytes one provider reply may occupy.
    pub reply_bytes: Option<u64>,
    /// Entries the `strongest_refutations` tool returns from the maximal
    /// antichain. Beyond it the answer is truncated and says so.
    pub strongest_refutations: Option<u64>,
}

impl HostLimits {
    /// No limit at all: the default every run starts from.
    pub const UNBOUNDED: Self = Self {
        catalog_size: None,
        clause_text_bytes: None,
        countermodel_retention_tuples: None,
        drop_references: None,
        evaluation_cost: None,
        level_bound: None,
        proposal_size: None,
        pushed_core: None,
        reply_bytes: None,
        strongest_refutations: None,
    };

    /// This limit set with `level_bound` reconciled against the controller
    /// state's own optional bound.
    ///
    /// The run policy is the single source of every host limit: the
    /// production bootstrap derives [`LeveledHoudiniState`]'s bound from
    /// `level_bound`, so on that path the two agree by construction. A state
    /// assembled another way is still reconciled here — a state bound fills
    /// in for a policy that named none, and a state bound that contradicts
    /// one the policy did name is an error rather than a value to prefer
    /// silently, because the presentation would then state a bound the
    /// controller does not enforce.
    ///
    /// [`LeveledHoudiniState`]: super::stabilization::LeveledHoudiniState
    pub fn with_level_bound(self, state_bound: Option<u64>) -> Result<Self, HostLimitDisagreement> {
        if let (Some(policy), Some(state)) = (self.level_bound, state_bound)
            && policy != state
        {
            return Err(HostLimitDisagreement {
                limit: "level_bound",
                policy: Some(policy),
                other: Some(state),
            });
        }
        Ok(Self {
            level_bound: self.level_bound.or(state_bound),
            ..self
        })
    }

    /// The first limit on which this set and `other` disagree, in
    /// [`HOST_LIMIT_NAMES`] order, or `None` when they are identical.
    ///
    /// Two authorities of one run — the feedback policy and the production
    /// checker's configuration — must carry the same host limits, or the
    /// presentation states one thing and the checker does another.
    pub fn first_disagreement(&self, other: &Self) -> Option<HostLimitDisagreement> {
        HOST_LIMIT_NAMES.into_iter().find_map(|limit| {
            let policy = self.get(limit);
            let observed = other.get(limit);
            (policy != observed).then_some(HostLimitDisagreement {
                limit,
                policy,
                other: observed,
            })
        })
    }

    /// Every limit in force, as `(name, value)` pairs in
    /// [`HOST_LIMIT_NAMES`] order. Empty when nothing is set.
    pub fn in_force(&self) -> Vec<(HostLimitName, u64)> {
        HOST_LIMIT_NAMES
            .into_iter()
            .filter_map(|name| self.get(name).map(|value| (name, value)))
            .collect()
    }

    /// The presentation's wire form: the limits in force, each named with
    /// its value, and nothing else. An empty list is the honest statement
    /// that the run sets none.
    pub fn wire_value(&self) -> Value {
        Value::Array(
            self.in_force()
                .into_iter()
                .map(|(limit, value)| json!({"limit": limit, "value": value}))
                .collect(),
        )
    }

    /// The digest form, carrying every field including the absent ones so
    /// that clearing a limit changes the policy's identity.
    pub fn digest_value(&self) -> Value {
        Value::Object(
            HOST_LIMIT_NAMES
                .into_iter()
                .map(|name| {
                    (
                        name.to_string(),
                        self.get(name).map_or(Value::Null, Value::from),
                    )
                })
                .collect(),
        )
    }

    /// The limit named, if it is in force.
    pub fn get(&self, name: HostLimitName) -> Option<u64> {
        match name {
            "catalog_size" => self.catalog_size,
            "clause_text_bytes" => self.clause_text_bytes,
            "countermodel_retention_tuples" => self.countermodel_retention_tuples,
            "drop_references" => self.drop_references,
            "evaluation_cost" => self.evaluation_cost,
            "level_bound" => self.level_bound,
            "proposal_size" => self.proposal_size,
            "pushed_core" => self.pushed_core,
            "reply_bytes" => self.reply_bytes,
            "strongest_refutations" => self.strongest_refutations,
            _ => None,
        }
    }

    /// The limit named, as a `usize`, saturating on a host that cannot
    /// represent it. Absent when the limit is unset.
    pub fn get_usize(&self, name: HostLimitName) -> Option<usize> {
        self.get(name)
            .map(|value| usize::try_from(value).unwrap_or(usize::MAX))
    }

    /// The refusal `observed` would earn under the named limit, or `None`
    /// when the limit is unset or `observed` is within it. An unset limit
    /// never refuses anything.
    pub fn refusal(&self, name: HostLimitName, observed: u64) -> Option<HostLimitRefusal> {
        let value = self.get(name)?;
        (observed > value).then_some(HostLimitRefusal {
            limit: name,
            value,
            observed,
        })
    }

    /// How many items of a list of `total` may be shown under the named
    /// limit: all of them when it is unset.
    pub fn shown_of(&self, name: HostLimitName, total: usize) -> usize {
        match self.get(name) {
            None => total,
            Some(value) => total.min(usize::try_from(value).unwrap_or(usize::MAX)),
        }
    }
}

/// Two authorities of one run naming different values for one host limit.
///
/// Host limits have a single source, the run's feedback policy. Every other
/// authority that carries them — the controller state's level bound, the
/// production checker's configuration — is built from it, and a
/// disagreement is a wiring fault that fails construction closed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HostLimitDisagreement {
    limit: HostLimitName,
    policy: Option<u64>,
    other: Option<u64>,
}

impl HostLimitDisagreement {
    pub fn limit(&self) -> HostLimitName {
        self.limit
    }

    pub fn policy(&self) -> Option<u64> {
        self.policy
    }

    pub fn other(&self) -> Option<u64> {
        self.other
    }
}

impl std::fmt::Display for HostLimitDisagreement {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = |value: Option<u64>| match value {
            None => String::from("unset"),
            Some(value) => value.to_string(),
        };
        write!(
            formatter,
            "host limit {} is {} in the run policy and {} in another authority",
            self.limit,
            name(self.policy),
            name(self.other),
        )
    }
}

/// One submission refused by a host limit. It is never a defect of the
/// proposal: the code is always `host_limit`, and the payload names which
/// limit, its value, and what was observed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HostLimitRefusal {
    limit: HostLimitName,
    value: u64,
    observed: u64,
}

/// The single correction code every host-limit refusal carries.
pub const HOST_LIMIT_CODE: &str = "host_limit";

impl HostLimitRefusal {
    /// The refusal a caller already knows the shape of: the limit's name,
    /// the value in force, and what was observed. Callers that hold a
    /// [`HostLimits`] should prefer [`HostLimits::refusal`], which cannot
    /// name a limit the run has not set.
    pub fn new(limit: HostLimitName, value: u64, observed: u64) -> Self {
        Self {
            limit,
            value,
            observed,
        }
    }

    pub fn limit(&self) -> HostLimitName {
        self.limit
    }

    pub fn value(&self) -> u64 {
        self.value
    }

    pub fn observed(&self) -> u64 {
        self.observed
    }

    /// The correction diagnostic's message: what was refused and why, with
    /// no suggestion that the proposal was wrong.
    pub fn message(&self) -> String {
        format!(
            "This run sets the host limit {} to {}; the submission observed {}. \
             The limit is the host's, not a defect of the proposal.",
            self.limit, self.value, self.observed
        )
    }

    /// The refusal's wire object, carried beside the `host_limit` code.
    pub fn wire_value(&self) -> Value {
        json!({
            "limit": self.limit,
            "value": self.value,
            "observed": self.observed,
        })
    }
}

/// One truncated list in a push or a tool answer: which list, how many
/// entries are shown, how many exist, and the limit that cut it. This is
/// the contract's `truncated` object, generalising the earlier Core-only
/// `core_truncated` marker to every list a host limit can truncate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HostLimitTruncation {
    list: Arc<str>,
    shown: usize,
    total: usize,
    limit: HostLimitName,
}

impl HostLimitTruncation {
    /// The truncation of `list` under `limit`, or `None` when the limit is
    /// unset or `total` is within it.
    pub fn of(
        limits: &HostLimits,
        list: impl Into<Arc<str>>,
        limit: HostLimitName,
        total: usize,
    ) -> Option<Self> {
        let shown = limits.shown_of(limit, total);
        (shown < total).then(|| Self {
            list: list.into(),
            shown,
            total,
            limit,
        })
    }

    pub fn list(&self) -> &str {
        &self.list
    }

    pub fn shown(&self) -> usize {
        self.shown
    }

    pub fn total(&self) -> usize {
        self.total
    }

    pub fn limit(&self) -> HostLimitName {
        self.limit
    }

    pub fn wire_value(&self) -> Value {
        json!({
            "list": self.list.as_ref(),
            "shown": self.shown,
            "total": self.total,
            "limit": self.limit,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The default is the whole point: a run that names no limit refuses
    /// nothing and truncates nothing.
    #[test]
    fn the_default_host_limits_are_unbounded() {
        let limits = HostLimits::default();
        assert_eq!(limits.in_force(), Vec::new());
        assert_eq!(limits.wire_value(), json!([]));
        for name in HOST_LIMIT_NAMES {
            assert_eq!(limits.get(name), None);
            assert_eq!(limits.refusal(name, u64::MAX), None);
            assert_eq!(limits.get_usize(name), None);
            assert_eq!(limits.shown_of(name, 4_096), 4_096);
            assert_eq!(HostLimitTruncation::of(&limits, "core", name, 4_096), None);
        }
    }

    /// A limit that is set refuses only beyond its value, and the refusal
    /// carries the limit's name, its value, and what was observed.
    #[test]
    fn a_set_limit_refuses_only_beyond_its_value() {
        let limits = HostLimits {
            proposal_size: Some(2),
            ..HostLimits::default()
        };
        assert_eq!(limits.in_force(), vec![("proposal_size", 2)]);
        assert_eq!(limits.refusal("proposal_size", 2), None);
        let refusal = limits
            .refusal("proposal_size", 3)
            .expect("three clauses exceed a limit of two");
        assert_eq!(refusal.limit(), "proposal_size");
        assert_eq!(refusal.value(), 2);
        assert_eq!(refusal.observed(), 3);
        assert_eq!(
            refusal.wire_value(),
            json!({"limit": "proposal_size", "value": 2, "observed": 3})
        );
        // Another limit is still absent, and still refuses nothing.
        assert_eq!(limits.refusal("catalog_size", u64::MAX), None);
    }

    /// Truncation names the list, the counts, and the limit that cut it.
    #[test]
    fn a_truncated_list_names_its_limit_and_its_counts() {
        let limits = HostLimits {
            pushed_core: Some(3),
            ..HostLimits::default()
        };
        assert_eq!(
            HostLimitTruncation::of(&limits, "core", "pushed_core", 3),
            None
        );
        let truncation = HostLimitTruncation::of(&limits, "core", "pushed_core", 7)
            .expect("seven entries exceed a limit of three");
        assert_eq!(
            truncation.wire_value(),
            json!({"list": "core", "shown": 3, "total": 7, "limit": "pushed_core"})
        );
    }

    /// The controller state's bound fills in for a policy that did not name
    /// one, and an equal bound on both sides reconciles. Pass 7.7b, item 4:
    /// the policy no longer silently wins over a state that disagrees.
    #[test]
    fn the_level_bound_reconciles_the_policy_and_the_state() {
        assert_eq!(
            HostLimits::default()
                .with_level_bound(Some(2))
                .expect("a state bound fills in for a policy that names none")
                .level_bound,
            Some(2)
        );
        assert_eq!(
            HostLimits {
                level_bound: Some(2),
                ..HostLimits::default()
            }
            .with_level_bound(Some(2))
            .expect("equal bounds reconcile")
            .level_bound,
            Some(2)
        );
        assert_eq!(
            HostLimits::default()
                .with_level_bound(None)
                .expect("two absent bounds reconcile")
                .level_bound,
            None
        );
        assert_eq!(
            HostLimits {
                level_bound: Some(1),
                ..HostLimits::default()
            }
            .with_level_bound(None)
            .expect("a policy bound stands where the state has none")
            .level_bound,
            Some(1)
        );
    }

    /// Both directions of the disagreement fail closed rather than one
    /// authority quietly winning.
    #[test]
    fn a_contradicted_level_bound_is_an_error_in_both_directions() {
        let policy_says_one = HostLimits {
            level_bound: Some(1),
            ..HostLimits::default()
        };
        let disagreement = policy_says_one
            .with_level_bound(Some(2))
            .expect_err("a state bound of two contradicts a policy bound of one");
        assert_eq!(disagreement.limit(), "level_bound");
        assert_eq!(disagreement.policy(), Some(1));
        assert_eq!(disagreement.other(), Some(2));
        assert!(disagreement.to_string().contains("level_bound"));

        let policy_says_two = HostLimits {
            level_bound: Some(2),
            ..HostLimits::default()
        };
        let reversed = policy_says_two
            .with_level_bound(Some(1))
            .expect_err("a state bound of one contradicts a policy bound of two");
        assert_eq!(reversed.policy(), Some(2));
        assert_eq!(reversed.other(), Some(1));
    }

    /// The whole-set comparison the search uses to check that the checker's
    /// configuration and the feedback policy carry the same limits.
    #[test]
    fn two_limit_sets_disagree_on_their_first_differing_limit() {
        let policy = HostLimits {
            catalog_size: Some(8),
            reply_bytes: Some(1_024),
            ..HostLimits::UNBOUNDED
        };
        assert_eq!(policy.first_disagreement(&policy), None);
        let checker = HostLimits {
            reply_bytes: Some(1_024),
            ..HostLimits::UNBOUNDED
        };
        let disagreement = policy
            .first_disagreement(&checker)
            .expect("an unset catalog_size disagrees with a set one");
        assert_eq!(disagreement.limit(), "catalog_size");
        assert_eq!(disagreement.policy(), Some(8));
        assert_eq!(disagreement.other(), None);
    }

    /// Pass 7.7b, deliverable 5: every limit refuses beyond its value when
    /// it is set, and refuses nothing at all when it is not. The table is
    /// over [`HOST_LIMIT_NAMES`], so a limit added later without a
    /// disposition fails this test rather than passing silently.
    #[test]
    fn every_limit_refuses_when_set_and_nothing_when_unset() {
        for name in HOST_LIMIT_NAMES {
            let unset = HostLimits::UNBOUNDED;
            assert_eq!(
                unset.refusal(name, u64::MAX),
                None,
                "{name} must refuse nothing while unset"
            );

            let mut set = HostLimits::UNBOUNDED;
            match name {
                "catalog_size" => set.catalog_size = Some(5),
                "clause_text_bytes" => set.clause_text_bytes = Some(5),
                "countermodel_retention_tuples" => set.countermodel_retention_tuples = Some(5),
                "drop_references" => set.drop_references = Some(5),
                "evaluation_cost" => set.evaluation_cost = Some(5),
                "level_bound" => set.level_bound = Some(5),
                "proposal_size" => set.proposal_size = Some(5),
                "pushed_core" => set.pushed_core = Some(5),
                "reply_bytes" => set.reply_bytes = Some(5),
                "strongest_refutations" => set.strongest_refutations = Some(5),
                other => panic!("{other} has no disposition in this test"),
            }
            assert_eq!(set.get(name), Some(5));
            assert_eq!(set.in_force(), vec![(name, 5)]);
            assert_eq!(set.refusal(name, 5), None, "{name} admits its own value");
            let refusal = set
                .refusal(name, 6)
                .unwrap_or_else(|| panic!("{name} must refuse 6 at a limit of 5"));
            assert_eq!(refusal.limit(), name);
            assert_eq!(refusal.value(), 5);
            assert_eq!(refusal.observed(), 6);
            assert_eq!(
                refusal.wire_value(),
                json!({"limit": name, "value": 5, "observed": 6})
            );
            // One code for every limit, and never a proposal defect.
            assert_eq!(HOST_LIMIT_CODE, "host_limit");
            assert!(refusal.message().contains("not a defect of the proposal"));
            // Setting one limit leaves every other absent.
            for other in HOST_LIMIT_NAMES.into_iter().filter(|other| *other != name) {
                assert_eq!(set.refusal(other, u64::MAX), None);
                assert_eq!(set.shown_of(other, 1_000), 1_000);
            }
            // Truncation follows the same rule.
            assert_eq!(set.shown_of(name, 4), 4);
            assert_eq!(set.shown_of(name, 9), 5);
            assert_eq!(
                HostLimitTruncation::of(&set, "items", name, 9).map(|t| t.wire_value()),
                Some(json!({"list": "items", "shown": 5, "total": 9, "limit": name}))
            );
        }
    }

    /// The presentation lists nothing by default, and lists exactly what is
    /// set otherwise, in a fixed order.
    #[test]
    fn the_presentation_list_is_empty_by_default() {
        assert_eq!(HostLimits::default().wire_value(), json!([]));
        let limits = HostLimits {
            reply_bytes: Some(1_024),
            catalog_size: Some(8),
            ..HostLimits::UNBOUNDED
        };
        assert_eq!(
            limits.wire_value(),
            json!([
                {"limit": "catalog_size", "value": 8},
                {"limit": "reply_bytes", "value": 1_024},
            ])
        );
    }

    /// The digest form carries every field, so clearing a limit is a
    /// different policy from never setting it alongside another.
    #[test]
    fn the_digest_form_carries_every_field() {
        let value = HostLimits::default().digest_value();
        let object = value.as_object().expect("the digest form is an object");
        assert_eq!(object.len(), HOST_LIMIT_NAMES.len());
        for name in HOST_LIMIT_NAMES {
            assert_eq!(object.get(name), Some(&Value::Null));
        }
    }
}
