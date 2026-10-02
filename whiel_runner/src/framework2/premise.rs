//! Tagged fixed-ambient verification-condition premises (Pass 7.5b).
//!
//! Lean assigns every axiom name it sends to the solver one of a small set
//! of semantic tags when it builds a verification condition (see
//! `reports/houdini/houdini.tex` Section 4.3, Definition "Tagged premises
//! and semantic key", and `TODO.md` Pass 7.5b's third scope bullet). Two
//! independent things build a [`FrameworkIIPremiseTag`] value:
//!
//! - [`tagged_premise_set`] computes the *full* tagged premise set Lean is
//!   known to build for a given `(clause, level, role)` request, and
//!   [`termination_tagged_premise_set`] the one Lean builds for the
//!   epoch's termination request, purely from Lean-issued clause-identity
//!   digests already held by the snapshot. Neither needs a worker round
//!   trip.
//! - [`FrameworkIIAxiomTagTable`] decodes the Lean-issued `axiom_tags`
//!   wire table from one worker preparation response,
//!   [`cited_tagged_premises_from_proof`] maps the axiom names a solver's
//!   own proof text cited through that table, and
//!   [`issued_tagged_premise_set`] reads the whole table back as a tagged
//!   set so the suites can assert that Rust's own computation agrees with
//!   the table (test-only since Pass 7.5d: on the live path the assembly
//!   differential compares the whole table against Lean's, byte for byte).
//!
//! Rust never infers a tag from an axiom's position or interprets formula
//! text: a name is either absent from the table (fails closed) or maps to
//! exactly the tag Lean assigned it.

use std::collections::BTreeMap;
use std::sync::Arc;

use serde_json::{Value, json};

use super::ledger::{FrameworkIICheckRequest, FrameworkIICheckRole};
use super::snapshot::LeveledCandidateSnapshot;
use super::types::FrameworkIILevel;

/// One tagged premise, matching the wire vocabulary of Lean's preparation
/// response `axiom_tags` table: `pre`, `guard`, `not_theta_guard`,
/// `plain(identity)`, `theta(identity)`, `support`, `not_guard`, or
/// `collapsed(identity)`. `Ord` is derived and used only to keep tagged
/// sets in one canonical, deterministic order; it carries no semantic
/// meaning of its own.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum FrameworkIIPremiseTag {
    Pre,
    Guard,
    NotThetaGuard,
    NotGuard,
    Support,
    Plain(Arc<str>),
    Theta(Arc<str>),
    Collapsed(Arc<str>),
}

impl FrameworkIIPremiseTag {
    pub(crate) fn to_json(&self) -> Value {
        match self {
            Self::Pre => json!({"tag": "pre", "identity": Value::Null}),
            Self::Guard => json!({"tag": "guard", "identity": Value::Null}),
            Self::NotThetaGuard => json!({"tag": "not_theta_guard", "identity": Value::Null}),
            Self::NotGuard => json!({"tag": "not_guard", "identity": Value::Null}),
            Self::Support => json!({"tag": "support", "identity": Value::Null}),
            Self::Plain(identity) => json!({"tag": "plain", "identity": identity.as_ref()}),
            Self::Theta(identity) => json!({"tag": "theta", "identity": identity.as_ref()}),
            Self::Collapsed(identity) => json!({"tag": "collapsed", "identity": identity.as_ref()}),
        }
    }

    /// Decode one wire `(tag, identity)` pair from Lean's `axiom_tags`
    /// table. Fails closed on any tag/identity combination outside the
    /// documented wire spec (an unsupported tag string, or a tag carrying
    /// an identity it should not, or missing one it must).
    pub(crate) fn from_wire(tag: &str, identity: Option<&str>) -> Result<Self, String> {
        match (tag, identity) {
            ("pre", None) => Ok(Self::Pre),
            ("guard", None) => Ok(Self::Guard),
            ("not_theta_guard", None) => Ok(Self::NotThetaGuard),
            ("not_guard", None) => Ok(Self::NotGuard),
            ("support", None) => Ok(Self::Support),
            ("plain", Some(identity)) => Ok(Self::Plain(Arc::from(identity))),
            ("theta", Some(identity)) => Ok(Self::Theta(Arc::from(identity))),
            ("collapsed", Some(identity)) => Ok(Self::Collapsed(Arc::from(identity))),
            _ => Err(format!(
                "unsupported axiom tag {tag:?} with identity {identity:?}"
            )),
        }
    }
}

/// A tagged premise multiset, represented as a sorted set: Lean never sends
/// the same axiom name twice for one obligation, and two occurrences of the
/// same tagged premise in one verification condition are indistinguishable
/// for subsumption.
pub(crate) type TaggedPremiseSet = std::collections::BTreeSet<FrameworkIIPremiseTag>;

pub(crate) fn tagged_premise_set_to_json(tags: &TaggedPremiseSet) -> Vec<Value> {
    tags.iter().map(FrameworkIIPremiseTag::to_json).collect()
}

/// Compute the full tagged premise set Lean is known to build for `request`,
/// entirely from Lean-issued clause-identity digests already held by the
/// snapshot, before any worker call.
///
/// - `Initialization` at level `j`: `{pre}`, plus (only when `j > 0`)
///   `{not_theta_guard}` and `{theta(d) : d strictly below j}`.
/// - `Maintenance` at level `j`: `{plain(d) : d at or below j, including
///   the conjecture}`, `{guard}`, plus (only when `j > 0`)
///   `{not_theta_guard}` and `{theta(d) : d strictly below j}`.
///
/// Level 0 carries no `not_theta_guard`/`theta` entries by construction
/// (Pass 7.5b's explicit exclusion, not merely an empty strictly-below set).
pub(crate) fn tagged_premise_set(request: &FrameworkIICheckRequest) -> TaggedPremiseSet {
    tagged_premise_set_at(request.snapshot(), request.level(), request.role())
}

/// [`tagged_premise_set`] for a `(snapshot, level, role)` triple that no
/// live request carries: the set Lean *would* build if the condition were
/// posed against `snapshot` at `checked_level`.
///
/// Pass 7.5f's freeze uses it to pose every one of the final Core's
/// conditions and ask which recorded launch closed that condition against
/// this Core rather than against an earlier one.
pub(crate) fn tagged_premise_set_at(
    snapshot: &LeveledCandidateSnapshot,
    checked_level: FrameworkIILevel,
    role: FrameworkIICheckRole,
) -> TaggedPremiseSet {
    let mut tags = TaggedPremiseSet::new();
    match role {
        FrameworkIICheckRole::Initialization => {
            tags.insert(FrameworkIIPremiseTag::Pre);
            if checked_level.get() > 0 {
                tags.insert(FrameworkIIPremiseTag::NotThetaGuard);
                insert_theta_strictly_below(&mut tags, snapshot, checked_level);
            }
        }
        FrameworkIICheckRole::Maintenance => {
            insert_plain_at_or_below(&mut tags, snapshot, checked_level);
            tags.insert(FrameworkIIPremiseTag::Guard);
            if checked_level.get() > 0 {
                tags.insert(FrameworkIIPremiseTag::NotThetaGuard);
                insert_theta_strictly_below(&mut tags, snapshot, checked_level);
            }
        }
    }
    tags
}

/// The full tagged premise set Lean builds for the epoch's termination
/// request over `core` (`houdini.tex` Section 4.4, Table 1, row
/// `Term(F)`): `{not_guard} ∪ {collapsed(d) : d ∈ Core}`. Like
/// [`tagged_premise_set`] this is computed entirely from Lean-issued
/// clause-identity digests already held by the snapshot, before any worker
/// call, and carries no level information: the termination request ranges
/// over the Core's clause *set*, never over its levels.
pub(crate) fn termination_tagged_premise_set(core: &LeveledCandidateSnapshot) -> TaggedPremiseSet {
    let mut tags = TaggedPremiseSet::new();
    tags.insert(FrameworkIIPremiseTag::NotGuard);
    for clause in core.canonical_order() {
        let record = core
            .records()
            .get(clause)
            .expect("canonical order clause has an immutable record");
        tags.insert(FrameworkIIPremiseTag::Collapsed(Arc::from(
            record.formula().identity_sha256(),
        )));
    }
    tags
}

/// The sorted, deduplicated Lean-issued identity list of `core`'s clauses,
/// without levels: the premise representation of the termination request's
/// semantic key (`houdini.tex` Section 4.4, Definition "Tagged premises and
/// semantic key": "for Term, T is represented by the sorted identity list
/// of F").
pub(crate) fn core_identity_list(core: &LeveledCandidateSnapshot) -> Vec<Arc<str>> {
    let mut identities: Vec<Arc<str>> = core
        .canonical_order()
        .iter()
        .map(|clause| {
            Arc::from(
                core.records()
                    .get(clause)
                    .expect("canonical order clause has an immutable record")
                    .formula()
                    .identity_sha256(),
            )
        })
        .collect();
    identities.sort();
    identities.dedup();
    identities
}

fn insert_theta_strictly_below(
    tags: &mut TaggedPremiseSet,
    snapshot: &LeveledCandidateSnapshot,
    checked_level: FrameworkIILevel,
) {
    for clause in snapshot.canonical_order() {
        let level = snapshot
            .level_of(*clause)
            .expect("canonical order only lists placed clauses");
        if level < checked_level {
            let record = snapshot
                .records()
                .get(clause)
                .expect("canonical order clause has an immutable record");
            tags.insert(FrameworkIIPremiseTag::Theta(Arc::from(
                record.formula().identity_sha256(),
            )));
        }
    }
}

fn insert_plain_at_or_below(
    tags: &mut TaggedPremiseSet,
    snapshot: &LeveledCandidateSnapshot,
    checked_level: FrameworkIILevel,
) {
    for clause in snapshot.canonical_order() {
        let level = snapshot
            .level_of(*clause)
            .expect("canonical order only lists placed clauses");
        if level <= checked_level {
            let record = snapshot
                .records()
                .get(clause)
                .expect("canonical order clause has an immutable record");
            tags.insert(FrameworkIIPremiseTag::Plain(Arc::from(
                record.formula().identity_sha256(),
            )));
        }
    }
}

/// The fixed conjecture name `entailment::assembly::render_query` always
/// writes (`fof(goal, conjecture, (...))`), independent of the obligation.
/// A real proof's own negated-conjecture step routinely carries a
/// `file(..., goal)` citation; that is never a premise, so
/// [`cited_tagged_premises_from_proof`] skips it rather than failing closed
/// on an "unknown" name. Lean's `axiom_tags` table never tags the
/// conjecture (`FixedAmbientWorker.lean`'s `prepareEntailmentJson` builds
/// entries only from `axiomBodies`/`roles` and the support block).
pub(crate) const FIXED_AMBIENT_CONJECTURE_TPTP_NAME: &str = "goal";

/// Translate one Lean-issued `axiom_tags` wire name into the short TPTP
/// declaration name `entailment::assembly::render_query` actually writes
/// into the problem file for that same axiom — the only name a real proof's
/// `file(...)` citation can ever carry. Lean's wire name is always
/// `"{prefix}.axiom.{index}"`, `"{prefix}.support.adom"`, or
/// `"{prefix}.support.distinct.{index}"` for the exact `prefix`
/// `fixed_ambient_obligation_source_prefix` computes from the obligation
/// identity (`FixedAmbientWorker.lean`'s `prepareEntailmentJson`); the
/// generic assembler writes the same axiom, respectively, as
/// `axiom_{index}`, `support_adom`, or `support_distinct_{index}`. This is a
/// deterministic decode of Lean's own name structure — every mapping is
/// keyed by the literal wire text after stripping the known prefix — never
/// an inference from the entry's position in the wire array; an
/// unrecognized suffix (including the conjecture's own
/// `"{prefix}.conjecture"`, which `axiom_tags` never actually emits) fails
/// closed to `None`.
///
/// Kept in sync with `entailment::assembly::render_query`'s naming scheme by
/// hand: the two modules share no naming constant, so a rename on either
/// side must update both (Pass 7.5b note).
pub(crate) fn fixed_ambient_tptp_name_for_wire_axiom_tag(
    prefix: &str,
    wire_name: &str,
) -> Option<Arc<str>> {
    let suffix = wire_name.strip_prefix(prefix)?.strip_prefix('.')?;
    if let Some(index) = suffix.strip_prefix("axiom.") {
        index.parse::<u64>().ok()?;
        return Some(Arc::from(format!("axiom_{index}")));
    }
    if suffix == "support.adom" {
        return Some(Arc::from("support_adom"));
    }
    if let Some(index) = suffix.strip_prefix("support.distinct.") {
        index.parse::<u64>().ok()?;
        return Some(Arc::from(format!("support_distinct_{index}")));
    }
    None
}

/// The Lean-issued `axiom_tags` table from one worker preparation response:
/// every positional axiom name Lean emitted, mapped to its tag. Lookup is by
/// exact name only — Rust never infers a tag from a name's position in the
/// wire array.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct FrameworkIIAxiomTagTable(Arc<BTreeMap<Arc<str>, FrameworkIIPremiseTag>>);

impl FrameworkIIAxiomTagTable {
    /// Build a table from `(name, tag)` pairs in wire order. Fails closed on
    /// a repeated name: the wire spec requires unique names, and a
    /// duplicate would make lookup ambiguous.
    pub(crate) fn from_entries(
        entries: Vec<(Arc<str>, FrameworkIIPremiseTag)>,
    ) -> Result<Self, String> {
        let mut map = BTreeMap::new();
        for (name, tag) in entries {
            if map.insert(Arc::clone(&name), tag).is_some() {
                return Err(format!("duplicate axiom name {name:?} in axiom_tags table"));
            }
        }
        Ok(Self(Arc::new(map)))
    }

    pub(crate) fn get(&self, name: &str) -> Option<&FrameworkIIPremiseTag> {
        self.0.get(name)
    }

    /// Every tag Lean actually issued for this preparation, with `support`
    /// entries dropped.
    ///
    /// `support` is excluded on this side because [`tagged_premise_set`]
    /// and [`termination_tagged_premise_set`] never produce it: the support
    /// block is a function of the constants that occur, not of the
    /// partition, so it is not part of the request's tagged premise set in
    /// the contract's sense. Every other tag is compared verbatim.
    /// Duplicate names are impossible ([`Self::from_entries`] fails closed
    /// on one), and two axioms carrying the identical tag are
    /// indistinguishable for subsumption, so the set is the multiset.
    ///
    /// Test-only: nothing on the production path reads a table back this
    /// way since Pass 7.5d made Rust the table's author.
    #[cfg(test)]
    pub(crate) fn issued_tagged_premise_set(&self) -> TaggedPremiseSet {
        self.0
            .values()
            .filter(|tag| !matches!(tag, FrameworkIIPremiseTag::Support))
            .cloned()
            .collect()
    }

    #[cfg(test)]
    pub(crate) fn for_test(entries: Vec<(&str, FrameworkIIPremiseTag)>) -> Self {
        Self::from_entries(
            entries
                .into_iter()
                .map(|(name, tag)| (Arc::from(name), tag))
                .collect(),
        )
        .expect("test axiom-tag table has unique names")
    }
}

/// Strict lexical scan for every `file(<anything>, <name>)` annotation in a
/// TPTP proof's text. Search-phase profiles pass `--output_axiom_names on`,
/// so Vampire cites each input axiom's name in a `file('<source>', <name>)`
/// annotation on the leaf steps that used it.
///
/// This never parses or interprets the surrounding formula: it only looks
/// for the literal substring `file(` and lexes the two comma-separated
/// arguments that follow it (a quoted string or a bare identifier token),
/// discarding the first (the source-file argument) and collecting the
/// second (the axiom name) verbatim. A malformed occurrence (no matching
/// arguments) is skipped rather than treated as a citation.
pub(crate) fn extract_cited_axiom_names(proof_text: &str) -> Vec<Arc<str>> {
    const MARKER: &str = "file(";
    let bytes = proof_text.as_bytes();
    let mut names = Vec::new();
    let mut search_from = 0usize;
    while let Some(relative) = proof_text[search_from..].find(MARKER) {
        let marker_start = search_from + relative;
        let mut cursor = marker_start + MARKER.len();
        cursor = skip_whitespace(bytes, cursor);
        if let Some((_, after_first)) = lex_token(bytes, cursor) {
            let mut next = skip_whitespace(bytes, after_first);
            if bytes.get(next) == Some(&b',') {
                next = skip_whitespace(bytes, next + 1);
                if let Some((name, after_second)) = lex_token(bytes, next) {
                    names.push(Arc::from(name.as_str()));
                    search_from = after_second;
                    continue;
                }
            }
        }
        // Not a well-formed `file(<a>, <b>)` occurrence at this position;
        // resume scanning right after this `file(` so later well-formed
        // occurrences are still found.
        search_from = marker_start + MARKER.len();
    }
    names
}

fn skip_whitespace(bytes: &[u8], mut pos: usize) -> usize {
    while pos < bytes.len() && (bytes[pos] as char).is_ascii_whitespace() {
        pos += 1;
    }
    pos
}

fn is_bare_identifier_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'.' || byte == b'-'
}

/// Lex one TPTP token starting at `pos`: a single-quoted string (TPTP
/// `single_quoted`, closed by the next unescaped `'`) or a bare run of
/// identifier bytes. Returns the token text and the byte offset just past
/// it, or `None` if `pos` starts neither.
fn lex_token(bytes: &[u8], pos: usize) -> Option<(String, usize)> {
    if pos >= bytes.len() {
        return None;
    }
    if bytes[pos] == b'\'' {
        let start = pos + 1;
        let mut cursor = start;
        while cursor < bytes.len() {
            if bytes[cursor] == b'\'' {
                let text = std::str::from_utf8(&bytes[start..cursor]).ok()?.to_owned();
                return Some((text, cursor + 1));
            }
            cursor += 1;
        }
        None
    } else {
        let start = pos;
        let mut cursor = pos;
        while cursor < bytes.len() && is_bare_identifier_byte(bytes[cursor]) {
            cursor += 1;
        }
        if cursor == start {
            return None;
        }
        let text = std::str::from_utf8(&bytes[start..cursor]).ok()?.to_owned();
        Some((text, cursor))
    }
}

/// How a proof entry's cited tagged premise set was obtained.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CitedTaggedPremiseSource {
    /// Every `file(..., name)` citation of the proof text resolved through
    /// Lean's `axiom_tags` table.
    ProofCitations,
    /// The citations failed closed — the proof named no axiom at all, or it
    /// named one absent from the table — so the request's own full tagged
    /// premise set stands in for the cited set.
    FullTaggedSetFallback,
}

/// Map a proof's cited axiom names through `table` into a tagged premise
/// set, falling back to the request's own full tagged premise set whenever
/// the citations fail closed (`houdini.tex` Section 4.4, Definition
/// "Subsumption": "on an unknown name or an empty citation it records the
/// request's full tagged set instead, which is always a sound cited set").
///
/// - a proof citing zero named axioms, or citing a name absent from
///   `table`, yields `full.clone()` tagged
///   [`CitedTaggedPremiseSource::FullTaggedSetFallback`]. The full set is
///   always sound as a cited set: the solver proved the conjecture from
///   *some* subset of the request's own premises, so every later request
///   containing the full set also contains whatever the proof really used.
///   It is merely weaker — it subsumes fewer later requests than the exact
///   citation would.
/// - otherwise every cited `support`-tagged name is dropped and the
///   remaining tags are returned, possibly empty (a proof citing only
///   support axioms legitimately matches every request sharing the same
///   tagged conjecture).
pub(crate) fn cited_tagged_premises_from_proof(
    proof_text: &str,
    table: &FrameworkIIAxiomTagTable,
    full: &TaggedPremiseSet,
) -> (TaggedPremiseSet, CitedTaggedPremiseSource) {
    let fallback = || {
        (
            full.clone(),
            CitedTaggedPremiseSource::FullTaggedSetFallback,
        )
    };
    let names = extract_cited_axiom_names(proof_text);
    if names.is_empty() {
        return fallback();
    }
    let mut tags = TaggedPremiseSet::new();
    for name in names {
        if name.as_ref() == FIXED_AMBIENT_CONJECTURE_TPTP_NAME {
            // The proof's own citation of its negated conjecture is not a
            // premise; `axiom_tags` never tags it (see the constant's doc).
            continue;
        }
        match table.get(&name) {
            Some(FrameworkIIPremiseTag::Support) => {}
            Some(tag) => {
                tags.insert(tag.clone());
            }
            None => return fallback(),
        }
    }
    (tags, CitedTaggedPremiseSource::ProofCitations)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn theta_and_plain_of_the_same_identity_are_distinct_tags() {
        let identity: Arc<str> = Arc::from("a".repeat(64));
        let theta = FrameworkIIPremiseTag::Theta(Arc::clone(&identity));
        let plain = FrameworkIIPremiseTag::Plain(identity);
        assert_ne!(theta, plain);
        let mut set = TaggedPremiseSet::new();
        set.insert(theta.clone());
        assert!(!set.contains(&plain));
        set.insert(plain);
        assert_eq!(set.len(), 2, "a theta tag never collapses into a plain tag");
    }

    #[test]
    fn from_wire_rejects_unsupported_shapes() {
        assert!(FrameworkIIPremiseTag::from_wire("pre", None).is_ok());
        assert!(FrameworkIIPremiseTag::from_wire("pre", Some("x")).is_err());
        assert!(FrameworkIIPremiseTag::from_wire("plain", None).is_err());
        assert!(FrameworkIIPremiseTag::from_wire("plain", Some("x")).is_ok());
        assert!(FrameworkIIPremiseTag::from_wire("nonsense", None).is_err());
    }

    #[test]
    fn axiom_tag_table_fails_closed_on_a_duplicate_name() {
        let entries = vec![
            (Arc::from("ax1"), FrameworkIIPremiseTag::Pre),
            (Arc::from("ax1"), FrameworkIIPremiseTag::Guard),
        ];
        assert!(FrameworkIIAxiomTagTable::from_entries(entries).is_err());
    }

    #[test]
    fn extraction_reads_a_realistic_tptp_proof_fixture() {
        let proof = "\
% SZS status Theorem for problem
% SZS output start Proof for problem
fof(f1, axiom, (foo), file('problem.p', framework_ii.fixed_ambient.axiom.3)).
fof(f2, axiom, (bar), file('problem.p', framework_ii.fixed_ambient.axiom.7)).
fof(f9, plain, ($false), inference(resolution, [], [f1, f2])).
% SZS output end Proof for problem";
        let names = extract_cited_axiom_names(proof);
        assert_eq!(
            names.iter().map(|name| name.as_ref()).collect::<Vec<_>>(),
            vec![
                "framework_ii.fixed_ambient.axiom.3",
                "framework_ii.fixed_ambient.axiom.7",
            ]
        );
    }

    fn full_fixture_set() -> TaggedPremiseSet {
        TaggedPremiseSet::from([
            FrameworkIIPremiseTag::Pre,
            FrameworkIIPremiseTag::NotThetaGuard,
            FrameworkIIPremiseTag::Theta(Arc::from("b".repeat(64))),
        ])
    }

    #[test]
    fn cited_tagged_premises_fall_back_to_the_full_set_on_an_empty_citation() {
        let table = FrameworkIIAxiomTagTable::for_test(vec![]);
        let proof = "% SZS status Theorem for problem\n1. $false [fixture]";
        let full = full_fixture_set();
        let (cited, source) = cited_tagged_premises_from_proof(proof, &table, &full);
        assert_eq!(cited, full);
        assert_eq!(source, CitedTaggedPremiseSource::FullTaggedSetFallback);
    }

    #[test]
    fn cited_tagged_premises_fall_back_to_the_full_set_on_an_unknown_name() {
        let table = FrameworkIIAxiomTagTable::for_test(vec![("known", FrameworkIIPremiseTag::Pre)]);
        let proof = "fof(f1, axiom, (foo), file('problem.p', unknown_name)).";
        let full = full_fixture_set();
        let (cited, source) = cited_tagged_premises_from_proof(proof, &table, &full);
        assert_eq!(cited, full);
        assert_eq!(source, CitedTaggedPremiseSource::FullTaggedSetFallback);
    }

    #[test]
    fn cited_tagged_premises_drops_support_and_keeps_the_rest() {
        let table = FrameworkIIAxiomTagTable::for_test(vec![
            ("ax_pre", FrameworkIIPremiseTag::Pre),
            ("ax_support", FrameworkIIPremiseTag::Support),
        ]);
        let proof = "fof(f1, axiom, (foo), file('problem.p', ax_pre)).\n\
             fof(f2, axiom, (bar), file('problem.p', ax_support)).";
        let (cited, source) = cited_tagged_premises_from_proof(proof, &table, &full_fixture_set());
        assert_eq!(cited, TaggedPremiseSet::from([FrameworkIIPremiseTag::Pre]));
        assert_eq!(source, CitedTaggedPremiseSource::ProofCitations);
    }

    #[test]
    fn cited_tagged_premises_citing_only_support_yields_an_empty_set() {
        let table = FrameworkIIAxiomTagTable::for_test(vec![(
            "ax_support",
            FrameworkIIPremiseTag::Support,
        )]);
        let proof = "fof(f1, axiom, (foo), file('problem.p', ax_support)).";
        let (cited, source) = cited_tagged_premises_from_proof(proof, &table, &full_fixture_set());
        assert!(cited.is_empty());
        assert_eq!(source, CitedTaggedPremiseSource::ProofCitations);
    }

    #[test]
    fn the_full_tagged_set_fallback_stays_sound_under_subsumption() {
        // A proof-entry cited set is reused only for a request whose own
        // tagged set contains it. With the fallback the cited set is the
        // original request's full set, so the only requests that hit it
        // are those carrying every premise the original had — the original
        // proof's real (unknown) cited subset is contained in each of them.
        let table = FrameworkIIAxiomTagTable::for_test(vec![("known", FrameworkIIPremiseTag::Pre)]);
        let proof = "fof(f1, axiom, (foo), file('problem.p', unknown_name)).";
        let full = full_fixture_set();
        let (cited, _) = cited_tagged_premises_from_proof(proof, &table, &full);
        let strictly_smaller = TaggedPremiseSet::from([FrameworkIIPremiseTag::Pre]);
        assert!(!cited.is_subset(&strictly_smaller));
        let mut larger = full.clone();
        larger.insert(FrameworkIIPremiseTag::Guard);
        assert!(cited.is_subset(&larger));
    }

    #[test]
    fn the_issued_table_reads_back_as_a_tagged_set_without_support() {
        let table = FrameworkIIAxiomTagTable::for_test(vec![
            ("axiom_0", FrameworkIIPremiseTag::Pre),
            ("axiom_1", FrameworkIIPremiseTag::NotThetaGuard),
            ("support_adom", FrameworkIIPremiseTag::Support),
            ("support_distinct_0", FrameworkIIPremiseTag::Support),
        ]);
        assert_eq!(
            table.issued_tagged_premise_set(),
            TaggedPremiseSet::from([
                FrameworkIIPremiseTag::Pre,
                FrameworkIIPremiseTag::NotThetaGuard,
            ])
        );
    }
}
