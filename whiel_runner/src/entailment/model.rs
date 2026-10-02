//! Strict decoding of complete Vampire finite-model output.
//!
//! This parser accepts the finite-model syntax emitted by the supported
//! Vampire worker. It is deliberately not a general TPTP parser. Any source
//! relation whose declaration or interpretation falls outside this syntax is
//! rejected instead of being approximated.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::encoding::{NameMappingKind, TaskNameEnv};
use crate::task::{ConstantKey, RelationKey, SynthesisTask, TaskIdentity};

// ------------------------------------------------------------
// Decoded Source Instance
// ------------------------------------------------------------

/// One source-domain value retained by a decoded finite instance.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InstanceValue {
    /// The exact task-scoped constant whose denotation is this model element.
    Constant(ConstantKey),
    /// A stable task-local name for an active model element without a constant.
    Fresh(u64),
}

/// One complete source-relation table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecodedRelation {
    arity: u64,
    true_tuples: BTreeSet<Vec<InstanceValue>>,
}

impl DecodedRelation {
    /// Return the schema arity of this relation.
    pub fn arity(&self) -> u64 {
        self.arity
    }

    /// Return exactly the tuples which are true in the finite model.
    pub fn true_tuples(&self) -> &BTreeSet<Vec<InstanceValue>> {
        &self.true_tuples
    }

    /// Return the truth value of a nullary relation.
    pub fn nullary_value(&self) -> Option<bool> {
        (self.arity == 0).then(|| self.true_tuples.contains(&Vec::new()))
    }
}

/// One immutable, task-bound, schema-complete decoded instance.
#[derive(Clone, Debug)]
pub struct DecodedInstance {
    task: TaskIdentity,
    relations: BTreeMap<RelationKey, DecodedRelation>,
}

impl DecodedInstance {
    /// Construct the unique empty-active-domain instance for one complete
    /// assignment of the task's nullary relations.
    ///
    /// Every positive-arity relation is present with an empty table. Every
    /// nullary relation must occur exactly once in `nullary_values`.
    pub fn empty_active_domain(
        task: &SynthesisTask,
        nullary_values: impl IntoIterator<Item = (RelationKey, bool)>,
    ) -> Result<Self, EmptyInstanceError> {
        let schema = task
            .solver_relations()
            .iter()
            .map(|relation| (relation.key().clone(), relation.arity()))
            .collect::<BTreeMap<_, _>>();
        let mut assignments = BTreeMap::new();
        for (key, value) in nullary_values {
            let Some(arity) = schema.get(&key) else {
                return Err(EmptyInstanceError::UnknownRelation(
                    key.as_str().to_string(),
                ));
            };
            if *arity != 0 {
                return Err(EmptyInstanceError::NonNullaryAssignment {
                    relation: key.as_str().to_string(),
                    arity: *arity,
                });
            }
            if assignments.insert(key.clone(), value).is_some() {
                return Err(EmptyInstanceError::DuplicateAssignment(
                    key.as_str().to_string(),
                ));
            }
        }

        let mut relations = BTreeMap::new();
        for relation in task.solver_relations() {
            let true_tuples = if relation.arity() == 0 {
                let value = assignments.remove(relation.key()).ok_or_else(|| {
                    EmptyInstanceError::MissingAssignment(relation.key().as_str().to_string())
                })?;
                if value {
                    BTreeSet::from([Vec::new()])
                } else {
                    BTreeSet::new()
                }
            } else {
                BTreeSet::new()
            };
            relations.insert(
                relation.key().clone(),
                DecodedRelation {
                    arity: relation.arity(),
                    true_tuples,
                },
            );
        }
        debug_assert!(assignments.is_empty());
        Ok(Self {
            task: task.identity().clone(),
            relations,
        })
    }

    /// Return the exact task which owns this instance.
    pub fn task_identity(&self) -> &TaskIdentity {
        &self.task
    }

    /// Return every source relation, including empty and nullary relations.
    pub fn relations(&self) -> &BTreeMap<RelationKey, DecodedRelation> {
        &self.relations
    }

    /// Look up one source relation by its exact task-scoped key.
    pub fn relation(&self, key: &RelationKey) -> Option<&DecodedRelation> {
        self.relations.get(key)
    }
}

/// A schema error while constructing an empty-active-domain instance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EmptyInstanceError {
    UnknownRelation(String),
    NonNullaryAssignment { relation: String, arity: u64 },
    DuplicateAssignment(String),
    MissingAssignment(String),
}

impl fmt::Display for EmptyInstanceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownRelation(relation) => {
                write!(formatter, "unknown relation {relation:?}")
            }
            Self::NonNullaryAssignment { relation, arity } => write!(
                formatter,
                "relation {relation:?} has arity {arity}, not arity zero"
            ),
            Self::DuplicateAssignment(relation) => {
                write!(formatter, "duplicate nullary assignment for {relation:?}")
            }
            Self::MissingAssignment(relation) => {
                write!(formatter, "missing nullary assignment for {relation:?}")
            }
        }
    }
}

impl std::error::Error for EmptyInstanceError {}

// ------------------------------------------------------------
// Decode Errors
// ------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModelDecodeError {
    Envelope(String),
    Syntax(String),
    NameEnvironment(String),
    Domain(String),
    Constant(String),
    Relation { relation: String, detail: String },
}

impl fmt::Display for ModelDecodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Envelope(detail) => write!(formatter, "invalid finite-model envelope: {detail}"),
            Self::Syntax(detail) => write!(formatter, "unsupported finite-model syntax: {detail}"),
            Self::NameEnvironment(detail) => {
                write!(formatter, "inconsistent task NameEnv: {detail}")
            }
            Self::Domain(detail) => write!(formatter, "invalid finite domain: {detail}"),
            Self::Constant(detail) => {
                write!(formatter, "invalid constant interpretation: {detail}")
            }
            Self::Relation { relation, detail } => {
                write!(formatter, "invalid interpretation of {relation}: {detail}")
            }
        }
    }
}

impl std::error::Error for ModelDecodeError {}

// ------------------------------------------------------------
// Public Decode Boundary
// ------------------------------------------------------------

/// Decode one complete Vampire finite model for `task`.
///
/// The NameEnv supplies the only accepted reverse mapping from solver symbols
/// to source symbols. The result contains no Vampire-internal predicate,
/// function, or isolated domain element.
pub fn decode_vampire_model(
    task: &SynthesisTask,
    names: &TaskNameEnv,
    stdout: &str,
) -> Result<DecodedInstance, ModelDecodeError> {
    let model_text = finite_model_envelope(stdout)?;
    let statements = parse_tff_statements(model_text)?;
    let reverse = ReverseNameEnv::new(task, names)?;
    let raw = RawModel::parse(task, &reverse, &statements)?;
    raw.finish(task, reverse)
}

/// One complete finite model over an explicitly supplied relation schema.
///
/// This crate-private representation deliberately retains Vampire's domain
/// element names.  The fixed-ambient boundary replaces them with canonical
/// concrete-data keys before any interpretation reaches Lean.
#[derive(Clone, Debug)]
pub(crate) struct DecodedFiniteModel {
    pub(crate) carrier: BTreeSet<String>,
    pub(crate) constant_values: BTreeMap<ConstantKey, String>,
    pub(crate) relations: BTreeMap<RelationKey, DecodedFiniteRelation>,
}

/// One complete relation table in an explicitly scoped finite model.
#[derive(Clone, Debug)]
pub(crate) struct DecodedFiniteRelation {
    pub(crate) arity: u64,
    pub(crate) true_tuples: BTreeSet<Vec<String>>,
}

/// Decode one complete Vampire finite model over an exact relation schema.
///
/// Unlike [`decode_vampire_model`], this path retains the whole finite carrier
/// and permits caller-supplied relations such as fixed-ambient prophecies.  It
/// also requires every listed obligation constant to occur with a complete
/// declaration and interpretation in the model.
pub(crate) fn decode_vampire_model_for_relations(
    names: &TaskNameEnv,
    relations: &[(RelationKey, u64)],
    required_constants: &[ConstantKey],
    stdout: &str,
    query: Option<&str>,
) -> Result<DecodedFiniteModel, ModelDecodeError> {
    let relation_arities = exact_relation_arities(relations)?;
    let required_constant_count = required_constants.len();
    let required_constants = required_constants.iter().cloned().collect::<BTreeSet<_>>();
    if required_constants.len() != required_constant_count {
        return Err(ModelDecodeError::NameEnvironment(
            "duplicate required obligation constant".to_string(),
        ));
    }
    let model_text = finite_model_envelope(stdout)?;
    let statements = parse_tff_statements(model_text)?;
    let reverse = ReverseNameEnv::new_exact(names, &relation_arities, &required_constants)?;
    let raw = RawModel::parse_exact(&relation_arities, &reverse, &statements)?;
    raw.finish_exact(&relation_arities, &required_constants, reverse, query)
}

/// Whether the problem the solver was handed mentions this solver name at
/// all, as a whole token.
///
/// TPTP names are ASCII alphanumerics and underscores, so a name that
/// occurs only as part of a longer name is not an occurrence of it.
fn query_mentions(query: &str, solver_name: &str) -> bool {
    if solver_name.is_empty() {
        return true;
    }
    let bytes = query.as_bytes();
    let name = solver_name.as_bytes();
    let boundary = |byte: u8| !(byte.is_ascii_alphanumeric() || byte == b'_');
    let mut from = 0;
    while let Some(offset) = query[from..].find(solver_name) {
        let start = from + offset;
        let end = start + name.len();
        let before = start == 0 || boundary(bytes[start - 1]);
        let after = end == bytes.len() || boundary(bytes[end]);
        if before && after {
            return true;
        }
        from = start + 1;
    }
    false
}

fn exact_relation_arities(
    relations: &[(RelationKey, u64)],
) -> Result<BTreeMap<RelationKey, u64>, ModelDecodeError> {
    let mut arities = BTreeMap::new();
    for (key, arity) in relations {
        if arities.insert(key.clone(), *arity).is_some() {
            return Err(ModelDecodeError::NameEnvironment(format!(
                "duplicate exact-schema relation {:?}",
                key.as_str()
            )));
        }
    }
    Ok(arities)
}

// ------------------------------------------------------------
// Exact NameEnv Reversal
// ------------------------------------------------------------

#[derive(Clone)]
enum SourceSymbol {
    Relation(RelationKey),
    Constant(ConstantKey),
    NonSourceRelation,
}

struct ReverseNameEnv {
    by_solver_name: BTreeMap<String, SourceSymbol>,
    source_relations: BTreeMap<RelationKey, String>,
}

impl ReverseNameEnv {
    fn new(task: &SynthesisTask, names: &TaskNameEnv) -> Result<Self, ModelDecodeError> {
        let schema_by_text = task
            .solver_relations()
            .iter()
            .map(|relation| (relation.key().as_str(), relation.key().clone()))
            .collect::<BTreeMap<_, _>>();
        let mut by_solver_name = BTreeMap::new();
        let mut source_relations = BTreeMap::new();
        let mut source_keys = BTreeSet::new();
        let mut constant_keys = BTreeSet::new();

        for mapping in names.all_mappings() {
            let symbol = match mapping.kind {
                NameMappingKind::Relation => {
                    if !source_keys.insert(mapping.key.clone()) {
                        return Err(ModelDecodeError::NameEnvironment(format!(
                            "duplicate relation key {:?}",
                            mapping.key
                        )));
                    }
                    if let Some(key) = schema_by_text.get(mapping.key.as_str()) {
                        source_relations.insert(key.clone(), mapping.tptp_name.clone());
                        SourceSymbol::Relation(key.clone())
                    } else {
                        SourceSymbol::NonSourceRelation
                    }
                }
                NameMappingKind::Constant => {
                    if !constant_keys.insert(mapping.key.clone()) {
                        return Err(ModelDecodeError::NameEnvironment(format!(
                            "duplicate constant key {:?}",
                            mapping.key
                        )));
                    }
                    let key =
                        ConstantKey::from_canonical(mapping.key.clone()).map_err(|error| {
                            ModelDecodeError::NameEnvironment(format!(
                                "invalid constant key {:?}: {error}",
                                mapping.key
                            ))
                        })?;
                    SourceSymbol::Constant(key)
                }
            };
            if by_solver_name
                .insert(mapping.tptp_name.clone(), symbol)
                .is_some()
            {
                return Err(ModelDecodeError::NameEnvironment(format!(
                    "solver name {:?} has more than one reverse mapping",
                    mapping.tptp_name
                )));
            }
        }

        for relation in task.solver_relations() {
            if !source_relations.contains_key(relation.key()) {
                return Err(ModelDecodeError::NameEnvironment(format!(
                    "schema relation {:?} has no solver name",
                    relation.key().as_str()
                )));
            }
        }
        Ok(Self {
            by_solver_name,
            source_relations,
        })
    }

    fn new_exact(
        names: &TaskNameEnv,
        relation_arities: &BTreeMap<RelationKey, u64>,
        required_constants: &BTreeSet<ConstantKey>,
    ) -> Result<Self, ModelDecodeError> {
        let relations_by_text = relation_arities
            .keys()
            .map(|key| (key.as_str().to_string(), key.clone()))
            .collect::<BTreeMap<_, _>>();
        let mut by_solver_name = BTreeMap::new();
        let mut source_relations = BTreeMap::new();
        let mut source_keys = BTreeSet::new();
        let mut constant_keys = BTreeSet::new();

        for mapping in names.all_mappings() {
            let symbol = match mapping.kind {
                NameMappingKind::Relation => {
                    if !source_keys.insert(mapping.key.clone()) {
                        return Err(ModelDecodeError::NameEnvironment(format!(
                            "duplicate relation key {:?}",
                            mapping.key
                        )));
                    }
                    let key = relations_by_text.get(&mapping.key).ok_or_else(|| {
                        ModelDecodeError::NameEnvironment(format!(
                            "relation key {:?} lies outside the exact relation schema",
                            mapping.key
                        ))
                    })?;
                    source_relations.insert(key.clone(), mapping.tptp_name.clone());
                    SourceSymbol::Relation(key.clone())
                }
                NameMappingKind::Constant => {
                    if !constant_keys.insert(mapping.key.clone()) {
                        return Err(ModelDecodeError::NameEnvironment(format!(
                            "duplicate constant key {:?}",
                            mapping.key
                        )));
                    }
                    let key =
                        ConstantKey::from_canonical(mapping.key.clone()).map_err(|error| {
                            ModelDecodeError::NameEnvironment(format!(
                                "invalid constant key {:?}: {error}",
                                mapping.key
                            ))
                        })?;
                    SourceSymbol::Constant(key)
                }
            };
            if by_solver_name
                .insert(mapping.tptp_name.clone(), symbol)
                .is_some()
            {
                return Err(ModelDecodeError::NameEnvironment(format!(
                    "solver name {:?} has more than one reverse mapping",
                    mapping.tptp_name
                )));
            }
        }

        for key in relation_arities.keys() {
            if !source_relations.contains_key(key) {
                return Err(ModelDecodeError::NameEnvironment(format!(
                    "exact-schema relation {:?} has no solver name",
                    key.as_str()
                )));
            }
        }
        for key in required_constants {
            if !constant_keys.contains(key.as_str()) {
                return Err(ModelDecodeError::NameEnvironment(format!(
                    "required obligation constant {:?} has no solver name",
                    key.as_str()
                )));
            }
        }
        Ok(Self {
            by_solver_name,
            source_relations,
        })
    }

    fn symbol(&self, solver_name: &str) -> Option<&SourceSymbol> {
        self.by_solver_name.get(solver_name)
    }

    fn source_relation_name(&self, key: &RelationKey) -> &str {
        self.source_relations
            .get(key)
            .expect("every schema relation was validated")
    }

    fn source_relation_in(&self, formula: &str) -> bool {
        formula_symbols(formula)
            .iter()
            .any(|symbol| matches!(self.symbol(symbol), Some(SourceSymbol::Relation(_))))
    }

    fn source_constant_in(&self, formula: &str) -> bool {
        formula_symbols(formula)
            .iter()
            .any(|symbol| matches!(self.symbol(symbol), Some(SourceSymbol::Constant(_))))
    }
}

// ------------------------------------------------------------
// SZS Envelope
// ------------------------------------------------------------

fn finite_model_envelope(stdout: &str) -> Result<&str, ModelDecodeError> {
    const STATUS: &str = "% SZS status CounterSatisfiable for ";
    const START: &str = "% SZS output start FiniteModel for ";
    const END: &str = "% SZS output end FiniteModel for ";

    let mut status_problem = None;
    let mut status_offset = None;
    let mut start = None;
    let mut start_problem = None;
    let mut end = None;
    let mut end_problem = None;
    let mut offset = 0;

    for segment in stdout.split_inclusive('\n') {
        let line = segment.trim_end_matches(['\r', '\n']);
        if let Some(problem) = line.strip_prefix("% SZS status ") {
            let Some(problem) = problem.strip_prefix("CounterSatisfiable for ") else {
                return Err(ModelDecodeError::Envelope(format!(
                    "unexpected SZS status line {line:?}"
                )));
            };
            if status_problem.replace(problem.to_string()).is_some() {
                return Err(ModelDecodeError::Envelope(
                    "more than one SZS status line".to_string(),
                ));
            }
            status_offset = Some(offset);
        } else if let Some(problem) = line.strip_prefix(START) {
            if start.replace(offset + segment.len()).is_some() {
                return Err(ModelDecodeError::Envelope(
                    "more than one FiniteModel start marker".to_string(),
                ));
            }
            start_problem = Some(problem.to_string());
        } else if let Some(problem) = line.strip_prefix(END) {
            if end.replace(offset).is_some() {
                return Err(ModelDecodeError::Envelope(
                    "more than one FiniteModel end marker".to_string(),
                ));
            }
            end_problem = Some(problem.to_string());
        }
        offset += segment.len();
    }

    let status_problem = status_problem
        .ok_or_else(|| ModelDecodeError::Envelope(format!("missing {STATUS:?} status line")))?;
    let start = start.ok_or_else(|| {
        ModelDecodeError::Envelope("missing FiniteModel start marker".to_string())
    })?;
    let end = end
        .ok_or_else(|| ModelDecodeError::Envelope("missing FiniteModel end marker".to_string()))?;
    if end < start {
        return Err(ModelDecodeError::Envelope(
            "FiniteModel end marker precedes its start marker".to_string(),
        ));
    }
    if status_offset.is_some_and(|status| status >= start) {
        return Err(ModelDecodeError::Envelope(
            "CounterSatisfiable status does not precede the FiniteModel envelope".to_string(),
        ));
    }
    if start_problem.as_deref() != Some(status_problem.as_str())
        || end_problem.as_deref() != Some(status_problem.as_str())
    {
        return Err(ModelDecodeError::Envelope(
            "status and FiniteModel markers name different problems".to_string(),
        ));
    }
    Ok(&stdout[start..end])
}

// ------------------------------------------------------------
// TFF Record Splitting
// ------------------------------------------------------------

#[derive(Debug)]
struct TffStatement {
    name: String,
    role: String,
    formula: String,
}

fn parse_tff_statements(model: &str) -> Result<Vec<TffStatement>, ModelDecodeError> {
    let mut statements = Vec::new();
    let mut cursor = 0;
    let bytes = model.as_bytes();
    while cursor < bytes.len() {
        skip_space_and_comments(model, &mut cursor);
        if cursor == bytes.len() {
            break;
        }
        if !model[cursor..].starts_with("tff(") {
            return Err(ModelDecodeError::Syntax(format!(
                "expected tff statement near {:?}",
                preview(&model[cursor..])
            )));
        }
        let open = cursor + 3;
        let close = matching_delimiter(model, open, '(', ')')?;
        let after = skip_ascii_space(model, close + 1);
        if model.as_bytes().get(after) != Some(&b'.') {
            return Err(ModelDecodeError::Syntax(
                "tff statement does not end with '.'".to_string(),
            ));
        }
        let fields = split_top_level(&model[open + 1..close], ',')?;
        if fields.len() != 3 {
            return Err(ModelDecodeError::Syntax(format!(
                "tff statement has {} top-level fields instead of 3",
                fields.len()
            )));
        }
        statements.push(TffStatement {
            name: parse_atom(fields[0])?,
            role: parse_atom(fields[1])?,
            formula: fields[2].trim().to_string(),
        });
        cursor = after + 1;
    }
    if statements.is_empty() {
        return Err(ModelDecodeError::Syntax(
            "FiniteModel envelope contains no tff statements".to_string(),
        ));
    }
    Ok(statements)
}

fn skip_space_and_comments(text: &str, cursor: &mut usize) {
    loop {
        *cursor = skip_ascii_space(text, *cursor);
        if text.as_bytes().get(*cursor) != Some(&b'%') {
            return;
        }
        *cursor = text[*cursor..]
            .find('\n')
            .map_or(text.len(), |length| *cursor + length + 1);
    }
}

fn skip_ascii_space(text: &str, mut cursor: usize) -> usize {
    while text
        .as_bytes()
        .get(cursor)
        .is_some_and(u8::is_ascii_whitespace)
    {
        cursor += 1;
    }
    cursor
}

fn preview(text: &str) -> String {
    text.chars().take(40).collect()
}

// ------------------------------------------------------------
// Raw Model Collection
// ------------------------------------------------------------

#[derive(Default)]
struct RawRelation {
    declared_arity: Option<u64>,
    interpretation: Option<BTreeMap<Vec<String>, bool>>,
}

#[derive(Default)]
struct RawModel {
    declarations: BTreeMap<String, String>,
    duplicate_declarations: BTreeSet<String>,
    domain: Option<BTreeSet<String>>,
    relations: BTreeMap<RelationKey, RawRelation>,
    constant_values: BTreeMap<ConstantKey, String>,
    seen_constant_declarations: BTreeSet<ConstantKey>,
}

impl RawModel {
    fn parse(
        task: &SynthesisTask,
        reverse: &ReverseNameEnv,
        statements: &[TffStatement],
    ) -> Result<Self, ModelDecodeError> {
        let mut model = Self::default();
        for relation in task.solver_relations() {
            model
                .relations
                .insert(relation.key().clone(), RawRelation::default());
        }

        for statement in statements {
            if statement.role == "type" {
                model.parse_declaration(statement, reverse)?;
                continue;
            }
            if statement.name == "finite_domain_$i" {
                if statement.role != "axiom" {
                    return Err(ModelDecodeError::Domain(
                        "finite-domain declaration is not an axiom".to_string(),
                    ));
                }
                let domain = parse_finite_domain(&statement.formula)?;
                if model.domain.replace(domain).is_some() {
                    return Err(ModelDecodeError::Domain(
                        "duplicate finite-domain declaration".to_string(),
                    ));
                }
                continue;
            }
            if reverse.source_relation_in(&statement.formula) {
                model.parse_relation_interpretation(statement, reverse)?;
                continue;
            }
            if reverse.source_constant_in(&statement.formula) {
                model.parse_constant_interpretation(statement, reverse)?;
            }
        }
        Ok(model)
    }

    fn parse_exact(
        relation_arities: &BTreeMap<RelationKey, u64>,
        reverse: &ReverseNameEnv,
        statements: &[TffStatement],
    ) -> Result<Self, ModelDecodeError> {
        let mut model = Self::default();
        for key in relation_arities.keys() {
            model.relations.insert(key.clone(), RawRelation::default());
        }

        for statement in statements {
            if statement.role == "type" {
                model.parse_declaration(statement, reverse)?;
                continue;
            }
            if statement.name == "finite_domain_$i" {
                if statement.role != "axiom" {
                    return Err(ModelDecodeError::Domain(
                        "finite-domain declaration is not an axiom".to_string(),
                    ));
                }
                let domain = parse_finite_domain(&statement.formula)?;
                if model.domain.replace(domain).is_some() {
                    return Err(ModelDecodeError::Domain(
                        "duplicate finite-domain declaration".to_string(),
                    ));
                }
                continue;
            }
            if reverse.source_relation_in(&statement.formula) {
                model.parse_relation_interpretation(statement, reverse)?;
                continue;
            }
            if reverse.source_constant_in(&statement.formula) {
                model.parse_constant_interpretation(statement, reverse)?;
            }
        }
        Ok(model)
    }

    fn parse_declaration(
        &mut self,
        statement: &TffStatement,
        reverse: &ReverseNameEnv,
    ) -> Result<(), ModelDecodeError> {
        let Some((raw_name, raw_type)) = split_top_level_once(&statement.formula, ':')? else {
            return Err(ModelDecodeError::Syntax(format!(
                "type statement {:?} has no top-level ':'",
                statement.name
            )));
        };
        let name = parse_atom(raw_name)?;
        let type_text = compact(raw_type);
        if self.declarations.contains_key(&name) {
            self.duplicate_declarations.insert(name.clone());
        } else {
            self.declarations.insert(name.clone(), type_text.clone());
        }

        match reverse.symbol(&name) {
            Some(SourceSymbol::Relation(key)) => {
                let arity = relation_type_arity(&type_text).ok_or_else(|| {
                    relation_error(key, format!("unsupported type {type_text:?}"))
                })?;
                let relation = self
                    .relations
                    .get_mut(key)
                    .expect("source relation was initialized");
                if relation.declared_arity.replace(arity).is_some() {
                    return Err(relation_error(key, "duplicate type declaration"));
                }
            }
            Some(SourceSymbol::Constant(key)) => {
                if type_text != "$i" {
                    return Err(ModelDecodeError::Constant(format!(
                        "constant {:?} has type {type_text:?} instead of $i",
                        key.as_str()
                    )));
                }
                if !self.seen_constant_declarations.insert(key.clone()) {
                    return Err(ModelDecodeError::Constant(format!(
                        "duplicate declaration of {:?}",
                        key.as_str()
                    )));
                }
            }
            Some(SourceSymbol::NonSourceRelation) | None => {}
        }
        Ok(())
    }

    fn parse_relation_interpretation(
        &mut self,
        statement: &TffStatement,
        reverse: &ReverseNameEnv,
    ) -> Result<(), ModelDecodeError> {
        if statement.role != "axiom" {
            return Err(ModelDecodeError::Syntax(format!(
                "source relation occurs in non-axiom statement {:?}",
                statement.name
            )));
        }
        let literals = parse_ground_conjunction(&statement.formula)?;
        if literals.is_empty() {
            return Err(ModelDecodeError::Syntax(format!(
                "empty source-relation interpretation {:?}",
                statement.name
            )));
        }
        let mut grouped: BTreeMap<RelationKey, BTreeMap<Vec<String>, bool>> = BTreeMap::new();
        for literal in literals {
            let Some(SourceSymbol::Relation(key)) = reverse.symbol(&literal.predicate) else {
                return Err(ModelDecodeError::Syntax(format!(
                    "source-relation statement {:?} mixes in predicate {:?}",
                    statement.name, literal.predicate
                )));
            };
            let table = grouped.entry(key.clone()).or_default();
            if table.insert(literal.arguments, literal.positive).is_some() {
                return Err(relation_error(key, "duplicate or conflicting ground tuple"));
            }
        }
        for (key, table) in grouped {
            let relation = self
                .relations
                .get_mut(&key)
                .expect("source relation was initialized");
            if relation.interpretation.replace(table).is_some() {
                return Err(relation_error(&key, "duplicate interpretation block"));
            }
        }
        Ok(())
    }

    fn parse_constant_interpretation(
        &mut self,
        statement: &TffStatement,
        reverse: &ReverseNameEnv,
    ) -> Result<(), ModelDecodeError> {
        if statement.role != "axiom" {
            return Err(ModelDecodeError::Constant(format!(
                "task constant occurs in non-axiom statement {:?}",
                statement.name
            )));
        }
        let Some((left, right)) = split_top_level_once(strip_outer(&statement.formula)?, '=')?
        else {
            return Err(ModelDecodeError::Constant(format!(
                "unsupported interpretation in statement {:?}",
                statement.name
            )));
        };
        let left = parse_atom(strip_outer(left)?)?;
        let right = parse_atom(strip_outer(right)?)?;
        let (key, value) = match (reverse.symbol(&left), reverse.symbol(&right)) {
            (Some(SourceSymbol::Constant(key)), None) => (key.clone(), right),
            (None, Some(SourceSymbol::Constant(key))) => (key.clone(), left),
            _ => {
                return Err(ModelDecodeError::Constant(format!(
                    "statement {:?} is not one task-constant/domain-element equality",
                    statement.name
                )));
            }
        };
        if self.constant_values.insert(key.clone(), value).is_some() {
            return Err(ModelDecodeError::Constant(format!(
                "duplicate or conflicting interpretation of {:?}",
                key.as_str()
            )));
        }
        Ok(())
    }

    fn finish(
        self,
        task: &SynthesisTask,
        reverse: ReverseNameEnv,
    ) -> Result<DecodedInstance, ModelDecodeError> {
        let domain = self
            .domain
            .ok_or_else(|| ModelDecodeError::Domain("missing finite-domain axiom".to_string()))?;
        if domain.is_empty() {
            return Err(ModelDecodeError::Domain(
                "Vampire domain must be nonempty".to_string(),
            ));
        }
        for element in &domain {
            if self.duplicate_declarations.contains(element) {
                return Err(ModelDecodeError::Domain(format!(
                    "domain element {element:?} has duplicate declarations"
                )));
            }
            if self.declarations.get(element).map(String::as_str) != Some("$i") {
                return Err(ModelDecodeError::Domain(format!(
                    "domain element {element:?} lacks one $i declaration"
                )));
            }
        }

        let mut element_constants = BTreeMap::new();
        for (constant, element) in &self.constant_values {
            if !self.seen_constant_declarations.contains(constant) {
                return Err(ModelDecodeError::Constant(format!(
                    "interpreted constant {:?} has no declaration",
                    constant.as_str()
                )));
            }
            if !domain.contains(element) {
                return Err(ModelDecodeError::Constant(format!(
                    "constant {:?} denotes undeclared element {element:?}",
                    constant.as_str()
                )));
            }
            if let Some(previous) = element_constants.insert(element.clone(), constant.clone()) {
                return Err(ModelDecodeError::Constant(format!(
                    "distinct constants {:?} and {:?} denote {element:?}",
                    previous.as_str(),
                    constant.as_str()
                )));
            }
        }
        for constant in &self.seen_constant_declarations {
            if !self.constant_values.contains_key(constant) {
                return Err(ModelDecodeError::Constant(format!(
                    "declared constant {:?} has no interpretation",
                    constant.as_str()
                )));
            }
        }

        let mut raw_true = BTreeMap::new();
        let mut active_elements = BTreeSet::new();
        for schema_relation in task.solver_relations() {
            let key = schema_relation.key();
            let solver_name = reverse.source_relation_name(key);
            let relation = self
                .relations
                .get(key)
                .expect("schema relation initialized");
            let declared = relation.declared_arity.ok_or_else(|| {
                relation_error(key, format!("missing declaration for {solver_name:?}"))
            })?;
            if declared != schema_relation.arity() {
                return Err(relation_error(
                    key,
                    format!(
                        "declared arity {declared} differs from schema arity {}",
                        schema_relation.arity()
                    ),
                ));
            }
            let table = relation.interpretation.as_ref().ok_or_else(|| {
                relation_error(key, format!("missing interpretation for {solver_name:?}"))
            })?;
            validate_complete_table(key, schema_relation.arity(), &domain, table)?;
            let tuples = table
                .iter()
                .filter_map(|(tuple, truth)| truth.then_some(tuple.clone()))
                .collect::<BTreeSet<_>>();
            for tuple in &tuples {
                active_elements.extend(tuple.iter().cloned());
            }
            raw_true.insert(key.clone(), tuples);
        }

        let fresh = active_elements
            .iter()
            .filter(|element| !element_constants.contains_key(*element))
            .enumerate()
            .map(|(index, element)| (element.clone(), index as u64))
            .collect::<BTreeMap<_, _>>();
        let relations = task
            .solver_relations()
            .iter()
            .map(|schema_relation| {
                let tuples = raw_true
                    .remove(schema_relation.key())
                    .expect("all schema relations were collected")
                    .into_iter()
                    .map(|tuple| {
                        tuple
                            .into_iter()
                            .map(|element| {
                                if let Some(constant) = element_constants.get(&element) {
                                    InstanceValue::Constant(constant.clone())
                                } else {
                                    InstanceValue::Fresh(
                                        *fresh
                                            .get(&element)
                                            .expect("every active element is named"),
                                    )
                                }
                            })
                            .collect()
                    })
                    .collect();
                (
                    schema_relation.key().clone(),
                    DecodedRelation {
                        arity: schema_relation.arity(),
                        true_tuples: tuples,
                    },
                )
            })
            .collect();
        Ok(DecodedInstance {
            task: task.identity().clone(),
            relations,
        })
    }

    fn finish_exact(
        self,
        relation_arities: &BTreeMap<RelationKey, u64>,
        required_constants: &BTreeSet<ConstantKey>,
        reverse: ReverseNameEnv,
        query: Option<&str>,
    ) -> Result<DecodedFiniteModel, ModelDecodeError> {
        let domain = self
            .domain
            .ok_or_else(|| ModelDecodeError::Domain("missing finite-domain axiom".to_string()))?;
        if domain.is_empty() {
            return Err(ModelDecodeError::Domain(
                "Vampire domain must be nonempty".to_string(),
            ));
        }
        for element in &domain {
            if self.duplicate_declarations.contains(element) {
                return Err(ModelDecodeError::Domain(format!(
                    "domain element {element:?} has duplicate declarations"
                )));
            }
            if self.declarations.get(element).map(String::as_str) != Some("$i") {
                return Err(ModelDecodeError::Domain(format!(
                    "domain element {element:?} lacks one $i declaration"
                )));
            }
        }

        let mut element_constants = BTreeMap::new();
        for (constant, element) in &self.constant_values {
            if !self.seen_constant_declarations.contains(constant) {
                return Err(ModelDecodeError::Constant(format!(
                    "interpreted constant {:?} has no declaration",
                    constant.as_str()
                )));
            }
            if !domain.contains(element) {
                return Err(ModelDecodeError::Constant(format!(
                    "constant {:?} denotes undeclared element {element:?}",
                    constant.as_str()
                )));
            }
            if let Some(previous) = element_constants.insert(element.clone(), constant.clone()) {
                return Err(ModelDecodeError::Constant(format!(
                    "distinct constants {:?} and {:?} denote {element:?}",
                    previous.as_str(),
                    constant.as_str()
                )));
            }
        }
        for constant in &self.seen_constant_declarations {
            if !self.constant_values.contains_key(constant) {
                return Err(ModelDecodeError::Constant(format!(
                    "declared constant {:?} has no interpretation",
                    constant.as_str()
                )));
            }
        }
        for constant in required_constants {
            if !self.seen_constant_declarations.contains(constant) {
                return Err(ModelDecodeError::Constant(format!(
                    "required obligation constant {:?} has no declaration",
                    constant.as_str()
                )));
            }
            if !self.constant_values.contains_key(constant) {
                return Err(ModelDecodeError::Constant(format!(
                    "required obligation constant {:?} has no interpretation",
                    constant.as_str()
                )));
            }
        }

        let mut relations = BTreeMap::new();
        for (key, arity) in relation_arities {
            let solver_name = reverse.source_relation_name(key);
            let relation = self
                .relations
                .get(key)
                .expect("exact-schema relation initialized");
            let Some(declared) = relation.declared_arity else {
                // The solver prints only the symbols that survived into the
                // problem it built a model of. A relation the query never
                // mentions is unconstrained by it — every expansion of the
                // model to that symbol is again a model of the same
                // formulas — so the empty table is a genuine
                // interpretation and the decode continues with it. The case
                // that arises is a nullary relation: the active-domain
                // support quantifies over each relation's tuples, and a
                // nullary relation has none, so nothing in the rendered
                // problem has to mention it.
                //
                // A symbol the query does mention and the model omits is
                // still an error: there the interpretation could have been
                // constrained, and guessing it would be guessing about the
                // obligation. Without the query text this path cannot tell
                // the two apart, so it stays strict.
                if query.is_some_and(|query| !query_mentions(query, solver_name)) {
                    relations.insert(
                        key.clone(),
                        DecodedFiniteRelation {
                            arity: *arity,
                            true_tuples: BTreeSet::new(),
                        },
                    );
                    continue;
                }
                return Err(relation_error(
                    key,
                    format!("missing declaration for {solver_name:?}"),
                ));
            };
            if declared != *arity {
                return Err(relation_error(
                    key,
                    format!("declared arity {declared} differs from schema arity {arity}"),
                ));
            }
            let table = relation.interpretation.as_ref().ok_or_else(|| {
                relation_error(key, format!("missing interpretation for {solver_name:?}"))
            })?;
            validate_complete_table(key, *arity, &domain, table)?;
            relations.insert(
                key.clone(),
                DecodedFiniteRelation {
                    arity: *arity,
                    true_tuples: table
                        .iter()
                        .filter_map(|(tuple, truth)| truth.then_some(tuple.clone()))
                        .collect(),
                },
            );
        }
        Ok(DecodedFiniteModel {
            carrier: domain,
            constant_values: self.constant_values,
            relations,
        })
    }
}

fn relation_error(key: &RelationKey, detail: impl Into<String>) -> ModelDecodeError {
    ModelDecodeError::Relation {
        relation: key.as_str().to_string(),
        detail: detail.into(),
    }
}

fn validate_complete_table(
    key: &RelationKey,
    arity: u64,
    domain: &BTreeSet<String>,
    table: &BTreeMap<Vec<String>, bool>,
) -> Result<(), ModelDecodeError> {
    let arity = usize::try_from(arity)
        .map_err(|_| relation_error(key, "arity does not fit this platform"))?;
    let expected = (0..arity).try_fold(1_usize, |size, _| {
        size.checked_mul(domain.len())
            .ok_or_else(|| relation_error(key, "finite table size overflows usize"))
    })?;
    for tuple in table.keys() {
        if tuple.len() != arity {
            return Err(relation_error(
                key,
                format!("tuple has arity {} instead of {arity}", tuple.len()),
            ));
        }
        if let Some(element) = tuple.iter().find(|element| !domain.contains(*element)) {
            return Err(relation_error(
                key,
                format!("tuple uses undeclared domain element {element:?}"),
            ));
        }
    }
    if table.len() != expected {
        return Err(relation_error(
            key,
            format!(
                "interpretation has {} ground cases; complete table requires {expected}",
                table.len()
            ),
        ));
    }
    Ok(())
}

// ------------------------------------------------------------
// Supported Model Formulas
// ------------------------------------------------------------

fn relation_type_arity(text: &str) -> Option<u64> {
    if text == "$o" {
        return Some(0);
    }
    let arguments = text.strip_suffix(">$o")?;
    let arguments = arguments
        .strip_prefix('(')
        .and_then(|inner| inner.strip_suffix(')'))
        .unwrap_or(arguments);
    let parts = arguments.split('*').collect::<Vec<_>>();
    (!parts.is_empty() && parts.iter().all(|part| *part == "$i")).then_some(parts.len() as u64)
}

fn compact(text: &str) -> String {
    text.chars()
        .filter(|character| !character.is_whitespace())
        .collect()
}

fn parse_finite_domain(formula: &str) -> Result<BTreeSet<String>, ModelDecodeError> {
    let formula = formula.trim();
    let Some(rest) = formula.strip_prefix('!') else {
        return Err(ModelDecodeError::Domain(
            "finite-domain axiom is not universally quantified".to_string(),
        ));
    };
    let rest = rest.trim_start();
    if !rest.starts_with('[') {
        return Err(ModelDecodeError::Domain(
            "finite-domain quantifier has no variable list".to_string(),
        ));
    }
    let close = matching_delimiter(rest, 0, '[', ']')?;
    let binding = &rest[1..close];
    let Some((variable, sort)) = split_top_level_once(binding, ':')? else {
        return Err(ModelDecodeError::Domain(
            "finite-domain variable has no sort".to_string(),
        ));
    };
    let variable = parse_atom(variable)?;
    if compact(sort) != "$i" {
        return Err(ModelDecodeError::Domain(
            "finite-domain variable does not have sort $i".to_string(),
        ));
    }
    let after = rest[close + 1..].trim_start();
    let Some(body) = after.strip_prefix(':') else {
        return Err(ModelDecodeError::Domain(
            "finite-domain quantifier has no body".to_string(),
        ));
    };
    let body = strip_outer(body)?;
    let cases = split_top_level(body, '|')?;
    let mut domain = BTreeSet::new();
    for case in cases {
        let Some((left, right)) = split_top_level_once(strip_outer(case)?, '=')? else {
            return Err(ModelDecodeError::Domain(
                "finite-domain case is not an equality".to_string(),
            ));
        };
        let left = parse_atom(strip_outer(left)?)?;
        let right = parse_atom(strip_outer(right)?)?;
        let element = if left == variable && right != variable {
            right
        } else if right == variable && left != variable {
            left
        } else {
            return Err(ModelDecodeError::Domain(
                "finite-domain equality does not bind its quantified variable".to_string(),
            ));
        };
        if !domain.insert(element.clone()) {
            return Err(ModelDecodeError::Domain(format!(
                "duplicate domain element {element:?}"
            )));
        }
    }
    Ok(domain)
}

struct GroundLiteral {
    positive: bool,
    predicate: String,
    arguments: Vec<String>,
}

fn parse_ground_conjunction(formula: &str) -> Result<Vec<GroundLiteral>, ModelDecodeError> {
    split_top_level(strip_outer(formula)?, '&')?
        .into_iter()
        .map(parse_ground_literal)
        .collect()
}

fn parse_ground_literal(text: &str) -> Result<GroundLiteral, ModelDecodeError> {
    let mut text = strip_outer(text)?.trim();
    let positive = if let Some(rest) = text.strip_prefix('~') {
        text = strip_outer(rest)?.trim();
        false
    } else {
        true
    };
    let (predicate, consumed) = parse_atom_prefix(text)?;
    let rest = text[consumed..].trim();
    let arguments = if rest.is_empty() {
        Vec::new()
    } else {
        if !rest.starts_with('(') {
            return Err(ModelDecodeError::Syntax(format!(
                "unexpected text after predicate {predicate:?}"
            )));
        }
        let close = matching_delimiter(rest, 0, '(', ')')?;
        if !rest[close + 1..].trim().is_empty() {
            return Err(ModelDecodeError::Syntax(format!(
                "unexpected suffix after predicate {predicate:?}"
            )));
        }
        let body = &rest[1..close];
        if body.trim().is_empty() {
            return Err(ModelDecodeError::Syntax(format!(
                "predicate {predicate:?} uses empty parentheses"
            )));
        }
        split_top_level(body, ',')?
            .into_iter()
            .map(|argument| parse_atom(strip_outer(argument)?))
            .collect::<Result<Vec<_>, _>>()?
    };
    Ok(GroundLiteral {
        positive,
        predicate,
        arguments,
    })
}

// ------------------------------------------------------------
// Small Balanced-Syntax Helpers
// ------------------------------------------------------------

fn split_top_level(text: &str, delimiter: char) -> Result<Vec<&str>, ModelDecodeError> {
    let mut fields = Vec::new();
    let mut start = 0;
    let mut parens = 0_u64;
    let mut brackets = 0_u64;
    let mut quoted = false;
    let mut escaped = false;
    for (index, character) in text.char_indices() {
        if quoted {
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '\'' {
                quoted = false;
            }
            continue;
        }
        match character {
            '\'' => quoted = true,
            '(' => parens += 1,
            ')' => {
                parens = parens
                    .checked_sub(1)
                    .ok_or_else(|| ModelDecodeError::Syntax("unbalanced ')'".to_string()))?;
            }
            '[' => brackets += 1,
            ']' => {
                brackets = brackets
                    .checked_sub(1)
                    .ok_or_else(|| ModelDecodeError::Syntax("unbalanced ']'".to_string()))?;
            }
            _ if character == delimiter && parens == 0 && brackets == 0 => {
                fields.push(text[start..index].trim());
                start = index + character.len_utf8();
            }
            _ => {}
        }
    }
    if quoted || parens != 0 || brackets != 0 {
        return Err(ModelDecodeError::Syntax(
            "unterminated quote or unbalanced delimiter".to_string(),
        ));
    }
    fields.push(text[start..].trim());
    Ok(fields)
}

fn split_top_level_once(
    text: &str,
    delimiter: char,
) -> Result<Option<(&str, &str)>, ModelDecodeError> {
    let fields = split_top_level(text, delimiter)?;
    match fields.as_slice() {
        [_] => Ok(None),
        [left, right] => Ok(Some((left, right))),
        _ => Err(ModelDecodeError::Syntax(format!(
            "more than one top-level {delimiter:?}"
        ))),
    }
}

fn matching_delimiter(
    text: &str,
    open: usize,
    opening: char,
    closing: char,
) -> Result<usize, ModelDecodeError> {
    if !text[open..].starts_with(opening) {
        return Err(ModelDecodeError::Syntax(format!(
            "expected {opening:?} delimiter"
        )));
    }
    let mut depth = 0_u64;
    let mut quoted = false;
    let mut escaped = false;
    for (offset, character) in text[open..].char_indices() {
        if quoted {
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '\'' {
                quoted = false;
            }
            continue;
        }
        if character == '\'' {
            quoted = true;
        } else if character == opening {
            depth += 1;
        } else if character == closing {
            depth -= 1;
            if depth == 0 {
                return Ok(open + offset);
            }
        }
    }
    Err(ModelDecodeError::Syntax(format!(
        "unterminated {opening:?} delimiter"
    )))
}

fn strip_outer(mut text: &str) -> Result<&str, ModelDecodeError> {
    text = text.trim();
    while text.starts_with('(') {
        let close = matching_delimiter(text, 0, '(', ')')?;
        if close + 1 != text.len() {
            break;
        }
        text = text[1..close].trim();
    }
    Ok(text)
}

fn parse_atom(text: &str) -> Result<String, ModelDecodeError> {
    let text = text.trim();
    let (atom, consumed) = parse_atom_prefix(text)?;
    if !text[consumed..].trim().is_empty() {
        return Err(ModelDecodeError::Syntax(format!(
            "expected one atomic symbol, found {:?}",
            preview(text)
        )));
    }
    Ok(atom)
}

fn parse_atom_prefix(text: &str) -> Result<(String, usize), ModelDecodeError> {
    let text = text.trim_start();
    if let Some(rest) = text.strip_prefix('\'') {
        let mut escaped = false;
        let mut value = String::new();
        for (offset, character) in rest.char_indices() {
            if escaped {
                value.push(character);
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '\'' {
                return Ok((value, offset + 2));
            } else {
                value.push(character);
            }
        }
        return Err(ModelDecodeError::Syntax(
            "unterminated quoted atom".to_string(),
        ));
    }
    let consumed = text
        .char_indices()
        .take_while(|(_, character)| {
            character.is_ascii_alphanumeric() || matches!(character, '_' | '$')
        })
        .last()
        .map_or(0, |(index, character)| index + character.len_utf8());
    if consumed == 0 {
        return Err(ModelDecodeError::Syntax(format!(
            "expected atomic symbol near {:?}",
            preview(text)
        )));
    }
    Ok((text[..consumed].to_string(), consumed))
}

fn formula_symbols(text: &str) -> Vec<String> {
    let mut symbols = Vec::new();
    let mut cursor = 0;
    while cursor < text.len() {
        let remainder = &text[cursor..];
        let first = remainder.chars().next().expect("cursor is in bounds");
        if (first == '\'' || first.is_ascii_alphanumeric() || matches!(first, '_' | '$'))
            && let Ok((symbol, consumed)) = parse_atom_prefix(remainder)
        {
            symbols.push(symbol);
            cursor += consumed;
            continue;
        }
        cursor += first.len_utf8();
    }
    symbols
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encoding::TaskNameEnv;
    use crate::houdini::CertificationInstance;

    fn task_with_nullary_and_constant() -> SynthesisTask {
        SynthesisTask::from_json(
            r#"{
              "format_version":3,"semantic_version":1,"encoding_version":1,
              "identity":{"canonical_id":"ModelDecode","module":"Whiel.Test.ModelDecode","namespace":"Whiel.Test.ModelDecode","source_sha256":"0000000000000000000000000000000000000000000000000000000000000000"},
              "schema":{"expression":"Whiel.Test.ModelDecode.programSchema","display":"schema"},
              "original":{"pre":{"expression":"Whiel.Test.ModelDecode.inputPre","display":"true"},"command":{"expression":"Whiel.Test.ModelDecode.inputCmd","display":"SKIP"},"post":{"expression":"Whiel.Test.ModelDecode.inputPost","display":"true"}},
              "preprocessed":{"pre":{"expression":"Whiel.Test.ModelDecode.inputPreproc.loopPre","display":"true"},"command":{"expression":"Whiel.Test.ModelDecode.inputPreproc.loopCmd","display":"SKIP"},"post":{"expression":"Whiel.Test.ModelDecode.inputPreproc.loopPost","display":"true"}},
              "preprocessing_evidence":{"expression":"Whiel.Test.ModelDecode.inputPreproc"},
              "solver":{"schema_relations":[{"key":"rel:N:0","arity":0},{"key":"rel:R:0","arity":1}],"task_constants":["num:7"],
                "preprocessed_pre":{"source_id":"task.preprocessed_pre","expression":"Whiel.Test.ModelDecode.inputPreproc.loopPre","no_bound_expression":"Whiel.Test.ModelDecode.inputPreproc.loopPre_noBound","constants":["num:7"],"relations":["rel:N:0","rel:R:0"]},
                "preprocessed_post":{"source_id":"task.preprocessed_post","expression":"Whiel.Test.ModelDecode.inputPreproc.loopPost","no_bound_expression":"Whiel.Test.ModelDecode.inputPreproc.loopPost_noBound","constants":[],"relations":[]},
                "loop_guard":{"source_id":"task.loop_guard","constants":[],"relations":[]},
                "negated_loop_guard":{"source_id":"task.negated_loop_guard","constants":[],"relations":[]}}
            }"#,
        )
        .unwrap()
    }

    fn task_for_certification_conversion() -> SynthesisTask {
        SynthesisTask::from_json(
            r#"{
              "format_version":3,"semantic_version":1,"encoding_version":1,
              "identity":{"canonical_id":"ModelCertification","module":"Whiel.Test.ModelCertification","namespace":"Whiel.Test.ModelCertification","source_sha256":"0000000000000000000000000000000000000000000000000000000000000000"},
              "schema":{"expression":"Whiel.Test.ModelCertification.programSchema","display":"schema"},
              "original":{"pre":{"expression":"Whiel.Test.ModelCertification.inputPre","display":"true"},"command":{"expression":"Whiel.Test.ModelCertification.inputCmd","display":"SKIP"},"post":{"expression":"Whiel.Test.ModelCertification.inputPost","display":"true"}},
              "preprocessed":{"pre":{"expression":"Whiel.Test.ModelCertification.inputPreproc.loopPre","display":"true"},"command":{"expression":"Whiel.Test.ModelCertification.inputPreproc.loopCmd","display":"SKIP"},"post":{"expression":"Whiel.Test.ModelCertification.inputPreproc.loopPost","display":"true"}},
              "preprocessing_evidence":{"expression":"Whiel.Test.ModelCertification.inputPreproc"},
              "solver":{"schema_relations":[{"key":"rel:N:0","arity":0},{"key":"rel:R:0","arity":5},{"key":"rel:E:0","arity":1}],"task_constants":["num:184467440737095516160000","bool:0","str:__whiel_fmb_fresh_0","str:__whiel_fmb_fresh_1"],
                "preprocessed_pre":{"source_id":"task.preprocessed_pre","expression":"Whiel.Test.ModelCertification.inputPreproc.loopPre","no_bound_expression":"Whiel.Test.ModelCertification.inputPreproc.loopPre_noBound","constants":["num:184467440737095516160000","bool:0","str:__whiel_fmb_fresh_0"],"relations":["rel:N:0","rel:R:0","rel:E:0"]},
                "preprocessed_post":{"source_id":"task.preprocessed_post","expression":"Whiel.Test.ModelCertification.inputPreproc.loopPost","no_bound_expression":"Whiel.Test.ModelCertification.inputPreproc.loopPost_noBound","constants":[],"relations":[]},
                "loop_guard":{"source_id":"task.loop_guard","constants":[],"relations":[]},
                "negated_loop_guard":{"source_id":"task.negated_loop_guard","constants":[],"relations":[]}}
            }"#,
        )
        .unwrap()
    }

    fn solver_name(names: &TaskNameEnv, kind: NameMappingKind, key: &str) -> String {
        names
            .all_mappings()
            .into_iter()
            .find(|mapping| mapping.kind == kind && mapping.key == key)
            .unwrap()
            .tptp_name
    }

    #[test]
    fn empty_constructor_requires_exact_nullary_assignment() {
        let task = task_with_nullary_and_constant();
        let nullary = task.solver_relations()[0].key().clone();
        let unary = task.solver_relations()[1].key().clone();

        let instance =
            DecodedInstance::empty_active_domain(&task, [(nullary.clone(), true)]).unwrap();
        assert_eq!(
            instance.relation(&nullary).unwrap().nullary_value(),
            Some(true)
        );
        assert!(instance.relation(&unary).unwrap().true_tuples().is_empty());
        assert!(matches!(
            DecodedInstance::empty_active_domain(&task, []),
            Err(EmptyInstanceError::MissingAssignment(_))
        ));
        assert!(matches!(
            DecodedInstance::empty_active_domain(&task, [(unary, false)]),
            Err(EmptyInstanceError::NonNullaryAssignment { .. })
        ));
    }

    /// The solver's model printer prints only the symbols that survived
    /// into the problem it modelled. A nullary scope relation the query
    /// never mentions is therefore absent from the model, and it is also
    /// unconstrained by that query, so the decode interprets it by the
    /// empty table and goes on. The same symbol missing from a model whose
    /// query does mention it stays an error, and so does a missing
    /// symbol when the query is not available to tell the two apart.
    #[test]
    fn a_relation_the_query_never_mentions_is_defaulted_rather_than_refused() {
        let task = task_with_nullary_and_constant();
        let names = TaskNameEnv::from_task(&task).unwrap();
        let nullary = task.solver_relations()[0].key().clone();
        let unary = task.solver_relations()[1].key().clone();
        let nullary_name = solver_name(&names, NameMappingKind::Relation, nullary.as_str());
        let unary_name = solver_name(&names, NameMappingKind::Relation, unary.as_str());
        let arities = [(nullary.clone(), 0), (unary.clone(), 1)];

        // One element, the unary relation declared and interpreted, the
        // nullary flag absent — exactly the shape the finite-model builder
        // prints for a query that never mentions the flag.
        let stdout = complete_output(&format!(
            "tff('declare_$i1',type,'fmb_$i_1':$i).\n\
             tff('finite_domain_$i',axiom,! [X:$i] : (X = 'fmb_$i_1')).\n\
             tff(declare_{unary_name},type,{unary_name}:$i>$o).\n\
             tff(predicate_{unary_name},axiom,~{unary_name}('fmb_$i_1')).\n"
        ));
        let mentions_unary_only = format!("fof(goal, conjecture, {unary_name}(a)).");
        let decoded = decode_vampire_model_for_relations(
            &names,
            &arities,
            &[],
            &stdout,
            Some(&mentions_unary_only),
        )
        .expect("a flag the query never mentions is unconstrained by it");
        let flag = decoded
            .relations
            .get(&nullary)
            .expect("the defaulted flag is still a total interpretation");
        assert_eq!(flag.arity, 0);
        assert!(
            flag.true_tuples.is_empty(),
            "an unconstrained flag defaults to false"
        );

        // The same model against a query that does mention the flag: the
        // omission is no longer explained, and the decode refuses.
        let mentions_both = format!("fof(goal, conjecture, {unary_name}(a) | {nullary_name}).");
        assert!(
            decode_vampire_model_for_relations(
                &names,
                &arities,
                &[],
                &stdout,
                Some(&mentions_both)
            )
            .is_err()
        );

        // And with no query to consult, the decode stays strict.
        assert!(decode_vampire_model_for_relations(&names, &arities, &[], &stdout, None).is_err());
    }

    #[test]
    fn certification_conversion_is_exact_complete_and_deterministic() {
        let task = task_for_certification_conversion();
        let constant = |key: &str| {
            task.solver_constants()
                .iter()
                .find(|constant| constant.as_str() == key)
                .unwrap()
                .clone()
        };
        let relation = |key: &str| {
            task.solver_relations()
                .iter()
                .find(|relation| relation.key().as_str() == key)
                .unwrap()
                .key()
                .clone()
        };
        let input = DecodedInstance {
            task: task.identity().clone(),
            relations: BTreeMap::from([
                (
                    relation("rel:N:0"),
                    DecodedRelation {
                        arity: 0,
                        true_tuples: BTreeSet::from([Vec::new()]),
                    },
                ),
                (
                    relation("rel:R:0"),
                    DecodedRelation {
                        arity: 5,
                        true_tuples: BTreeSet::from([vec![
                            InstanceValue::Constant(constant("num:184467440737095516160000")),
                            InstanceValue::Constant(constant("bool:0")),
                            InstanceValue::Constant(constant("str:__whiel_fmb_fresh_0")),
                            InstanceValue::Fresh(0),
                            InstanceValue::Fresh(1),
                        ]]),
                    },
                ),
                (
                    relation("rel:E:0"),
                    DecodedRelation {
                        arity: 1,
                        true_tuples: BTreeSet::new(),
                    },
                ),
            ]),
        };

        let first = CertificationInstance::from_decoded(&task, &input).unwrap();
        let second = CertificationInstance::from_decoded(&task, &input).unwrap();
        assert!(
            CertificationInstance::from_decoded(&task_with_nullary_and_constant(), &input).is_err()
        );
        assert_eq!(first.as_json(), second.as_json());
        assert_eq!(first.as_json()["N"], serde_json::json!([[]]));
        assert_eq!(first.as_json()["E"], serde_json::json!([]));
        let row = first.as_json()["R"][0].as_array().unwrap();
        assert_eq!(
            row[0].as_number().unwrap().to_string(),
            "184467440737095516160000"
        );
        assert_eq!(row[1], serde_json::json!(false));
        assert_eq!(row[2], serde_json::json!("__whiel_fmb_fresh_0"));
        assert_eq!(row[3], serde_json::json!("__whiel_fmb_fresh_0_"));
        assert_eq!(row[4], serde_json::json!("__whiel_fmb_fresh_1_"));
    }

    fn complete_output(model: &str) -> String {
        format!(
            "% Running Vampire\n% SZS status CounterSatisfiable for p\n% SZS output start FiniteModel for p\n{model}% SZS output end FiniteModel for p\n% done\n"
        )
    }

    #[test]
    fn decodes_nullary_empty_and_constant_backed_values() {
        let task = task_with_nullary_and_constant();
        let names = TaskNameEnv::from_task(&task).unwrap();
        let n = solver_name(&names, NameMappingKind::Relation, "rel:N:0");
        let r = solver_name(&names, NameMappingKind::Relation, "rel:R:0");
        let c = solver_name(&names, NameMappingKind::Constant, "num:7");
        let stdout = complete_output(&format!(
            "tff('declare_$i1',type,'fmb_$i_1':$i).\n\
             tff('declare_$i2',type,'fmb_$i_2':$i).\n\
             tff('finite_domain_$i',axiom,! [X:$i] : (X = 'fmb_$i_1' | X = 'fmb_$i_2')).\n\
             tff(declare_{c},type,{c}:$i).\n\
             tff(function_{c},axiom,{c} = 'fmb_$i_2').\n\
             tff(declare_{n},type,{n}:$o).\n\
             tff(predicate_{n},axiom,~{n}).\n\
             tff(declare_{r},type,{r}:$i>$o).\n\
             tff(predicate_{r},axiom,{r}('fmb_$i_1') & {r}('fmb_$i_2')).\n"
        ));

        let instance = decode_vampire_model(&task, &names, &stdout).unwrap();
        assert_eq!(instance.task_identity(), task.identity());
        assert_eq!(
            instance
                .relation(task.solver_relations()[0].key())
                .unwrap()
                .nullary_value(),
            Some(false)
        );
        let r = instance.relation(task.solver_relations()[1].key()).unwrap();
        assert_eq!(
            r.true_tuples(),
            &BTreeSet::from([
                vec![InstanceValue::Fresh(0)],
                vec![InstanceValue::Constant(task.solver_constants()[0].clone())],
            ])
        );
    }

    #[test]
    fn all_false_relation_is_present_as_an_empty_table() {
        let task = task_with_nullary_and_constant();
        let names = TaskNameEnv::from_task(&task).unwrap();
        let n = solver_name(&names, NameMappingKind::Relation, "rel:N:0");
        let r = solver_name(&names, NameMappingKind::Relation, "rel:R:0");
        let stdout = complete_output(&format!(
            "tff('declare_$i1',type,'fmb_$i_1':$i).\n\
             tff('finite_domain_$i',axiom,! [X:$i] : X = 'fmb_$i_1').\n\
             tff(declare_{n},type,{n}:$o).\n\
             tff(predicate_{n},axiom,{n}).\n\
             tff(declare_{r},type,{r}:$i>$o).\n\
             tff(predicate_{r},axiom,~{r}('fmb_$i_1')).\n"
        ));

        let instance = decode_vampire_model(&task, &names, &stdout).unwrap();
        assert!(
            instance
                .relation(task.solver_relations()[1].key())
                .unwrap()
                .true_tuples()
                .is_empty()
        );
    }

    #[test]
    fn rejects_incomplete_envelope_and_incomplete_relation_table() {
        let task = task_with_nullary_and_constant();
        let names = TaskNameEnv::from_task(&task).unwrap();
        let n = solver_name(&names, NameMappingKind::Relation, "rel:N:0");
        let r = solver_name(&names, NameMappingKind::Relation, "rel:R:0");
        let model = format!(
            "tff('declare_$i1',type,'fmb_$i_1':$i).\n\
             tff('declare_$i2',type,'fmb_$i_2':$i).\n\
             tff('finite_domain_$i',axiom,! [X:$i] : (X = 'fmb_$i_1' | X = 'fmb_$i_2')).\n\
             tff(declare_{n},type,{n}:$o).\n\
             tff(predicate_{n},axiom,{n}).\n\
             tff(declare_{r},type,{r}:$i>$o).\n\
             tff(predicate_{r},axiom,{r}('fmb_$i_1')).\n"
        );
        let truncated = format!(
            "% SZS status CounterSatisfiable for p\n% SZS output start FiniteModel for p\n{model}"
        );
        assert!(matches!(
            decode_vampire_model(&task, &names, &truncated),
            Err(ModelDecodeError::Envelope(_))
        ));
        assert!(matches!(
            decode_vampire_model(&task, &names, &complete_output(&model)),
            Err(ModelDecodeError::Relation { .. })
        ));
    }

    #[test]
    fn rejects_wrong_arity_and_undeclared_tuple_values() {
        let task = task_with_nullary_and_constant();
        let names = TaskNameEnv::from_task(&task).unwrap();
        let n = solver_name(&names, NameMappingKind::Relation, "rel:N:0");
        let r = solver_name(&names, NameMappingKind::Relation, "rel:R:0");
        let wrong_arity = complete_output(&format!(
            "tff('declare_$i1',type,'fmb_$i_1':$i).\n\
             tff('finite_domain_$i',axiom,! [X:$i] : X = 'fmb_$i_1').\n\
             tff(declare_{n},type,{n}:$o).\n\
             tff(predicate_{n},axiom,{n}).\n\
             tff(declare_{r},type,{r}:($i*$i)>$o).\n\
             tff(predicate_{r},axiom,{r}('fmb_$i_1','fmb_$i_1')).\n"
        ));
        assert!(matches!(
            decode_vampire_model(&task, &names, &wrong_arity),
            Err(ModelDecodeError::Relation { .. })
        ));

        let undeclared = complete_output(&format!(
            "tff('declare_$i1',type,'fmb_$i_1':$i).\n\
             tff('finite_domain_$i',axiom,! [X:$i] : X = 'fmb_$i_1').\n\
             tff(declare_{n},type,{n}:$o).\n\
             tff(predicate_{n},axiom,{n}).\n\
             tff(declare_{r},type,{r}:$i>$o).\n\
             tff(predicate_{r},axiom,{r}(ghost)).\n"
        ));
        assert!(matches!(
            decode_vampire_model(&task, &names, &undeclared),
            Err(ModelDecodeError::Relation { .. })
        ));
    }

    #[test]
    fn rejects_duplicate_or_conflicting_source_tuples() {
        let task = task_with_nullary_and_constant();
        let names = TaskNameEnv::from_task(&task).unwrap();
        let n = solver_name(&names, NameMappingKind::Relation, "rel:N:0");
        let r = solver_name(&names, NameMappingKind::Relation, "rel:R:0");
        let stdout = complete_output(&format!(
            "tff('declare_$i1',type,'fmb_$i_1':$i).\n\
             tff('finite_domain_$i',axiom,! [X:$i] : X = 'fmb_$i_1').\n\
             tff(declare_{n},type,{n}:$o).\n\
             tff(predicate_{n},axiom,{n}).\n\
             tff(declare_{r},type,{r}:$i>$o).\n\
             tff(predicate_{r},axiom,{r}('fmb_$i_1') & ~{r}('fmb_$i_1')).\n"
        ));
        assert!(matches!(
            decode_vampire_model(&task, &names, &stdout),
            Err(ModelDecodeError::Relation { .. })
        ));
    }
}
