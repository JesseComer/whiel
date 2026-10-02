//! Dependency-sliced local prenex (legacy transformation 5).
//!
//! Vampire's emitter introduces every Skolem witness of a global step at
//! once, whether or not the proof below it ever mentions them:
//!
//! ```text
//!   -- step39 skolemisation
//!   exists_prenex at step28
//!   let ⟨«_sK9»,«_sK10»,…,«_sK28»,step39'⟩ := step28
//!   have step39 : <the whole prenexed formula> := by symm_match using step39'
//! ```
//!
//! The clauses actually projected out of `step39` (Pass 7.9a's targeted
//! clause projection has already rewritten them to
//! `vampire_project_ordered using step39`) usually mention only a handful
//! of those witnesses, and only the ones introduced by the formula's
//! *first* conjunct. When that is so, the block is replaced by a slice
//! that prenexes that conjunct alone:
//!
//! ```text
//!   -- step39 dependency-sliced skolemisation from step28 (6/20 witnesses; …)
//!   have step39_slice : <first conjunct of the changed formula> := by
//!     vampire_project_ordered using step28
//!   exists_prenex at step39_slice
//!   let ⟨«_sK9»,…,«_sK14»,step39_slice'⟩ := step39_slice
//!   have step39_first : <first conjunct of the prenexed formula> := by
//!     symm_match using step39_slice'
//!   have step39 := And.intro step39_first step28
//! ```
//!
//! `step39` keeps a proposition of the same shape — the first conjunct
//! paired with the untouched pre-prenex `step28` — so every target below
//! projects out of it exactly as before, while the witnesses no target
//! mentions are never introduced.
//!
//! The contract is deliberately narrow, and every way of falling outside
//! it is a *recorded miss* that leaves the block byte-for-byte as Vampire
//! wrote it, so the compile-checked projected proof stays the fallback:
//! the live witnesses must all come from the first conjunct, be nullary
//! (never applied to an argument), and be a subset of the block's own
//! witness order; the prenexed step must descend by `change`/`have` lineage
//! from a step whose changed formula's first conjunct is a purely
//! existential `ι` block of exactly that many binders; no discarded witness
//! and no use of the global step itself may occur below the block. Only a
//! *damaged* generated slice — one this rewrite itself wrote and something
//! then edited — is a refusal rather than a miss.
//!
//! Idempotence is by a marker comment that binds every semantic field the
//! rewrite removed (the original witness order, both formulas, the source
//! step) under a digest, so re-running the rewrite on its own output
//! recovers the same receipt and changes no byte.
//!
//! This is a port of `whiel_synth.verification.tier1_bundle`'s
//! `rewrite_vamplean_prenex_slices` and its helpers, kept in differential
//! parity with it on the reference shapes.

use std::collections::{BTreeSet, HashMap};

use serde_json::{Value, json};

use crate::encoding::bytes_sha256;

use super::projection::{
    PROJECT_CALL_PREFIX, code_without_comments_or_strings, contains_delimited, is_ascii_word_char,
    parse_digits, parse_target_header, split_lines, tactic_body_end,
};

/// The version bound into every generated marker's digest. A change to
/// what the digest covers bumps this and the transformation's own version
/// together, so an older marker is recognized as altered rather than
/// silently re-accepted under new rules.
const MARKER_FORMAT_VERSION: u64 = 1;

/// One accepted or recovered slice.
#[derive(Clone, Debug)]
struct Slice {
    step_id: u64,
    /// The witnesses the slice still introduces, in the block's own order.
    retained: Vec<String>,
    /// How many the unsliced block introduced.
    original_count: usize,
}

/// The result of one dependency-sliced local prenex rewrite.
#[derive(Clone, Debug)]
pub struct PrenexSliceSummary {
    /// The rewritten (or, on a miss, unchanged) proof text.
    pub source: String,
    slices: Vec<Slice>,
    /// Exact skolemisation blocks left as Vampire wrote them, with the
    /// structural reason each fell outside the contract.
    missed: Vec<(u64, &'static str)>,
}

impl PrenexSliceSummary {
    pub fn block_count(&self) -> usize {
        self.slices.len()
    }

    pub fn retained_witness_count(&self) -> usize {
        self.slices.iter().map(|slice| slice.retained.len()).sum()
    }

    pub fn original_witness_count(&self) -> usize {
        self.slices.iter().map(|slice| slice.original_count).sum()
    }

    /// Witnesses the accepted slices never introduce.
    pub fn eliminated_witness_count(&self) -> usize {
        self.original_witness_count() - self.retained_witness_count()
    }

    /// The receipt's own counters for this rewrite.
    pub fn detail(&self) -> Value {
        json!({
            "slices": self.block_count(),
            "step_ids": self.slices.iter().map(|slice| slice.step_id).collect::<Vec<_>>(),
            "original_witnesses": self.original_witness_count(),
            "retained_witnesses": self.retained_witness_count(),
            "eliminated_witnesses": self.eliminated_witness_count(),
            "original_witness_counts": self
                .slices
                .iter()
                .map(|slice| slice.original_count)
                .collect::<Vec<_>>(),
            "retained_witness_names": self
                .slices
                .iter()
                .map(|slice| slice.retained.clone())
                .collect::<Vec<_>>(),
            "missed": self
                .missed
                .iter()
                .map(|(step_id, reason)| json!({ "step_id": step_id, "reason": reason }))
                .collect::<Vec<_>>(),
        })
    }
}

// ------------------------------------------------------------
// Line Shapes
// ------------------------------------------------------------

fn is_ascii_digits(text: &str) -> bool {
    !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit())
}

/// `«_sK<digits>»`, the pinned emitter's own Skolem spelling.
fn is_skolem_name(name: &str) -> bool {
    name.strip_prefix('«')
        .and_then(|rest| rest.strip_suffix('»'))
        .and_then(|inner| inner.strip_prefix("_sK"))
        .is_some_and(is_ascii_digits)
}

/// `  -- step<N> skolemisation`
fn match_skolem_marker(line: &str) -> Option<u64> {
    parse_digits(
        line.strip_prefix("  -- step")?
            .strip_suffix(" skolemisation")?,
    )
}

/// `  exists_prenex at step<N>`
fn match_skolem_prenex(line: &str) -> Option<u64> {
    parse_digits(line.strip_prefix("  exists_prenex at step")?)
}

/// `  have step<N> := <body>`
fn parse_definition(line: &str) -> Option<(u64, &str)> {
    let rest = line.strip_prefix("  have step")?;
    let boundary = rest.find(|character: char| !character.is_ascii_digit())?;
    let (digits, tail) = rest.split_at(boundary);
    let step_id = parse_digits(digits)?;
    let body = tail.strip_prefix(" := ")?;
    if body.is_empty() {
        return None;
    }
    Some((step_id, body))
}

/// `  change <formula> at step<N>`, with the legacy pattern's greedy
/// formula: the *last* ` at step<digits>` that ends the line wins.
fn parse_change(line: &str) -> Option<(String, u64)> {
    const AT: &str = " at step";
    let rest = line.strip_prefix("  change ")?;
    let mut found: Option<(usize, u64)> = None;
    let mut search_from = 0usize;
    while let Some(offset) = rest[search_from..].find(AT) {
        let at = search_from + offset;
        if let Some(step_id) = parse_digits(&rest[at + AT.len()..]) {
            found = Some((at, step_id));
        }
        search_from = at + 1;
    }
    let (at, step_id) = found?;
    if at == 0 {
        return None;
    }
    Some((rest[..at].to_string(), step_id))
}

/// Every `step<digits>` occurrence not inside a longer identifier.
fn step_references(text: &str) -> Vec<u64> {
    let mut references = Vec::new();
    let mut search_from = 0usize;
    while let Some(offset) = text[search_from..].find("step") {
        let start = search_from + offset;
        let after = start + "step".len();
        let digits = text[after..].bytes().take_while(u8::is_ascii_digit).count();
        let delimited = !text[..start]
            .chars()
            .next_back()
            .is_some_and(is_ascii_word_char);
        if delimited && digits > 0 {
            if let Some(step_id) = parse_digits(&text[after..after + digits]) {
                references.push(step_id);
            }
            search_from = after + digits;
        } else {
            search_from = after;
        }
    }
    references
}

/// Whether `step<id>` — with or without the emitter's prime — occurs in
/// `text` outside a longer identifier.
fn contains_step_use(text: &str, step_id: u64) -> bool {
    let needle = format!("step{step_id}");
    let mut search_from = 0usize;
    while let Some(offset) = text[search_from..].find(&needle) {
        let start = search_from + offset;
        let end = start + needle.len();
        let before = text[..start]
            .chars()
            .next_back()
            .is_some_and(is_ascii_word_char);
        let next = text[end..].chars().next();
        // The pattern's optional prime means a following `'` matches
        // either way: greedily, or by backtracking onto the `'` itself,
        // which is not a word character.
        if !before && (next == Some('\'') || !next.is_some_and(is_ascii_word_char)) {
            return true;
        }
        search_from = end;
    }
    false
}

/// Zero-based line numbers whose Lean line comment begins in code.
///
/// The pinned emitter writes its step markers as whole-line comments, so
/// a marker recognized inside a string literal or a block comment is not a
/// marker at all.
pub(super) fn line_comment_lines(source: &str) -> BTreeSet<usize> {
    let characters: Vec<char> = source.chars().collect();
    let mut lines = BTreeSet::new();
    let mut index = 0usize;
    let mut line = 0usize;
    let mut block_depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    while index < characters.len() {
        let character = characters[index];
        let next = characters.get(index + 1).copied();
        if block_depth > 0 {
            if character == '/' && next == Some('-') {
                block_depth += 1;
                index += 2;
            } else if character == '-' && next == Some('/') {
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
            lines.insert(line);
            match characters[index..]
                .iter()
                .position(|candidate| *candidate == '\n')
            {
                Some(offset) => {
                    line += 1;
                    index += offset + 1;
                }
                None => break,
            }
            continue;
        }
        if character == '/' && next == Some('-') {
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
    lines
}

// ------------------------------------------------------------
// Formula Shapes
// ------------------------------------------------------------

/// Remove only parenthesis pairs that enclose one complete formula.
fn strip_formula_parentheses(formula: &str) -> String {
    let mut value: String = formula.trim_matches(char::is_whitespace).to_string();
    while value.starts_with('(') && value.ends_with(')') {
        let characters: Vec<char> = value.chars().collect();
        let mut depth = 0i64;
        let mut closes_at_end = false;
        let mut unbalanced = false;
        for (index, character) in characters.iter().enumerate() {
            if *character == '(' {
                depth += 1;
            } else if *character == ')' {
                depth -= 1;
                if depth < 0 {
                    unbalanced = true;
                    break;
                }
                if depth == 0 {
                    closes_at_end = index == characters.len() - 1;
                    break;
                }
            }
        }
        if unbalanced {
            return value;
        }
        if !closes_at_end {
            break;
        }
        value = characters[1..characters.len() - 1]
            .iter()
            .collect::<String>()
            .trim_matches(char::is_whitespace)
            .to_string();
    }
    value
}

/// The first top-level conjunct, without parsing atoms. Empty when the
/// formula's parentheses do not balance.
fn first_formula_conjunct(formula: &str) -> String {
    let value = strip_formula_parentheses(formula);
    let characters: Vec<char> = value.chars().collect();
    let mut depth = 0i64;
    for (index, character) in characters.iter().enumerate() {
        match character {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth < 0 {
                    return String::new();
                }
            }
            '∧' if depth == 0 => {
                return characters[..index]
                    .iter()
                    .collect::<String>()
                    .trim_matches(char::is_whitespace)
                    .to_string();
            }
            _ => {}
        }
    }
    if depth == 0 { value } else { String::new() }
}

/// Recover the pinned emitter's Skolem names in source order, deduplicated.
fn ordered_skolem_names(source: &str) -> Vec<String> {
    const OPEN: &str = "«_sK";
    let mut names: Vec<String> = Vec::new();
    let mut search_from = 0usize;
    while let Some(offset) = source[search_from..].find(OPEN) {
        let start = search_from + offset;
        let after = start + OPEN.len();
        let digits = source[after..]
            .bytes()
            .take_while(u8::is_ascii_digit)
            .count();
        if digits > 0 && source[after + digits..].starts_with('»') {
            let end = after + digits + '»'.len_utf8();
            let name = source[start..end].to_string();
            if !names.contains(&name) {
                names.push(name);
            }
            search_from = end;
        } else {
            search_from = after;
        }
    }
    names
}

/// Reject every selected Skolem token that is applied to an argument.
fn skolem_names_are_constants(formula: &str, names: &[String]) -> bool {
    for name in names {
        let mut search_from = 0usize;
        while let Some(offset) = formula[search_from..].find(name.as_str()) {
            let end = search_from + offset + name.len();
            let suffix = formula[end..].trim_start_matches(char::is_whitespace);
            if let Some(character) = suffix.chars().next()
                && !matches!(character, ')' | '=' | ',' | '∧' | '∨' | '↔')
            {
                return false;
            }
            search_from = end;
        }
    }
    true
}

/// Count the binders of an `ι`-only existential formula, or reject its
/// shape. `None` means "not a purely existential block over `ι`".
fn constant_existential_count(formula: &str) -> Option<usize> {
    if formula.contains('∀') {
        return None;
    }
    let total = formula.matches('∃').count();
    let mut matched = 0usize;
    let mut binders = 0usize;
    let mut search_from = 0usize;
    while let Some(offset) = formula[search_from..].find('∃') {
        let start = search_from + offset;
        match parse_existential_binders(formula, start + '∃'.len_utf8()) {
            Some((names, end)) => {
                binders += names;
                matched += 1;
                search_from = end;
            }
            None => search_from = start + '∃'.len_utf8(),
        }
    }
    if matched == 0 || matched != total {
        return None;
    }
    Some(binders)
}

/// `\s+v\d+(\s+v\d+)*\s*:\s*ι\s*,` from `index`, returning the binder
/// count and the offset just past the comma.
fn parse_existential_binders(formula: &str, index: usize) -> Option<(usize, usize)> {
    let mut cursor = skip_whitespace(formula, index);
    if cursor == index {
        return None;
    }
    let mut names = 0usize;
    while let Some(after) = parse_binder_name(formula, cursor) {
        names += 1;
        cursor = after;
        let spaced = skip_whitespace(formula, cursor);
        if spaced == cursor || parse_binder_name(formula, spaced).is_none() {
            break;
        }
        cursor = spaced;
    }
    if names == 0 {
        return None;
    }
    cursor = skip_whitespace(formula, cursor);
    cursor = expect(formula, cursor, ':')?;
    cursor = skip_whitespace(formula, cursor);
    cursor = expect(formula, cursor, 'ι')?;
    cursor = skip_whitespace(formula, cursor);
    Some((names, expect(formula, cursor, ',')?))
}

fn skip_whitespace(text: &str, index: usize) -> usize {
    let mut cursor = index;
    while let Some(character) = text[cursor..].chars().next() {
        if !character.is_whitespace() {
            break;
        }
        cursor += character.len_utf8();
    }
    cursor
}

fn expect(text: &str, index: usize, character: char) -> Option<usize> {
    if text[index..].starts_with(character) {
        Some(index + character.len_utf8())
    } else {
        None
    }
}

/// `v<digits>`, returning the offset just past it.
fn parse_binder_name(text: &str, index: usize) -> Option<usize> {
    let rest = text[index..].strip_prefix('v')?;
    let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
    if digits == 0 {
        return None;
    }
    Some(index + 1 + digits)
}

// ------------------------------------------------------------
// The Idempotence Marker
// ------------------------------------------------------------

/// Bind every semantic field the generated slice removes.
///
/// The marker carries only counts and names in plain text; the digest is
/// what makes an edited slice — a reordered witness list, a substituted
/// formula, a redirected source step — recognizable as altered instead of
/// being re-accepted on its own say-so.
fn slice_body_sha256(
    step_id: u64,
    source_step: u64,
    witness_names: &[String],
    original_witness_names: &[String],
    source_formula: &str,
    result_formula: &str,
) -> String {
    let payload = json!({
        "format_version": MARKER_FORMAT_VERSION,
        "step_id": step_id,
        "source_step": source_step,
        "witness_names": witness_names,
        "original_witness_names": original_witness_names,
        "source_formula": source_formula,
        "result_formula": result_formula,
    });
    // `serde_json`'s map is ordered by key, which is the legacy
    // `sort_keys=True`, and its compact form is the legacy
    // `separators=(",", ":")` with `ensure_ascii=False`.
    bytes_sha256(payload.to_string().as_bytes())
}

/// One generated slice recovered from an already-rewritten proof.
#[derive(Clone, Debug)]
pub(super) struct GeneratedSlice {
    step_id: u64,
    retained: Vec<String>,
    original_count: usize,
}

/// The generated slice's own eight lines, from the marker.
const SLICE_LINES: usize = 8;

/// Parse the complete generated slice at `line_number`, or refuse an
/// altered one.
///
/// `Ok(None)` means "not a generated slice"; an `Err` means the marker is
/// one this rewrite wrote and the block below it no longer is.
pub(super) fn parse_generated_slice(
    lines: &[&str],
    code_lines: &[&str],
    line_number: usize,
    comment_lines: &BTreeSet<usize>,
) -> Result<Option<GeneratedSlice>, String> {
    let marker = match parse_slice_marker(lines[line_number]) {
        Some(marker) => marker,
        None => {
            if let Some(step_id) = near_slice_marker(lines[line_number])
                && comment_lines.contains(&line_number)
            {
                return Err(altered_slice(step_id));
            }
            return Ok(None);
        }
    };
    if !comment_lines.contains(&line_number) {
        return Ok(None);
    }
    let SliceMarker {
        step_id,
        source_step,
        retained_count,
        original_count,
        originals,
        digest,
    } = marker;
    let altered = || altered_slice(step_id);

    if line_number + SLICE_LINES > lines.len() {
        return Err(altered());
    }
    let source_formula = strip_between(
        code_lines[line_number + 1],
        &format!("  have step{step_id}_slice : "),
        " := by",
    )
    .ok_or_else(altered)?;
    let witnesses = strip_between(
        code_lines[line_number + 4],
        "  let ⟨",
        &format!(",step{step_id}_slice'⟩ := step{step_id}_slice"),
    )
    .ok_or_else(altered)?;
    let result_formula = strip_between(
        code_lines[line_number + 5],
        &format!("  have step{step_id}_first : "),
        " := by",
    )
    .ok_or_else(altered)?;
    if code_lines[line_number + 2] != format!("{PROJECT_CALL_PREFIX}{source_step}")
        || code_lines[line_number + 3] != format!("  exists_prenex at step{step_id}_slice")
        || code_lines[line_number + 6] != format!("    symm_match using step{step_id}_slice'")
        || code_lines[line_number + 7]
            != format!("  have step{step_id} := And.intro step{step_id}_first step{source_step}")
    {
        return Err(altered());
    }

    let witnesses: Vec<String> = witnesses.split(',').map(str::to_string).collect();
    let result_names = ordered_skolem_names(&result_formula);
    let retained_set: BTreeSet<&String> = witnesses.iter().collect();
    let filtered: Vec<String> = originals
        .iter()
        .filter(|name| retained_set.contains(name))
        .cloned()
        .collect();
    if retained_count < 1
        || retained_count > original_count
        || originals.len() != original_count
        || has_duplicates(&originals)
        || digest
            != slice_body_sha256(
                step_id,
                source_step,
                &witnesses,
                &originals,
                &source_formula,
                &result_formula,
            )
        || witnesses.len() != retained_count
        || has_duplicates(&witnesses)
        || witnesses.iter().any(|name| !is_skolem_name(name))
        || originals.iter().any(|name| !is_skolem_name(name))
        || witnesses != filtered
        || result_names.iter().collect::<BTreeSet<_>>() != retained_set
        || constant_existential_count(&source_formula) != Some(retained_count)
        || !skolem_names_are_constants(&result_formula, &result_names)
    {
        return Err(altered());
    }
    Ok(Some(GeneratedSlice {
        step_id,
        retained: witnesses,
        original_count,
    }))
}

/// The line the generated slice's `vampire_project_ordered` call sits on,
/// relative to its marker. Pass 7.9a's projection recognizer needs it:
/// that call is a legitimate generated call site it does not own.
pub(super) const SLICE_PROJECT_CALL_OFFSET: usize = 2;

fn altered_slice(step_id: u64) -> String {
    format!("has an altered dependency-sliced skolem step {step_id}")
}

fn has_duplicates(names: &[String]) -> bool {
    names.iter().collect::<BTreeSet<_>>().len() != names.len()
}

/// `prefix<middle>suffix`, with a nonempty middle.
fn strip_between(line: &str, prefix: &str, suffix: &str) -> Option<String> {
    let middle = line.strip_prefix(prefix)?.strip_suffix(suffix)?;
    if middle.is_empty() {
        return None;
    }
    Some(middle.to_string())
}

struct SliceMarker {
    step_id: u64,
    source_step: u64,
    retained_count: usize,
    original_count: usize,
    originals: Vec<String>,
    digest: String,
}

/// `  -- step<N> dependency-sliced skolemisation from step<M> (<r>/<o>
/// witnesses; originals: «_sK…»,…; sha256: <64 hex>)`
fn parse_slice_marker(line: &str) -> Option<SliceMarker> {
    let rest = line.strip_prefix("  -- step")?;
    let (step_id, rest) = split_step(rest, " dependency-sliced skolemisation from step")?;
    let (source_step, rest) = split_step(rest, " (")?;
    let rest = rest.strip_suffix(')')?;
    let (counts, rest) = rest.split_once(" witnesses; originals: ")?;
    let (retained, original) = counts.split_once('/')?;
    let (originals, digest) = rest.split_once("; sha256: ")?;
    if digest.len() != 64
        || !digest
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return None;
    }
    if !is_ascii_digits(retained) || !is_ascii_digits(original) {
        return None;
    }
    let originals: Vec<String> = originals.split(',').map(str::to_string).collect();
    if originals.iter().any(|name| !is_skolem_name(name)) {
        return None;
    }
    Some(SliceMarker {
        step_id,
        source_step,
        retained_count: retained.parse().ok()?,
        original_count: original.parse().ok()?,
        originals,
        digest: digest.to_string(),
    })
}

/// A leading run of digits, then `separator`.
fn split_step<'a>(text: &'a str, separator: &str) -> Option<(u64, &'a str)> {
    let boundary = text.find(|character: char| !character.is_ascii_digit())?;
    let (digits, tail) = text.split_at(boundary);
    Some((parse_digits(digits)?, tail.strip_prefix(separator)?))
}

/// A marker this rewrite plainly wrote, whose exact shape no longer parses.
fn near_slice_marker(line: &str) -> Option<u64> {
    let rest = line.strip_prefix("  -- step")?;
    let boundary = rest.find(|character: char| !character.is_ascii_digit())?;
    let (digits, tail) = rest.split_at(boundary);
    if !tail.starts_with(" dependency-sliced skolemisation") {
        return None;
    }
    parse_digits(digits)
}

// ------------------------------------------------------------
// Lineage
// ------------------------------------------------------------

/// The nearest `change`d full formula the prenexed step descends from.
///
/// Only lines above the block's marker are considered, and only the
/// `have stepN := …` definition graph is followed, so the formula is one
/// the emitter itself stated for a step this block's input was built from.
fn step_reaches_change(
    code_lines: &[&str],
    source_step: u64,
    marker_line: usize,
) -> Option<String> {
    let mut definitions: HashMap<u64, Vec<u64>> = HashMap::new();
    let mut changes: HashMap<u64, (usize, String)> = HashMap::new();
    for (line_number, line) in code_lines[..marker_line.min(code_lines.len())]
        .iter()
        .enumerate()
    {
        if let Some((formula, step_id)) = parse_change(line) {
            changes.insert(step_id, (line_number, formula));
            continue;
        }
        if let Some((step_id, body)) = parse_definition(line) {
            definitions.insert(step_id, step_references(body));
        }
    }

    let mut seen: BTreeSet<u64> = BTreeSet::new();
    let mut pending = vec![source_step];
    let mut reachable: Vec<(usize, String)> = Vec::new();
    while let Some(step_id) = pending.pop() {
        if !seen.insert(step_id) {
            continue;
        }
        if let Some(change) = changes.get(&step_id) {
            reachable.push(change.clone());
        }
        if let Some(dependencies) = definitions.get(&step_id) {
            pending.extend(dependencies.iter().copied());
        }
    }
    reachable
        .into_iter()
        .max_by_key(|(line_number, _)| *line_number)
        .map(|(_, formula)| formula)
}

// ------------------------------------------------------------
// Rewrite
// ------------------------------------------------------------

/// Replace every exact constant-only global skolemisation block by its
/// dependency slice.
///
/// The input must already be canonical (see [`super::canonical`]) and
/// already projected (see [`super::projection`]): the live witnesses are
/// read off the projected targets' own statements, never from a
/// case-specific recipe.
pub(super) fn rewrite_prenex_slices(source: &str) -> Result<PrenexSliceSummary, String> {
    let lines = split_lines(source);
    let masked = code_without_comments_or_strings(source)?;
    let code_lines = split_lines(&masked);
    let comment_lines = line_comment_lines(source);

    let mut edits: Vec<(usize, usize, Vec<String>)> = Vec::new();
    let mut slices: Vec<Slice> = Vec::new();
    let mut missed: Vec<(u64, &'static str)> = Vec::new();
    let mut generated_lines: BTreeSet<usize> = BTreeSet::new();

    for line_number in 0..lines.len() {
        if let Some(existing) =
            parse_generated_slice(&lines, &code_lines, line_number, &comment_lines)?
        {
            slices.push(Slice {
                step_id: existing.step_id,
                retained: existing.retained,
                original_count: existing.original_count,
            });
            generated_lines.extend(line_number..line_number + SLICE_LINES);
            continue;
        }
        let step_id = match match_skolem_marker(lines[line_number]) {
            Some(step_id) if comment_lines.contains(&line_number) => step_id,
            _ => continue,
        };
        match slice_block(&lines, &code_lines, line_number, step_id) {
            Ok(accepted) => {
                edits.push((line_number, line_number + 4, accepted.replacement));
                slices.push(accepted.slice);
            }
            Err(reason) => missed.push((step_id, reason)),
        }
    }

    // Nothing but this rewrite may own a `_slice`/`_first` name: an
    // orphaned or hand-edited one would otherwise be carried into a
    // published proof under a marker that no longer describes it.
    for (line_number, line) in code_lines.iter().enumerate() {
        if !generated_lines.contains(&line_number) && contains_generated_name(line) {
            return Err("has an unowned dependency-sliced proof line".to_string());
        }
    }
    let mut step_ids: Vec<u64> = slices.iter().map(|slice| slice.step_id).collect();
    let count = step_ids.len();
    step_ids.sort_unstable();
    step_ids.dedup();
    if step_ids.len() != count {
        return Err("repeats a dependency-sliced skolem step".to_string());
    }

    let mut rewritten_lines: Vec<String> = lines.iter().map(|line| (*line).to_string()).collect();
    edits.sort_by(|left, right| right.0.cmp(&left.0));
    for (start, end, replacement) in edits {
        rewritten_lines.splice(start..end, replacement);
    }
    let rewritten = format!(
        "{}\n",
        rewritten_lines.join("\n").trim_matches(char::is_whitespace)
    );

    Ok(PrenexSliceSummary {
        source: rewritten,
        slices,
        missed,
    })
}

/// Whether a masked line uses a `step<N>_slice`/`step<N>_first` name, which
/// only a generated slice may own.
fn contains_generated_name(line: &str) -> bool {
    let mut search_from = 0usize;
    while let Some(offset) = line[search_from..].find("step") {
        let start = search_from + offset;
        let after = start + "step".len();
        let digits = line[after..].bytes().take_while(u8::is_ascii_digit).count();
        let delimited = !line[..start]
            .chars()
            .next_back()
            .is_some_and(is_ascii_word_char);
        if digits > 0 && delimited {
            for suffix in ["_slice", "_first"] {
                if let Some(rest) = line[after + digits..].strip_prefix(suffix) {
                    // The pattern's optional prime means a following `'`
                    // matches either way, greedily or by backtracking onto
                    // the `'`, which is not a word character.
                    let next = rest.chars().next();
                    if next == Some('\'') || !next.is_some_and(is_ascii_word_char) {
                        return true;
                    }
                }
            }
        }
        search_from = after;
    }
    false
}

/// One accepted block: the eight lines that replace it, and its receipt row.
struct AcceptedSlice {
    replacement: Vec<String>,
    slice: Slice,
}

/// Decide one exact skolemisation block, or name the structural reason it
/// falls outside the contract.
///
/// Every `Err` here is a *miss*: the block is left exactly as Vampire
/// wrote it and the projected proof stands.
fn slice_block(
    lines: &[&str],
    code_lines: &[&str],
    line_number: usize,
    step_id: u64,
) -> Result<AcceptedSlice, &'static str> {
    if line_number + 3 >= lines.len() {
        return Err("truncated_skolem_block");
    }
    let source_step =
        match_skolem_prenex(code_lines[line_number + 1]).ok_or("altered_prenex_call")?;
    let witnesses: Vec<String> = strip_between(
        code_lines[line_number + 2],
        "  let ⟨",
        &format!(",step{step_id}'⟩ := step{source_step}"),
    )
    .ok_or("altered_witness_destructure")?
    .split(',')
    .map(str::to_string)
    .collect();
    if has_duplicates(&witnesses) || witnesses.iter().any(|name| !is_skolem_name(name)) {
        return Err("altered_witness_destructure");
    }
    let post_formula = strip_between(
        code_lines[line_number + 3],
        &format!("  have step{step_id} : "),
        &format!(" := by symm_match using step{step_id}'"),
    )
    .ok_or("altered_skolem_result")?;

    // The live witnesses are exactly the ones the projected targets state.
    let mut targets: Vec<(usize, usize)> = Vec::new();
    let mut live: Vec<String> = Vec::new();
    let projection_call = format!("{PROJECT_CALL_PREFIX}{step_id}");
    let mut cursor = line_number + 4;
    while cursor < lines.len() {
        // `strict` is false here: an unrecognized `have` below the block
        // is simply not one of this block's targets.
        let parsed = parse_target_header(lines, code_lines, cursor, None, false)
            .map_err(|_| "malformed_projection_target")?;
        let (_, header_end) = match parsed {
            Some(parsed) => parsed,
            None => {
                cursor += 1;
                continue;
            }
        };
        let body_start = header_end + 1;
        let body_end = tactic_body_end(lines, header_end);
        if lines[body_start..body_end] != [projection_call.as_str()] {
            cursor = (cursor + 1).max(body_end);
            continue;
        }
        for name in ordered_skolem_names(&code_lines[cursor..=header_end].join("\n")) {
            if !live.contains(&name) {
                live.push(name);
            }
        }
        targets.push((body_start, body_end));
        cursor = body_end;
    }
    if targets.is_empty() {
        return Err("no_exact_projection_targets");
    }

    let first_post = first_formula_conjunct(&post_formula);
    let branch: Vec<String> = ordered_skolem_names(&first_post);
    let branch_set: BTreeSet<&String> = branch.iter().collect();
    let witness_set: BTreeSet<&String> = witnesses.iter().collect();
    if live.is_empty()
        || live.iter().collect::<BTreeSet<_>>() != branch_set
        || !branch_set.is_subset(&witness_set)
    {
        return Err("live_witnesses_not_first_conjunct");
    }
    if !skolem_names_are_constants(&first_post, &branch) {
        return Err("function_valued_live_witness");
    }
    let changed = step_reaches_change(code_lines, source_step, line_number)
        .ok_or("no_changed_formula_lineage")?;
    let first_source = first_formula_conjunct(&changed);
    // The later inference can expand XOR into CNF. The ancestor's XOR is
    // then no longer an assumption that vampire_project_ordered can select.
    // Decline that known unsupported lineage; Lean still checks every slice.
    if first_source
        .split(|character: char| {
            !(character.is_alphanumeric() || matches!(character, '_' | '\'' | '.' | '«' | '»'))
        })
        .any(|token| matches!(token, "Xor'" | "VampLean.Xor'"))
    {
        return Err("unsupported_first_conjunct_xor_lineage");
    }
    if constant_existential_count(&first_source) != Some(branch.len()) {
        return Err("unsupported_first_conjunct_quantifiers");
    }

    // Nothing below the block may still need what the slice drops, nor
    // the unsliced global step itself. The projected targets are blanked
    // out first: they are exactly what the slice keeps proving.
    let mut external: Vec<String> = code_lines[line_number + 4..]
        .iter()
        .map(|line| (*line).to_string())
        .collect();
    for (body_start, body_end) in targets {
        for index in body_start..body_end {
            external[index - line_number - 4] = String::new();
        }
    }
    let suffix = external.join("\n");
    if witnesses
        .iter()
        .filter(|name| !branch_set.contains(*name))
        .any(|name| contains_delimited(&suffix, name, is_ascii_word_char))
    {
        return Err("discarded_witness_used_later");
    }
    if contains_step_use(&suffix, step_id) {
        return Err("global_step_used_later");
    }

    let retained: Vec<String> = witnesses
        .iter()
        .filter(|name| branch_set.contains(*name))
        .cloned()
        .collect();
    let digest = slice_body_sha256(
        step_id,
        source_step,
        &retained,
        &witnesses,
        &first_source,
        &first_post,
    );
    let replacement = vec![
        format!(
            "  -- step{step_id} dependency-sliced skolemisation from step{source_step} ({}/{} \
             witnesses; originals: {}; sha256: {digest})",
            retained.len(),
            witnesses.len(),
            witnesses.join(","),
        ),
        format!("  have step{step_id}_slice : {first_source} := by"),
        format!("{PROJECT_CALL_PREFIX}{source_step}"),
        format!("  exists_prenex at step{step_id}_slice"),
        format!(
            "  let ⟨{},step{step_id}_slice'⟩ := step{step_id}_slice",
            retained.join(",")
        ),
        format!("  have step{step_id}_first : {first_post} := by"),
        format!("    symm_match using step{step_id}_slice'"),
        format!("  have step{step_id} := And.intro step{step_id}_first step{source_step}"),
    ];
    Ok(AcceptedSlice {
        replacement,
        slice: Slice {
            step_id,
            retained,
            original_count: witnesses.len(),
        },
    })
}
