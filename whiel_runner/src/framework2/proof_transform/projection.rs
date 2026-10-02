//! Targeted clause projection (legacy transformation 4).
//!
//! Vampire's emitter proves a family of clauses by normalizing one global
//! step into CNF and then closing each target by `assumption` against the
//! destructured conjuncts:
//!
//! ```text
//!   have step19' := by
//!     prenexify at step19
//!     cnfify at step19
//!     exact step19
//!   let ⟨s19c0, s19c1, s19c2⟩ := step19'
//!   ac_nf0 at s19c0 s19c1 s19c2
//!
//!   have step47 : <clause> := by
//!     try simp only
//!     ac_nf0
//!     assumption
//! ```
//!
//! The whole normalization package is deleted and each target is proved
//! directly from the *un*normalized `step19` by the Whiel-owned
//! `vampire_project_ordered` tactic
//! (`Whiel/Vampire/ClauseProjection.lean`), which builds ordinary
//! `And`/`Or`/`∀` eliminator applications the kernel checks:
//!
//! ```text
//!   have step47 : <clause> := by
//!     vampire_project_ordered using step19
//! ```
//!
//! The recognizer is deliberately all-or-nothing. Once a complete
//! normalization core has matched, every clause destructure and every
//! target below it must match either the pinned assumption-only body or
//! its exact quantified-binder reorder variant, so the rewrite can never
//! silently become partial; an unrecognized *core* is an ordinary miss
//! and leaves the proof untouched. Re-running the rewrite on an
//! already-rewritten proof reconstructs the same metadata and changes no
//! byte.
//!
//! This is a port of `whiel_synth.verification.tier1_bundle`'s
//! `rewrite_vamplean_projection_blocks` and its helpers, kept in
//! differential parity with it on the reference shapes.

use serde_json::{Value, json};

/// One recognized target below a global normalization core.
#[derive(Clone, Debug)]
struct Target {
    step_id: u64,
    body_start: usize,
    body_end: usize,
}

/// One complete pinned global `prenexify`/`cnfify` block.
#[derive(Clone, Debug)]
struct Block {
    step_id: u64,
    core_start: usize,
    core_end: usize,
    targets: Vec<Target>,
}

/// The result of one projection rewrite.
#[derive(Clone, Debug)]
pub struct ProjectionSummary {
    /// The rewritten (or, on a miss, unchanged) proof text.
    pub source: String,
    /// The global steps that are now projected from, in source order.
    pub step_ids: Vec<u64>,
    /// For each of those, the targets projected out of it.
    pub projected_step_ids: Vec<Vec<u64>>,
    /// Global normalization steps left exactly as Vampire wrote them.
    pub missed_step_ids: Vec<u64>,
}

impl ProjectionSummary {
    pub fn block_count(&self) -> usize {
        self.step_ids.len()
    }

    pub fn projection_count(&self) -> usize {
        self.projected_step_ids.iter().map(Vec::len).sum()
    }

    /// The receipt's own counters for this rewrite.
    pub fn detail(&self) -> Value {
        json!({
            "blocks": self.block_count(),
            "projections": self.projection_count(),
            "step_ids": self.step_ids,
            "projected_step_ids": self.projected_step_ids,
            "missed_step_ids": self.missed_step_ids,
        })
    }
}

/// The pinned assumption-only target body.
const PROJECTION_BODY: [&str; 3] = ["    try simp only", "    ac_nf0", "    assumption"];
/// The quantified-binder reorder variant's fixed first and last lines.
const REORDER_PREFIX: [&str; 1] = ["    try simp only"];
const REORDER_SUFFIX: [&str; 3] = ["    rw[reorder]", "    ac_nf0", "    assumption"];
/// The tactic call the rewrite emits.
pub(super) const PROJECT_CALL_PREFIX: &str = "    vampire_project_ordered using step";
/// The bare token every executable projection call must be part of.
const PROJECT_TOKEN: &str = "vampire_project";

// ------------------------------------------------------------
// Line Shapes
// ------------------------------------------------------------

/// Python's `str.splitlines` over the one separator canonical text can
/// contain: no trailing empty element for a final newline.
pub(super) fn split_lines(source: &str) -> Vec<&str> {
    let mut lines: Vec<&str> = source.split('\n').collect();
    if source.ends_with('\n') {
        lines.pop();
    }
    lines
}

fn is_word_char(character: char) -> bool {
    character.is_alphanumeric() || character == '_'
}

pub(super) fn is_ascii_word_char(character: char) -> bool {
    character.is_ascii_alphanumeric() || character == '_'
}

pub(super) fn parse_digits(text: &str) -> Option<u64> {
    if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    text.parse().ok()
}

/// `  have stepN' := by`
fn match_global_header(line: &str) -> Option<u64> {
    parse_digits(line.strip_prefix("  have step")?.strip_suffix("' := by")?)
}

/// `\s*prenexify at stepN\s*`
fn match_global_prenex(line: &str) -> Option<u64> {
    parse_digits(
        line.trim_matches(char::is_whitespace)
            .strip_prefix("prenexify at step")?,
    )
}

/// `\s*cnfify at stepN\s*`
fn match_global_cnf(line: &str) -> Option<u64> {
    parse_digits(
        line.trim_matches(char::is_whitespace)
            .strip_prefix("cnfify at step")?,
    )
}

/// `  have stepN :` optionally followed by one space and a type fragment.
fn match_target_header(line: &str) -> Option<(u64, &str)> {
    let rest = line.strip_prefix("  have step")?;
    let boundary = rest.find(|character: char| !character.is_ascii_digit())?;
    let (digits, tail) = rest.split_at(boundary);
    let step_id = parse_digits(digits)?;
    if tail == " :" {
        return Some((step_id, ""));
    }
    Some((step_id, tail.strip_prefix(" : ")?))
}

/// `    vampire_project_ordered using stepN`
fn match_project_call(line: &str) -> Option<u64> {
    parse_digits(line.strip_prefix(PROJECT_CALL_PREFIX)?)
}

/// The legacy `\bvampire_project(?:_ordered)?\b` search.
fn contains_project_token(text: &str) -> bool {
    let mut search_from = 0usize;
    while let Some(offset) = text[search_from..].find(PROJECT_TOKEN) {
        let start = search_from + offset;
        let after = start + PROJECT_TOKEN.len();
        if !text[..start].chars().next_back().is_some_and(is_word_char) {
            if let Some(rest) = text[after..].strip_prefix("_ordered")
                && !rest.chars().next().is_some_and(is_word_char)
            {
                return true;
            }
            if !text[after..].chars().next().is_some_and(is_word_char) {
                return true;
            }
        }
        search_from = after;
    }
    false
}

/// Whether `name` occurs in `text` delimited by non-word characters.
fn contains_word(text: &str, name: &str) -> bool {
    contains_delimited(text, name, is_word_char)
}

/// Whether `stepN'` occurs in `text` outside any longer identifier, the
/// legacy `(?<![A-Za-z0-9_])stepN'(?![A-Za-z0-9_])` search.
fn contains_primed_step(text: &str, step_id: u64) -> bool {
    contains_delimited(text, &format!("step{step_id}'"), is_ascii_word_char)
}

pub(super) fn contains_delimited(text: &str, needle: &str, is_boundary: fn(char) -> bool) -> bool {
    let mut search_from = 0usize;
    while let Some(offset) = text[search_from..].find(needle) {
        let start = search_from + offset;
        let end = start + needle.len();
        let before = text[..start].chars().next_back().is_some_and(is_boundary);
        let after = text[end..].chars().next().is_some_and(is_boundary);
        if !before && !after {
            return true;
        }
        search_from = end;
    }
    false
}

// ------------------------------------------------------------
// Comment And String Masking
// ------------------------------------------------------------

/// Replace every Lean comment and string literal by spaces, keeping the
/// line structure, so a shape recognizer never reads commented-out or
/// quoted text as code.
pub(super) fn code_without_comments_or_strings(source: &str) -> Result<String, String> {
    Ok(scan_source_lexical_layout(source)?.code)
}

/// Lexical facts needed before canonicalization changes any source bytes.
pub(super) struct SourceLexicalLayout {
    pub code: String,
    /// Lines whose comment begins at column zero in code, not a comment
    /// later on a line that began inside a block comment or a literal.
    pub line_comments: std::collections::BTreeSet<usize>,
    pub multiline_string: bool,
    pub unsupported_literal: bool,
}

/// Scan the original text without normalizing literal contents. Line
/// numbers count LF characters; callers using them for line rewrites
/// first normalize line endings, after refusing multiline literals.
pub(super) fn scan_source_lexical_layout(source: &str) -> Result<SourceLexicalLayout, String> {
    let characters: Vec<char> = source.chars().collect();
    let mut output = String::with_capacity(source.len());
    let mut line_comments = std::collections::BTreeSet::new();
    let mut multiline_string = false;
    let mut unsupported_literal = false;
    let mut line = 0usize;
    let mut index = 0usize;
    let mut block_depth = 0usize;
    let mut in_string = false;
    let mut escaped = false;
    while index < characters.len() {
        let character = characters[index];
        let next = characters.get(index + 1).copied();
        if block_depth > 0 {
            if character == '/' && next == Some('-') {
                block_depth += 1;
                output.push_str("  ");
                index += 2;
            } else if character == '-' && next == Some('/') {
                block_depth -= 1;
                output.push_str("  ");
                index += 2;
            } else {
                output.push(if matches!(character, '\n' | '\r') {
                    character
                } else {
                    ' '
                });
                line += usize::from(character == '\n');
                index += 1;
            }
            continue;
        }
        if in_string {
            let line_break = matches!(character, '\n' | '\r');
            multiline_string |= line_break;
            output.push(if line_break { character } else { ' ' });
            line += usize::from(character == '\n');
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
            if index == 0 || matches!(characters[index - 1], '\n' | '\r') {
                line_comments.insert(line);
            }
            match characters[index..]
                .iter()
                .position(|candidate| matches!(candidate, '\n' | '\r'))
            {
                Some(offset) => {
                    let newline = index + offset;
                    output.extend(std::iter::repeat_n(' ', newline - index));
                    index = newline;
                }
                None => {
                    output.extend(std::iter::repeat_n(' ', characters.len() - index));
                    break;
                }
            }
            continue;
        }
        if character == '/' && next == Some('-') {
            block_depth = 1;
            output.push_str("  ");
            index += 2;
            continue;
        }
        if character == '«' {
            // Quoted identifiers are code, not strings; a comment marker
            // or quote inside one cannot change the surrounding lexical
            // context. Only the emitter's simple ASCII names are admitted
            // by canonicalization, before whitespace can change a name.
            output.push(character);
            index += 1;
            let name_start = index;
            while characters.get(index).is_some_and(|value| *value != '»') {
                let value = characters[index];
                unsupported_literal |=
                    !value.is_ascii_alphanumeric() && value != '_' && value != '\'';
                output.push(value);
                line += usize::from(value == '\n');
                index += 1;
            }
            if characters.get(index).is_none() {
                return Err("raw proof has an unterminated quoted identifier".to_string());
            }
            unsupported_literal |= name_start == index;
            output.push('»');
            index += 1;
            continue;
        }
        // The pinned emitter has no syntax quotations, raw-string or character literal
        // syntax. Those forms have different quote/escape rules, so a
        // recognizer must refuse them rather than guess their boundaries.
        if character == '`' {
            return Err("raw proof carries an unsupported syntax quotation".to_string());
        }
        if character == 'r' {
            let mut quote = index + 1;
            while characters.get(quote) == Some(&'#') {
                quote += 1;
            }
            if characters.get(quote) == Some(&'"') {
                return Err("raw proof carries an unsupported raw string literal".to_string());
            }
        }
        if character == '\''
            && (index == 0
                || !matches!(characters[index - 1], '_' | '\'' | '»')
                    && !characters[index - 1].is_alphanumeric())
        {
            return Err("raw proof carries an unsupported character literal".to_string());
        }
        if character == '"' {
            if output.trim_end().ends_with('!') {
                return Err(
                    "raw proof carries an unsupported interpolated string literal".to_string(),
                );
            }
            in_string = true;
            output.push(' ');
        } else {
            output.push(character);
            line += usize::from(character == '\n');
        }
        index += 1;
    }
    if block_depth > 0 || in_string {
        return Err("raw proof has an unterminated comment or string".to_string());
    }
    Ok(SourceLexicalLayout {
        code: output,
        line_comments,
        multiline_string,
        unsupported_literal,
    })
}

// ------------------------------------------------------------
// Target Recognition
// ------------------------------------------------------------

/// The end of one indented generated tactic body, trailing blank lines
/// excluded.
pub(super) fn tactic_body_end(lines: &[&str], header_end: usize) -> usize {
    let mut cursor = header_end + 1;
    while cursor < lines.len() {
        let line = lines[cursor];
        if line.is_empty() || line.starts_with("    ") {
            cursor += 1;
            continue;
        }
        break;
    }
    while cursor > header_end + 1 && lines[cursor - 1].is_empty() {
        cursor -= 1;
    }
    cursor
}

/// Drop the last six characters, the way Python's `s[:-6]` does.
fn drop_last_six(text: &str) -> String {
    let characters: Vec<char> = text.chars().collect();
    characters[..characters.len().saturating_sub(6)]
        .iter()
        .collect()
}

/// Parse one typed `have stepN` through its exact `:= by`, returning the
/// step and the line the `:= by` sits on.
///
/// `strict` turns "this is not a well-formed target" from a miss into a
/// refusal: below a matched normalization core nothing may be ambiguous.
pub(super) fn parse_target_header(
    lines: &[&str],
    code_lines: &[&str],
    start: usize,
    source_step: Option<u64>,
    strict: bool,
) -> Result<Option<(u64, usize)>, String> {
    if start >= lines.len() || lines[start] != code_lines[start] {
        return Ok(None);
    }
    let (target_step, target_type) = match match_target_header(lines[start]) {
        Some(parsed) => parsed,
        None => return Ok(None),
    };
    let mut cursor = start;
    let mut fragments: Vec<String> = vec![target_type.to_string()];
    loop {
        let line = code_lines[cursor];
        if line.ends_with(" := by") {
            if line.matches(" := by").count() != 1 {
                break;
            }
            let last = fragments.len() - 1;
            fragments[last] = drop_last_six(&fragments[last]);
            if fragments.iter().any(|fragment| !fragment.trim().is_empty()) {
                return Ok(Some((target_step, cursor)));
            }
            break;
        }
        if line.contains(" := by") {
            break;
        }
        cursor += 1;
        if cursor >= lines.len()
            || lines[cursor] != code_lines[cursor]
            || lines[cursor].is_empty()
            || !lines[cursor].starts_with("    ")
        {
            break;
        }
        fragments.push(lines[cursor].to_string());
    }
    if strict {
        let context = match source_step {
            Some(step) => format!(" below step {step}"),
            None => String::new(),
        };
        return Err(format!(
            "malformed projection target step {target_step}{context}"
        ));
    }
    Ok(None)
}

/// The `have reorder …` helper's `(lhs, rhs)` binder lists, or `None` if
/// the line is not exactly the emitter's own helper.
fn parse_reorder_helper(line: &str) -> Option<(Vec<String>, Vec<String>)> {
    let mut rest = line.strip_prefix("    have reorder (P :")?;
    let mut arrows = 0usize;
    while let Some(remainder) = rest.strip_prefix("ι→") {
        rest = remainder;
        arrows += 1;
    }
    let rest = rest.strip_prefix("Prop) : ( ∀ ")?;
    let (lhs_first, rest) = rest.split_once(", P ")?;
    let (lhs_second, rest) = rest.split_once(") ↔ (∀ ")?;
    let (rhs_first, rest) = rest.split_once(" , P ")?;
    let (lhs_third, rest) = rest.split_once(") := Iff.intro (fun f ")?;
    let (rhs_second, rest) = rest.split_once("  => f ")?;
    let (lhs_fourth, rest) = rest.split_once(") (fun f ")?;
    let (lhs_fifth, rhs_tail) = rest.split_once(" => f ")?;
    let rhs_third = rhs_tail.strip_suffix(" )")?;

    if [lhs_second, lhs_third, lhs_fourth, lhs_fifth]
        .iter()
        .any(|repeat| *repeat != lhs_first)
        || rhs_second != rhs_first
        || rhs_third != rhs_first
    {
        return None;
    }
    let lhs = parse_binder_names(lhs_first)?;
    let rhs = parse_binder_names(rhs_first)?;
    if arrows != lhs.len() {
        return None;
    }
    Some((lhs, rhs))
}

/// One space-separated run of `v<digits>` binder names.
fn parse_binder_names(text: &str) -> Option<Vec<String>> {
    if text.is_empty() {
        return None;
    }
    let mut names = Vec::new();
    for name in text.split(' ') {
        parse_digits(name.strip_prefix('v')?)?;
        names.push(name.to_string());
    }
    Some(names)
}

/// The binder run of a `  have stepN : (∀ v0 v1 : ι,` target header.
fn target_header_binders(line: &str, target_step: u64) -> Option<Vec<String>> {
    let rest = line.strip_prefix(&format!("  have step{target_step} : (∀ "))?;
    let boundary = rest.find(" : ι,")?;
    parse_binder_names(&rest[..boundary])
}

/// Recognize only the pinned assumption body and its exact quantified
/// reorder variant.
fn is_projection_body(body: &[&str], target_header: &[&str], target_step: u64) -> bool {
    if body == PROJECTION_BODY {
        return true;
    }
    if body.len() != 5 || body[..1] != REORDER_PREFIX || body[2..] != REORDER_SUFFIX {
        return false;
    }
    let (lhs, rhs) = match parse_reorder_helper(body[1]) {
        Some(parsed) => parsed,
        None => return false,
    };
    if lhs.is_empty() || lhs == rhs {
        return false;
    }
    let mut sorted_lhs = lhs.clone();
    let mut sorted_rhs = rhs.clone();
    sorted_lhs.sort();
    sorted_rhs.sort();
    let (lhs_len, rhs_len) = (sorted_lhs.len(), sorted_rhs.len());
    sorted_lhs.dedup();
    sorted_rhs.dedup();
    if sorted_lhs.len() != lhs_len || sorted_rhs.len() != rhs_len || sorted_lhs != sorted_rhs {
        return false;
    }
    if target_header.len() != 1 {
        return false;
    }
    target_header_binders(target_header[0], target_step).is_some_and(|binders| binders == lhs)
}

// ------------------------------------------------------------
// Block Recognition
// ------------------------------------------------------------

/// `  let ⟨sNc0, sNc1, …⟩ := stepN'`
fn parse_clause_destructure(line: &str, step_id: u64) -> Option<Vec<String>> {
    let rest = line.strip_prefix("  let ⟨")?;
    let rest = rest.strip_suffix(&format!("⟩ := step{step_id}'"))?;
    if rest.is_empty() {
        return None;
    }
    let clause_prefix = format!("s{step_id}c");
    let mut names = Vec::new();
    for name in rest.split(", ") {
        parse_digits(name.strip_prefix(&clause_prefix)?)?;
        names.push(name.to_string());
    }
    Some(names)
}

/// Accept one complete pinned global prenex/CNF emitter block.
fn parse_projection_block(
    lines: &[&str],
    code_lines: &[&str],
    start: usize,
) -> Result<Option<Block>, String> {
    let step_id = match match_global_header(code_lines[start]) {
        Some(step_id) if lines[start] == code_lines[start] => step_id,
        _ => return Ok(None),
    };
    let expected = [
        format!("    prenexify at step{step_id}"),
        format!("    cnfify at step{step_id}"),
        format!("    exact step{step_id}"),
    ];
    if start + 4 > lines.len()
        || lines[start + 1..start + 4]
            .iter()
            .zip(expected.iter())
            .any(|(found, wanted)| found != wanted)
    {
        return Ok(None);
    }
    if start + 5 >= lines.len() {
        return Err(format!("truncated global CNF step {step_id}"));
    }

    let clause_names = parse_clause_destructure(lines[start + 4], step_id)
        .ok_or_else(|| format!("global CNF step {step_id} has an altered clause destructure"))?;
    let expected_clauses: Vec<String> = (0..clause_names.len())
        .map(|index| format!("s{step_id}c{index}"))
        .collect();
    if clause_names != expected_clauses {
        return Err(format!(
            "global CNF step {step_id} has noncontiguous clause names"
        ));
    }
    if lines[start + 5] != format!("  ac_nf0 at {}", clause_names.join(" ")) {
        return Err(format!(
            "global CNF step {step_id} has an altered clause normalization"
        ));
    }

    let mut targets: Vec<Target> = Vec::new();
    let mut cursor = start + 6;
    loop {
        while cursor < lines.len() && lines[cursor].is_empty() {
            cursor += 1;
        }
        if cursor >= lines.len() || match_target_header(code_lines[cursor]).is_none() {
            break;
        }
        // A masked header that does not match its own raw line is a
        // commented-out or quoted target below a matched core: ambiguous,
        // so refuse rather than guess.
        let (target_step, header_end) =
            parse_target_header(lines, code_lines, cursor, Some(step_id), true)?.ok_or_else(
                || format!("global CNF step {step_id} has an ambiguous projection target"),
            )?;
        let body_start = header_end + 1;
        let body_end = tactic_body_end(lines, header_end);
        if !is_projection_body(
            &lines[body_start..body_end],
            &lines[cursor..header_end + 1],
            target_step,
        ) {
            return Err(format!(
                "global CNF step {step_id} has an ambiguous projection target step {target_step}"
            ));
        }
        targets.push(Target {
            step_id: target_step,
            body_start,
            body_end,
        });
        cursor = body_end;
    }
    if targets.is_empty() {
        return Err(format!(
            "global CNF step {step_id} has no exact projection targets"
        ));
    }
    let mut seen: Vec<u64> = targets.iter().map(|target| target.step_id).collect();
    let target_count = seen.len();
    seen.sort_unstable();
    seen.dedup();
    if seen.len() != target_count {
        return Err(format!(
            "global CNF step {step_id} repeats a projection target"
        ));
    }

    let suffix = code_lines[start + 6..].join("\n");
    for clause_name in &clause_names {
        if contains_word(&suffix, clause_name) {
            return Err(format!(
                "global CNF step {step_id} uses {clause_name} outside its projection block"
            ));
        }
    }
    if contains_primed_step(&suffix, step_id) {
        return Err(format!(
            "global CNF step {step_id} reuses its primed normalization result"
        ));
    }
    Ok(Some(Block {
        step_id,
        core_start: start,
        core_end: start + 6,
        targets,
    }))
}

/// Validate and recover the tactic groups of an already-rewritten proof.
///
/// Every executable `vampire_project` token must sit inside one exact
/// generated projection body, and the calls using one source step must be
/// contiguous. A dependency-sliced prenex block ([`super::prenex`]) proves
/// its slice by the same tactic, so its own call line is the one other
/// recognized call site; the slice is parsed whole, so an edited one is a
/// refusal rather than a stray call.
fn existing_projection_groups(source: &str) -> Result<Vec<(u64, Vec<u64>)>, String> {
    let lines = split_lines(source);
    let masked = code_without_comments_or_strings(source)?;
    let code_lines = split_lines(&masked);
    let comment_lines = super::prenex::line_comment_lines(source);
    let mut records: Vec<(usize, usize, u64, u64)> = Vec::new();
    let mut recognized_calls: Vec<usize> = Vec::new();

    for start in 0..lines.len() {
        if super::prenex::parse_generated_slice(&lines, &code_lines, start, &comment_lines)?
            .is_some()
        {
            recognized_calls.push(start + super::prenex::SLICE_PROJECT_CALL_OFFSET);
        }
    }

    for start in 0..lines.len() {
        if match_target_header(code_lines[start]).is_none() {
            continue;
        }
        let (target_step, header_end) =
            match parse_target_header(&lines, &code_lines, start, None, false)? {
                Some(parsed) => parsed,
                None => continue,
            };
        let body_start = header_end + 1;
        let body_end = tactic_body_end(&lines, header_end);
        let body_code = code_lines[body_start..body_end].join("\n");
        if !contains_project_token(&body_code) {
            continue;
        }
        if body_end != body_start + 1 {
            return Err(format!(
                "altered vampire_project body at step {target_step}"
            ));
        }
        let source_step = match match_project_call(lines[body_start]) {
            Some(step) if lines[body_start] == code_lines[body_start] => step,
            _ => {
                return Err(format!(
                    "unrecognized vampire_project call at step {target_step}"
                ));
            }
        };
        records.push((start, body_end, source_step, target_step));
        recognized_calls.push(body_start);
    }

    for (line_number, line) in code_lines.iter().enumerate() {
        if contains_project_token(line) && !recognized_calls.contains(&line_number) {
            return Err(
                "executable vampire_project outside an exact generated projection body".to_string(),
            );
        }
    }

    let mut groups: Vec<(u64, Vec<u64>)> = Vec::new();
    let mut prior_end: Option<usize> = None;
    let mut seen_sources: Vec<u64> = Vec::new();
    let mut seen_targets: Vec<u64> = Vec::new();
    for (header_start, body_end, source_step, target_step) in records {
        if seen_targets.contains(&target_step) {
            return Err(format!("repeats projected target step {target_step}"));
        }
        seen_targets.push(target_step);
        let adjacent = prior_end
            .is_some_and(|end| lines[end..header_start].iter().all(|line| line.is_empty()));
        let extends = adjacent
            && groups
                .last()
                .is_some_and(|(group_source, _)| *group_source == source_step);
        if extends {
            groups
                .last_mut()
                .expect("a group exists whenever one is extended")
                .1
                .push(target_step);
        } else {
            if seen_sources.contains(&source_step) {
                return Err(format!(
                    "noncontiguous vampire_project calls using step{source_step}"
                ));
            }
            seen_sources.push(source_step);
            groups.push((source_step, vec![target_step]));
        }
        prior_end = Some(body_end);
    }
    Ok(groups)
}

// ------------------------------------------------------------
// Rewrite
// ------------------------------------------------------------

/// Replace every exact global prenex/CNF package by targeted projections.
///
/// The input must already be canonical (see [`super::canonical`]).
pub(super) fn rewrite_projection_blocks(source: &str) -> Result<ProjectionSummary, String> {
    let lines = split_lines(source);
    let masked = code_without_comments_or_strings(source)?;
    let code_lines = split_lines(&masked);

    let mut blocks: Vec<Block> = Vec::new();
    for line_number in 0..lines.len() {
        if match_global_header(code_lines[line_number]).is_none() {
            continue;
        }
        if let Some(block) = parse_projection_block(&lines, &code_lines, line_number)? {
            blocks.push(block);
        }
    }
    let mut block_steps: Vec<u64> = blocks.iter().map(|block| block.step_id).collect();
    let block_count = block_steps.len();
    block_steps.sort_unstable();
    block_steps.dedup();
    if block_steps.len() != block_count {
        return Err("repeats an exact global CNF step".to_string());
    }

    let mut occupied: Vec<(usize, usize)> = Vec::new();
    let mut target_steps: Vec<u64> = Vec::new();
    let mut edits: Vec<(usize, usize, Vec<String>)> = Vec::new();
    for block in &blocks {
        let block_end = block
            .targets
            .last()
            .expect("a recognized block has at least one target")
            .body_end;
        occupied.push((block.core_start, block_end));
        edits.push((block.core_start, block.core_end, Vec::new()));
        for target in &block.targets {
            if target_steps.contains(&target.step_id) {
                return Err(format!("repeats projected target step {}", target.step_id));
            }
            target_steps.push(target.step_id);
            edits.push((
                target.body_start,
                target.body_end,
                vec![format!("{PROJECT_CALL_PREFIX}{}", block.step_id)],
            ));
        }
    }
    occupied.sort_unstable();
    for pair in occupied.windows(2) {
        if pair[0].1 > pair[1].0 {
            return Err("has overlapping global CNF blocks".to_string());
        }
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

    let groups = existing_projection_groups(&rewritten)?;
    for block in &blocks {
        let expected: Vec<u64> = block.targets.iter().map(|target| target.step_id).collect();
        let found = groups
            .iter()
            .find(|(source_step, _)| *source_step == block.step_id)
            .map(|(_, targets)| targets.as_slice());
        if found != Some(expected.as_slice()) {
            return Err(format!(
                "global CNF step {} was only partially transformed",
                block.step_id
            ));
        }
    }

    let rewritten_masked = code_without_comments_or_strings(&rewritten)?;
    let mut missed: Vec<u64> = Vec::new();
    for line in split_lines(&rewritten_masked) {
        if let Some(step_id) = match_global_prenex(line).or_else(|| match_global_cnf(line))
            && !missed.contains(&step_id)
        {
            missed.push(step_id);
        }
    }
    if missed
        .iter()
        .any(|step| blocks.iter().any(|block| block.step_id == *step))
    {
        return Err("retained part of a rewritten global CNF step".to_string());
    }

    Ok(ProjectionSummary {
        source: rewritten,
        step_ids: groups.iter().map(|(source_step, _)| *source_step).collect(),
        projected_step_ids: groups.into_iter().map(|(_, targets)| targets).collect(),
        missed_step_ids: missed,
    })
}
