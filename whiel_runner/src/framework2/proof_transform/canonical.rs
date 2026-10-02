//! Canonical form of one raw leancheck stdout.
//!
//! This is the port of the legacy `canonicalize_leancheck_proof` and its
//! two helpers (`_strip_vamplean_resource_options`,
//! `validate_leancheck_hygiene`). It is the first step of the pipeline and
//! the only one every proof goes through, so it is where determinism and
//! fail-closed hygiene are established for the rest:
//!
//! * line endings and trailing whitespace are normalized, so a pinned
//!   emitter shape is recognized (or refused) on its bytes alone;
//! * the module shape is *checked*, not assumed — exactly one VampLean
//!   import, one `fullProof`, one `section vamproof`/`end vamproof`;
//! * the four volatile solver comment lines (wall clock, peak memory, the
//!   two progress lines) are dropped, so that nothing which changes
//!   between two runs of the same problem reaches a published file; the
//!   measurements they carried are read out first by
//!   [`solver_measurements`] and recorded in the receipt and in the
//!   certificate's `timing.csv` instead;
//! * the two `linter.unused*` options Vampire writes for its own benefit
//!   are dropped;
//! * Vampire's proof-section resource prelude (`maxHeartbeats 0`,
//!   `maxRecDepth 100000000` — "no limit at all") is replaced by the
//!   certificate-wide policy, so a published module cannot spin forever on
//!   a machine that is merely slow;
//! * a proof carrying a hole (`sorry`, `axiom`, …) or any `#` command is
//!   refused *before* anything compiles it.
//!
//! The `variable` telescope order is deliberately left exactly as Vampire
//! wrote it. The legacy code sorted binder names inside equal-type groups;
//! that order is real Lean, consumed by the per-job reconstruction
//! modules, and reordering it here would put an untrusted rewrite in front
//! of a statement the certificate depends on, for nothing but a digest.
//! Revalidation absorbs the volatility instead, by comparing two trees
//! through [`normalize_telescope_order`].

use super::projection::{code_without_comments_or_strings, scan_source_lexical_layout};

/// The only imports a raw leancheck proof may carry.
const PERMITTED_IMPORTS: [&str; 2] = ["import VampLean", "import VampLean.Runtime"];

/// The comment lines whose content changes between two runs of the same
/// problem. They are dropped from every file this pipeline writes — the
/// staged per-job evidence (`leancheck.lean`, kept only until it is moved
/// to a caller-supplied evidence directory or dropped, never published
/// with the tree) and the packaged module alike — and what they measured
/// is recorded in the build receipt and in the certificate's own
/// `timing.csv`, which is published at the tree's root.
///
/// `scripts/check_leancheck_emitter.py` is the single authority for this
/// list; its `VOLATILE_PREFIXES` and this constant are pinned equal by
/// `tests::the_volatile_prefixes_match_the_emitter_check`.
pub const VOLATILE_LINE_PREFIXES: [&str; 4] = [
    "-- Time elapsed:",
    "-- Peak memory usage:",
    "-- Success in time",
    "--  found proof, printing to",
];

/// Options Vampire sets for its own emitter's benefit and which say
/// nothing about the proof. Dropped verbatim, as the legacy
/// `_REMOVED_RAW_LINES` did; `set_option linter.all false` stays and
/// already covers them.
const REMOVED_RAW_LINES: [&str; 2] = [
    "set_option linter.unusedTactic false",
    "set_option linter.unusedSimpArgs false",
];

/// Vampire's own proof-section resource prelude: no heartbeat limit and a
/// recursion depth no machine reaches. Exactly these two spellings, in
/// exactly this order, between `section vamproof` and the first
/// declaration.
const VAMPIRE_RESOURCE_PRELUDE: [&str; 2] = [
    "set_option maxHeartbeats 0",
    "set_option maxRecDepth 100000000",
];

/// The certificate-wide resource policy that replaces it: generous, but
/// finite, so a published module fails rather than hangs.
pub const CERTIFICATE_RESOURCE_POLICY: [&str; 2] = [
    "set_option maxHeartbeats 400000000",
    "set_option maxRecDepth 1048576",
];

/// The one further resource option the pinned emitter writes: the
/// term-level `set_option … in` that guards each AVATAR Boolean helper
/// under the `casc_2025` profile. It is left exactly as emitted — the
/// kernel-LRAT step later in the same pipeline deletes the helper block it
/// belongs to — but it is *pinned* here, so that any other resource option
/// refuses the job instead of being published unread.
///
/// The legacy code refused this line outright, because it stripped the
/// prelude only after transformation 2 had already removed the AVATAR
/// blocks. This pipeline canonicalizes first, so the pinned spelling is
/// admitted here and removed there.
const AVATAR_HELPER_RESOURCE_OPTION: &str = "set_option maxHeartbeats 200000000 in";

/// Tokens that either open a proof hole or mutate the elaborator's
/// environment. The legacy `_BANNED_LEAN_PROOF_TOKENS`, verbatim.
const BANNED_PROOF_TOKENS: [&str; 13] = [
    "admit",
    "axiom",
    "builtin_initialize",
    "constant",
    "elab",
    "initialize",
    "macro",
    "opaque",
    "partial",
    "run_tac",
    "sorry",
    "syntax",
    "unsafe",
];

/// What the volatile lines measured, read out of one raw stdout before
/// they are dropped.
///
/// Both fields are optional: a profile or a Vampire build that does not
/// print one of them is not an error, it simply leaves that column of
/// `timing.csv` empty.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct SolverMeasurements {
    /// Vampire's own reported wall clock, in seconds.
    pub vampire_elapsed_seconds: Option<f64>,
    /// Vampire's own reported peak resident size, in megabytes.
    pub vampire_peak_memory_mb: Option<f64>,
}

/// Read the measurements the volatile comment lines carry.
///
/// Called on the *raw* stdout, before [`canonicalize`] drops those lines.
/// A line whose value does not parse is ignored rather than fatal: this is
/// evidence about a run, not a fact the certificate rests on.
pub fn solver_measurements(raw: &str) -> SolverMeasurements {
    let mut measurements = SolverMeasurements::default();
    let Ok(original_lexical) = scan_source_lexical_layout(raw) else {
        return measurements;
    };
    if original_lexical.multiline_string || original_lexical.unsupported_literal {
        return measurements;
    }
    let normalized = raw.replace("\r\n", "\n").replace('\r', "\n");
    let Ok(lexical) = scan_source_lexical_layout(&normalized) else {
        return measurements;
    };
    for (index, line) in normalized.split('\n').enumerate() {
        if !lexical.line_comments.contains(&index) {
            continue;
        }
        let line = line.trim_end_matches(char::is_whitespace);
        if let Some(rest) = line.strip_prefix("-- Time elapsed:") {
            measurements.vampire_elapsed_seconds = parse_leading_number(rest);
        } else if let Some(rest) = line.strip_prefix("-- Peak memory usage:") {
            measurements.vampire_peak_memory_mb = parse_leading_number(rest);
        }
    }
    measurements
}

/// The first whitespace-delimited token of `rest`, as a number.
fn parse_leading_number(rest: &str) -> Option<f64> {
    rest.split_whitespace().next()?.parse::<f64>().ok()
}

/// Normalize the raw stdout and check the module shape the rest of the
/// pipeline relies on.
///
/// Fails closed on anything that is not exactly one VampLean proof
/// module: a foreign or missing import, more than one import, a missing or
/// repeated `fullProof`, a section that does not open and close exactly
/// once, a resource option outside the two pinned shapes, a banned token,
/// or a `#` command.
pub(super) fn canonicalize(source: &str) -> Result<String, String> {
    // Physical line breaks and trailing spaces inside a multiline
    // literal are data. The pinned emitter never writes such a literal,
    // so refuse it before line-ending or whitespace normalization can
    // silently change a theorem statement.
    let original_lexical = scan_source_lexical_layout(source)?;
    if original_lexical.multiline_string {
        return Err("raw proof carries an unsupported multiline string literal".to_string());
    }
    if original_lexical.unsupported_literal {
        return Err("raw proof carries an unsupported quoted identifier".to_string());
    }
    let normalized = source.replace("\r\n", "\n").replace('\r', "\n");
    let lines: Vec<&str> = normalized
        .split('\n')
        .map(|line| line.trim_end_matches(char::is_whitespace))
        .collect();
    let lexical = scan_source_lexical_layout(&lines.join("\n"))?;
    let code_lines: Vec<&str> = lexical.code.split('\n').collect();

    let imports: Vec<&str> = lines
        .iter()
        .copied()
        .filter(|line| is_import_line(line))
        .collect();
    if imports.len() != 1 {
        return Err(format!(
            "raw proof must carry exactly one import, found {}",
            imports.len()
        ));
    }
    if !PERMITTED_IMPORTS.contains(&imports[0]) {
        return Err(format!(
            "raw proof carries a foreign import `{}`",
            imports[0]
        ));
    }

    let retained: Vec<&str> = lines
        .into_iter()
        .enumerate()
        .filter(|(index, line)| {
            !(is_volatile_line(line) && lexical.line_comments.contains(index)
                || REMOVED_RAW_LINES.contains(line) && *line == code_lines[*index])
        })
        .map(|(_, line)| line)
        .collect();
    let rendered = format!(
        "{}\n",
        retained.join("\n").trim_matches(char::is_whitespace)
    );

    for (needle, label) in [
        ("theorem fullProof", "declare fullProof"),
        ("section vamproof", "open its section"),
        ("end vamproof", "close its section"),
    ] {
        let count = rendered.matches(needle).count();
        if count != 1 {
            return Err(format!(
                "raw proof must {label} exactly once, found {count} occurrences of `{needle}`"
            ));
        }
    }

    let rendered = apply_certificate_resource_policy(&rendered)?;
    validate_hygiene(&rendered)?;
    Ok(rendered)
}

/// Whether one already-trimmed line is one of the volatile solver
/// comments.
fn is_volatile_line(line: &str) -> bool {
    VOLATILE_LINE_PREFIXES
        .iter()
        .any(|prefix| line.starts_with(prefix))
}

/// Whether one already-trimmed line is an `import` command, matching the
/// legacy `^\s*import\s+` recognizer.
fn is_import_line(line: &str) -> bool {
    let rest = match line
        .trim_start_matches(char::is_whitespace)
        .strip_prefix("import")
    {
        Some(rest) => rest,
        None => return false,
    };
    rest.starts_with(char::is_whitespace)
}

// ------------------------------------------------------------
// Resource Policy
// ------------------------------------------------------------

/// Replace Vampire's proof-section resource prelude by the
/// certificate-wide policy, checking the exact shape the legacy
/// `_strip_vamplean_resource_options` pinned before it touches anything.
///
/// The prelude must be the two exact spellings, once each, uncommented and
/// unquoted, in order, between the single `section vamproof` and the first
/// declaration. Every other `maxHeartbeats`/`maxRecDepth` command must be
/// the pinned AVATAR helper guard, below that first declaration.
fn apply_certificate_resource_policy(source: &str) -> Result<String, String> {
    let lines: Vec<&str> = source.split('\n').collect();
    let masked = code_without_comments_or_strings(source)?;
    let code_lines: Vec<&str> = masked.split('\n').collect();
    if lines.len() != code_lines.len() {
        return Err("raw proof's comment mask does not preserve its line structure".to_string());
    }

    let resource_lines: Vec<usize> = code_lines
        .iter()
        .enumerate()
        .filter(|(_, line)| is_resource_option_command(line))
        .map(|(number, _)| number)
        .collect();
    if resource_lines.is_empty() {
        return Ok(source.to_string());
    }

    let mut prelude: [Option<usize>; 2] = [None, None];
    for number in resource_lines {
        // A line the mask changed carries a comment or a string, so its
        // raw text is not the command it looks like.
        let raw = lines[number];
        if raw != code_lines[number] {
            return Err(unexpected_resource_option(raw));
        }
        // Either spelling fills a slot: Vampire's, or the policy this
        // function itself writes, so that canonicalizing an already
        // canonical proof is the identity rather than a refusal.
        match (0..2).find(|slot| {
            raw == VAMPIRE_RESOURCE_PRELUDE[*slot] || raw == CERTIFICATE_RESOURCE_POLICY[*slot]
        }) {
            Some(slot) => {
                if prelude[slot].is_some() {
                    return Err(unexpected_resource_option(raw));
                }
                prelude[slot] = Some(number);
            }
            None if raw == AVATAR_HELPER_RESOURCE_OPTION => {}
            None => return Err(unexpected_resource_option(raw)),
        }
    }

    let (Some(heartbeats), Some(rec_depth)) = (prelude[0], prelude[1]) else {
        return Err(
            "raw proof does not carry Vampire's pinned proof-section resource prelude".to_string(),
        );
    };
    let section = code_lines
        .iter()
        .position(|line| *line == "section vamproof")
        .ok_or_else(|| "raw proof opens no `section vamproof`".to_string())?;
    let declaration = code_lines
        .iter()
        .position(|line| is_declaration_line(line))
        .ok_or_else(|| "raw proof carries no declaration".to_string())?;
    if !(section < heartbeats && heartbeats < rec_depth && rec_depth < declaration) {
        return Err(
            "raw proof's resource prelude is not between `section vamproof` and its \
                    first declaration"
                .to_string(),
        );
    }
    // Every AVATAR guard belongs to a helper, and every helper is a
    // declaration, so a guard above the first declaration is a prelude
    // option in disguise.
    if code_lines
        .iter()
        .take(declaration)
        .any(|line| *line == AVATAR_HELPER_RESOURCE_OPTION)
    {
        return Err(unexpected_resource_option(AVATAR_HELPER_RESOURCE_OPTION));
    }

    let mut rewritten = lines;
    rewritten[heartbeats] = CERTIFICATE_RESOURCE_POLICY[0];
    rewritten[rec_depth] = CERTIFICATE_RESOURCE_POLICY[1];
    Ok(rewritten.join("\n"))
}

fn unexpected_resource_option(line: &str) -> String {
    format!("raw proof carries an unexpected resource option `{line}`")
}

/// The legacy `^\s*set_option\s+(?:maxHeartbeats|maxRecDepth)\b`.
fn is_resource_option_command(line: &str) -> bool {
    let rest = match line
        .trim_start_matches(char::is_whitespace)
        .strip_prefix("set_option")
    {
        Some(rest) if rest.starts_with(char::is_whitespace) => {
            rest.trim_start_matches(char::is_whitespace)
        }
        _ => return false,
    };
    ["maxHeartbeats", "maxRecDepth"].iter().any(|option| {
        rest.strip_prefix(*option)
            .is_some_and(|tail| !tail.starts_with(is_word_char))
    })
}

/// The legacy `^(?:def|example|lemma|structure|theorem|variable)\b`.
fn is_declaration_line(line: &str) -> bool {
    [
        "def",
        "example",
        "lemma",
        "structure",
        "theorem",
        "variable",
    ]
    .iter()
    .any(|keyword| {
        line.strip_prefix(*keyword)
            .is_some_and(|tail| !tail.starts_with(is_word_char))
    })
}

// ------------------------------------------------------------
// Hygiene
// ------------------------------------------------------------

/// Refuse a proof that opens a hole or mutates the environment, before
/// anything compiles it.
///
/// The check reads the text with comments and string literals masked out,
/// so a `sorry` in a comment is prose and a `sorry` in the proof is a
/// refusal. It is a *containment* check, not a proof of soundness: the
/// certificate's own exact-std3 audit is what finally decides. This runs
/// first so that a hole is named where it is, rather than surfacing as a
/// stray axiom in an audit of the whole tree.
fn validate_hygiene(source: &str) -> Result<(), String> {
    let masked = code_without_comments_or_strings(source)?;
    if let Some(token) = BANNED_PROOF_TOKENS
        .iter()
        .find(|token| contains_word(&masked, token))
    {
        return Err(format!(
            "raw proof contains the forbidden Lean token `{token}`"
        ));
    }
    // A command can follow a wrapper on the same line, such as
    // `set_option pp.universes true in #eval ...`. The pinned emitter
    // needs no executable hash syntax; reject it at any code position.
    if masked.contains('#') {
        return Err("raw proof contains a Lean command".to_string());
    }
    Ok(())
}

/// Whether `needle` occurs in `text` delimited by non-word characters, the
/// legacy `\b…\b`.
fn contains_word(text: &str, needle: &str) -> bool {
    let mut search_from = 0usize;
    while let Some(offset) = text[search_from..].find(needle) {
        let start = search_from + offset;
        let end = start + needle.len();
        let before = text[..start].chars().next_back().is_some_and(is_word_char);
        let after = text[end..].chars().next().is_some_and(is_word_char);
        if !before && !after {
            return true;
        }
        search_from = end;
    }
    false
}

fn is_word_char(character: char) -> bool {
    character.is_alphanumeric() || character == '_'
}

// ------------------------------------------------------------
// Telescope Order
// ------------------------------------------------------------

/// Sort the binder names inside every equal-type `variable` group, and the
/// groups inside every multi-line `variable` block.
///
/// This is the legacy `_canonicalize_named_binder_groups` and
/// `_canonicalize_variable_group_blocks`, and it is deliberately *not*
/// part of [`canonicalize`]: the published text keeps Vampire's own
/// telescope. Vampire's order within an equal-type group carries no
/// information — the names are collected from an unordered set — so two
/// runs of one problem can write it two ways. This function exists so that
/// a comparison of two certificate trees can ignore exactly that, and
/// nothing else.
pub fn normalize_telescope_order(source: &str) -> String {
    // Comparison must not erase a change to a theorem parameter, comment,
    // or string merely because it looks like a generated binder group.
    // An unrecognized lexical shape retains byte-for-byte comparison.
    let Ok(lexical) = scan_source_lexical_layout(source) else {
        return source.to_string();
    };
    if lexical.multiline_string || lexical.unsupported_literal {
        return source.to_string();
    }
    let lines: Vec<&str> = source.split('\n').collect();
    let code_lines: Vec<&str> = lexical.code.split('\n').collect();
    let mut output = Vec::with_capacity(lines.len());
    let mut index = 0usize;
    while index < lines.len() {
        let head = (lines[index] == code_lines[index])
            .then(|| lines[index].strip_prefix("variable "))
            .flatten()
            .and_then(normalize_binder_group_line);
        let Some(head) = head else {
            output.push(lines[index].to_string());
            index += 1;
            continue;
        };
        let mut groups = vec![head];
        let mut next = index + 1;
        while next < lines.len() && lines[next] == code_lines[next] {
            let Some(group) = lines[next]
                .strip_prefix("  ")
                .and_then(normalize_binder_group_line)
            else {
                break;
            };
            groups.push(group);
            next += 1;
        }
        groups.sort();
        output.push(format!("variable {}", groups[0]));
        for group in &groups[1..] {
            output.push(format!("  {group}"));
        }
        index = next;
    }
    output.join("\n")
}

/// One complete group in the pinned generated `variable` layout. A line
/// containing additional syntax is not a telescope line we can compare.
fn normalize_binder_group_line(line: &str) -> Option<String> {
    if !line.starts_with("{«") {
        return None;
    }
    let characters: Vec<char> = line.chars().collect();
    let (rendered, next) = parse_binder_group(&characters, 0)?;
    (next == characters.len()).then_some(rendered)
}

/// Parse one `{«a» «b» : T}` group starting at the `{` at `start`,
/// returning its canonical spelling and the index just past its `}`.
fn parse_binder_group(characters: &[char], start: usize) -> Option<(String, usize)> {
    let mut index = start + 1;
    let mut names: Vec<String> = Vec::new();
    loop {
        while characters.get(index).is_some_and(|c| c.is_whitespace()) {
            index += 1;
        }
        if characters.get(index).copied() != Some('«') {
            break;
        }
        let open = index;
        index += 1;
        while characters.get(index).is_some_and(|c| *c != '»') {
            index += 1;
        }
        characters.get(index)?;
        index += 1;
        names.push(characters[open..index].iter().collect());
    }
    if names.is_empty() || characters.get(index).copied() != Some(':') {
        return None;
    }
    index += 1;
    let type_start = index;
    while let Some(character) = characters.get(index) {
        match character {
            '}' => {
                let binder_type: String = characters[type_start..index].iter().collect();
                // The emitter's symbol types are first-order: zero or
                // more domain arguments, ending in the domain or Prop.
                // Other variable declarations may carry dependencies
                // whose order is significant, so leave them untouched.
                let mut tokens: Vec<&str> = binder_type.split_whitespace().collect();
                if !matches!(tokens.pop(), Some("ι" | "Prop"))
                    || !tokens.len().is_multiple_of(2)
                    || !tokens.chunks_exact(2).all(|pair| pair == ["ι", "→"])
                {
                    return None;
                }
                names.sort();
                return Some((
                    format!("{{{} : {}}}", names.join(" "), binder_type.trim()),
                    index + 1,
                ));
            }
            '{' | '\n' => return None,
            _ => index += 1,
        }
    }
    None
}
