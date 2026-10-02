//! The solver-facing name of one symbol, computed from its wire key.
//!
//! Lean owns the naming convention: `Whiel/Vampire/SolverName.lean` gives each
//! carrier a name function, and `Whiel/Vampire/SolverName/Concrete.lean` fixes
//! it for the two production carriers. This module recomputes exactly that
//! function from the wire key, because the multi-worker name-environment
//! replay needs a name synchronously and locally, before any worker has been
//! asked. Lean stays the authority: the fixed-ambient worker refuses a binding
//! whose name is not its own name for that symbol.
//!
//! The function is total on the key grammars and injective on each of them,
//! so no sanitizing and no collision suffix is involved. A key that does not
//! parse yields an error rather than an invented name.

use std::fmt;

// ------------------------------------------------------------
// Failure
// ------------------------------------------------------------

/// One wire key no solver name can be computed from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolverNameError {
    key: String,
    reason: &'static str,
}

impl SolverNameError {
    fn new(key: &str, reason: &'static str) -> Self {
        Self {
            key: key.to_string(),
            reason,
        }
    }

    /// The key that could not be named.
    pub fn key(&self) -> &str {
        &self.key
    }
}

impl fmt::Display for SolverNameError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "no solver name for the key {key:?}: {reason}",
            key = self.key,
            reason = self.reason
        )
    }
}

impl std::error::Error for SolverNameError {}

// ------------------------------------------------------------
// The Identifier Escape
// ------------------------------------------------------------

/// Escape one arbitrary string into the TPTP identifier alphabet.
///
/// A lowercase ASCII letter or digit stands for itself; every other character
/// becomes `_` and exactly six lowercase hexadecimal digits of its code point.
/// This mirrors `Whiel.Vampire.SolverName.Escape.escape`, whose round-trip
/// theorem is what makes the encoding injective.
pub(crate) fn escape(text: &str) -> String {
    let mut escaped = String::with_capacity(text.len());
    for character in text.chars() {
        if character.is_ascii_lowercase() || character.is_ascii_digit() {
            escaped.push(character);
        } else {
            escaped.push('_');
            escaped.push_str(&format!("{code:06x}", code = character as u32));
        }
    }
    escaped
}

// ------------------------------------------------------------
// Relation Names
// ------------------------------------------------------------

/// The solver name of one relation, from its wire key.
///
/// A fixed-ambient key `‹copy›:‹family›:‹index›:‹payload›` names the relation
/// by its clause source `‹copy›‹family›_‹index›z‹payload›`, the spelling
/// agents already read and write. A one-shot manifest key `rel:‹base›:‹index›`
/// belongs to a carrier with no clause source, and is named `r`, the decimal
/// index, `z`, and the base — the same layout with the copy and family tags
/// that carrier does not have replaced by the single tag `r`.
pub(crate) fn relation_solver_name(key: &str) -> Result<String, SolverNameError> {
    match key.strip_prefix("rel:") {
        Some(rest) => index_alpha_relation_name(key, rest),
        None => fixed_ambient_relation_name(key),
    }
}

fn fixed_ambient_relation_name(key: &str) -> Result<String, SolverNameError> {
    let fields = key.split(':').collect::<Vec<_>>();
    let [copy, family, index, payload] = fields.as_slice() else {
        return Err(SolverNameError::new(
            key,
            "a fixed-ambient relation key has four colon-separated fields",
        ));
    };
    if *copy != "o" && *copy != "y" {
        return Err(SolverNameError::new(
            key,
            "the copy tag must be ordinary or prophecy",
        ));
    }
    if !index.chars().all(|character| character == 's') {
        return Err(SolverNameError::new(
            key,
            "the relation index must be a unary run",
        ));
    }
    let payload_is_valid = match *family {
        "p" | "a" => payload
            .chars()
            .all(|character| character.is_ascii_alphabetic()),
        "f" => is_canonical_nat(payload),
        _ => {
            return Err(SolverNameError::new(key, "unknown relation-family tag"));
        }
    };
    if !payload_is_valid {
        return Err(SolverNameError::new(
            key,
            "the relation payload is neither an alphabetic base nor a flag identity",
        ));
    }
    Ok(format!("{copy}{family}_{index}z{payload}"))
}

fn index_alpha_relation_name(key: &str, rest: &str) -> Result<String, SolverNameError> {
    let Some((base, index)) = rest.rsplit_once(':') else {
        return Err(SolverNameError::new(
            key,
            "a one-shot manifest relation key carries an index",
        ));
    };
    if base.is_empty()
        || !base
            .chars()
            .all(|character| character.is_ascii_alphabetic())
    {
        return Err(SolverNameError::new(
            key,
            "the relation base must be alphabetic",
        ));
    }
    if !is_canonical_nat(index) {
        return Err(SolverNameError::new(
            key,
            "the relation index must be a canonical decimal",
        ));
    }
    Ok(format!("r_{index}z{base}"))
}

// ------------------------------------------------------------
// Constant Names
// ------------------------------------------------------------

/// The solver name of one concrete domain value, from its wire key.
///
/// `k`, a kind letter, and an injective encoding of the value: decimal for a
/// number, one letter for a Boolean, and the escape for an arbitrary string.
pub(crate) fn constant_solver_name(key: &str) -> Result<String, SolverNameError> {
    if let Some(number) = key.strip_prefix("num:") {
        if !is_canonical_nat(number) {
            return Err(SolverNameError::new(
                key,
                "a numeric constant carries a canonical decimal",
            ));
        }
        return Ok(format!("kn{number}"));
    }
    if let Some(text) = key.strip_prefix("str:") {
        return Ok(format!("ks{escaped}", escaped = escape(text)));
    }
    match key {
        "bool:0" => Ok("kbf".to_string()),
        "bool:1" => Ok("kbt".to_string()),
        _ => Err(SolverNameError::new(key, "unknown constant kind")),
    }
}

// ------------------------------------------------------------
// Shared Checks
// ------------------------------------------------------------

fn is_canonical_nat(value: &str) -> bool {
    !value.is_empty()
        && value.chars().all(|character| character.is_ascii_digit())
        && (value.len() == 1 || !value.starts_with('0'))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The relation spellings pinned in `Whiel/Synthesis/Tests/SolverName.lean`.
    #[test]
    fn relation_names_match_the_pinned_lean_spellings() {
        assert_eq!(relation_solver_name("o:p::E").unwrap(), "op_zE");
        assert_eq!(relation_solver_name("o:a::S").unwrap(), "oa_zS");
        assert_eq!(relation_solver_name("y:p::T").unwrap(), "yp_zT");
        assert_eq!(relation_solver_name("o:f::3").unwrap(), "of_z3");
        assert_eq!(relation_solver_name("y:a:ss:T").unwrap(), "ya_sszT");
    }

    /// The constant spellings pinned in the same Lean file.
    #[test]
    fn constant_names_match_the_pinned_lean_spellings() {
        assert_eq!(constant_solver_name("num:42").unwrap(), "kn42");
        assert_eq!(constant_solver_name("bool:0").unwrap(), "kbf");
        assert_eq!(constant_solver_name("bool:1").unwrap(), "kbt");
        assert_eq!(constant_solver_name("str:root").unwrap(), "ksroot");
        assert_eq!(constant_solver_name("str:Root").unwrap(), "ks_000052oot");
        assert_eq!(constant_solver_name("str:a_b").unwrap(), "ksa_00005fb");
        assert_eq!(constant_solver_name("str:a b").unwrap(), "ksa_000020b");
        assert_eq!(constant_solver_name("str:é").unwrap(), "ks_0000e9");
        assert_eq!(constant_solver_name("str:").unwrap(), "ks");
    }

    /// The synthesized finite-carrier keys are ordinary string constants.
    #[test]
    fn a_synthesized_carrier_key_names_through_the_escape() {
        assert_eq!(
            constant_solver_name("str:__whiel_fmb_fresh_0").unwrap(),
            "ks_00005f_00005fwhiel_00005ffmb_00005ffresh_00005f0"
        );
    }

    /// Relation, constant and one-shot names never meet.
    #[test]
    fn the_three_name_families_start_with_different_letters() {
        assert!(relation_solver_name("o:p::E").unwrap().starts_with('o'));
        assert!(relation_solver_name("y:p::E").unwrap().starts_with('y'));
        assert!(relation_solver_name("rel:E:0").unwrap().starts_with('r'));
        assert!(constant_solver_name("str:E").unwrap().starts_with('k'));
    }

    #[test]
    fn one_shot_manifest_relations_keep_the_base_and_index_apart() {
        assert_eq!(relation_solver_name("rel:E:0").unwrap(), "r_0zE");
        assert_eq!(relation_solver_name("rel:e:0").unwrap(), "r_0ze");
        assert_eq!(relation_solver_name("rel:TBound:0").unwrap(), "r_0zTBound");
        assert_eq!(relation_solver_name("rel:T:12").unwrap(), "r_12zT");
    }

    /// The old sanitizing collision is gone: case is carried, not folded.
    #[test]
    fn keys_differing_only_in_case_or_punctuation_get_different_names() {
        assert_ne!(
            relation_solver_name("rel:E:0").unwrap(),
            relation_solver_name("rel:e:0").unwrap()
        );
        assert_ne!(
            constant_solver_name("str:a-b").unwrap(),
            constant_solver_name("str:a_b").unwrap()
        );
    }

    #[test]
    fn an_unparsable_key_is_an_error_rather_than_a_fallback_name() {
        for key in [
            "",
            "o:p::E:extra",
            "z:p::E",
            "o:q::E",
            "o:p:x:E",
            "o:p::E1",
            "o:f::03",
            "rel:E",
            "rel::0",
            "rel:E:00",
        ] {
            assert!(
                relation_solver_name(key).is_err(),
                "the relation key {key:?} must not be named"
            );
        }
        for key in ["", "num:", "num:007", "bool:2", "data:1"] {
            assert!(
                constant_solver_name(key).is_err(),
                "the constant key {key:?} must not be named"
            );
        }
    }

    /// Every name the two grammars produce is a legal TPTP `lower_word`.
    #[test]
    fn every_produced_name_is_a_legal_lower_word() {
        let names = [
            relation_solver_name("o:p::E").unwrap(),
            relation_solver_name("y:a:ss:T").unwrap(),
            relation_solver_name("o:f::3").unwrap(),
            relation_solver_name("rel:TBound:0").unwrap(),
            constant_solver_name("num:42").unwrap(),
            constant_solver_name("str:Root a_b é").unwrap(),
            constant_solver_name("bool:1").unwrap(),
        ];
        for name in names {
            let mut characters = name.chars();
            let first = characters.next().expect("a name is nonempty");
            assert!(first.is_ascii_lowercase(), "{name:?} starts lowercase");
            assert!(
                characters.all(|character| character.is_ascii_alphanumeric() || character == '_'),
                "{name:?} is an identifier"
            );
        }
    }
}
