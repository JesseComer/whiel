//! Strict bounded JSON decoding for untrusted agent content.

use std::collections::HashSet;
use std::fmt;

use serde::de::{self, DeserializeSeed, MapAccess, SeqAccess, Visitor};
use serde_json::Value;

const DUPLICATE_OBJECT_KEY_SENTINEL: &str = "whiel strict JSON duplicate object key";

/// Decode one complete JSON value without collapsing duplicate keys.
///
/// `maximum_bytes` is the run's optional `reply_bytes` host limit. `None` —
/// the default — decodes a value of any size.
pub(crate) fn decode_strict_json(
    bytes: &[u8],
    maximum_bytes: Option<usize>,
) -> Result<Value, StrictJsonError> {
    if maximum_bytes == Some(0) {
        return Err(StrictJsonError::InvalidLimit);
    }
    if bytes.is_empty() {
        return Err(StrictJsonError::Empty);
    }
    if maximum_bytes.is_some_and(|maximum| bytes.len() > maximum) {
        return Err(StrictJsonError::TooLarge {
            found: bytes.len(),
            limit: maximum_bytes.expect("the comparison ran under a set limit"),
        });
    }

    let mut deserializer = serde_json::Deserializer::from_slice(bytes);
    StrictJsonValueSeed
        .deserialize(&mut deserializer)
        .map_err(classify_decode_error)?;
    deserializer.end().map_err(|_| StrictJsonError::Malformed)?;
    serde_json::from_slice(bytes).map_err(|_| StrictJsonError::Malformed)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum StrictJsonError {
    InvalidLimit,
    Empty,
    TooLarge { found: usize, limit: usize },
    DuplicateObjectKey,
    Malformed,
}

impl fmt::Display for StrictJsonError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidLimit => formatter.write_str("strict JSON byte limit must be positive"),
            Self::Empty => formatter.write_str("strict JSON input is empty"),
            Self::TooLarge { found, limit } => write!(
                formatter,
                "strict JSON input has {found} bytes; maximum is {limit}",
            ),
            Self::DuplicateObjectKey => {
                formatter.write_str("strict JSON input repeats an object key")
            }
            Self::Malformed => formatter.write_str("strict JSON input is malformed"),
        }
    }
}

impl std::error::Error for StrictJsonError {}

fn classify_decode_error(error: serde_json::Error) -> StrictJsonError {
    if error.to_string().starts_with(DUPLICATE_OBJECT_KEY_SENTINEL) {
        StrictJsonError::DuplicateObjectKey
    } else {
        StrictJsonError::Malformed
    }
}

#[derive(Clone, Copy)]
struct StrictJsonValueSeed;

impl<'de> DeserializeSeed<'de> for StrictJsonValueSeed {
    type Value = ();

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(StrictJsonValueVisitor)
    }
}

struct StrictJsonValueVisitor;

impl<'de> Visitor<'de> for StrictJsonValueVisitor {
    type Value = ();

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("one JSON value")
    }

    fn visit_bool<E>(self, _value: bool) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_i64<E>(self, _value: i64) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_u64<E>(self, _value: u64) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_f64<E>(self, _value: f64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(())
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        let _ = value;
        Ok(())
    }

    fn visit_borrowed_str<E>(self, value: &'de str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        self.visit_str(value)
    }

    fn visit_string<E>(self, _value: String) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_none<E>(self) -> Result<Self::Value, E> {
        Ok(())
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        StrictJsonValueSeed.deserialize(deserializer)
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        while sequence.next_element_seed(StrictJsonValueSeed)?.is_some() {}
        Ok(())
    }

    fn visit_map<A>(self, mut object: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut keys = HashSet::with_capacity(object.size_hint().unwrap_or(0));
        while let Some(key) = object.next_key::<String>()? {
            if !keys.insert(key.clone()) {
                return Err(de::Error::custom(DUPLICATE_OBJECT_KEY_SENTINEL));
            }
            object.next_value_seed(StrictJsonValueSeed)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    const LIMIT: Option<usize> = Some(4096);

    #[test]
    fn accepts_one_exact_complete_value() {
        let bytes = br#"{
            "array": [null, true, false, -2, 3, 1.5, {"inner": "value"}],
            "escaped": "line\nvalue"
        }"#;
        assert_eq!(
            decode_strict_json(bytes, LIMIT).unwrap(),
            json!({
                "array": [null, true, false, -2, 3, 1.5, {"inner": "value"}],
                "escaped": "line\nvalue",
            })
        );
    }

    #[test]
    fn preserves_arbitrary_precision_numbers_after_duplicate_scan() {
        let bytes = br#"{"value":184467440737095516160000}"#;
        let decoded = decode_strict_json(bytes, LIMIT).unwrap();
        assert_eq!(
            decoded["value"].as_number().unwrap().to_string(),
            "184467440737095516160000"
        );
    }

    #[test]
    fn rejects_duplicate_root_key_without_echoing_it() {
        let error = decode_strict_json(br#"{"secret": 1, "secret": 2}"#, LIMIT).unwrap_err();
        assert_eq!(error, StrictJsonError::DuplicateObjectKey);
        assert!(!error.to_string().contains("secret"));
    }

    #[test]
    fn rejects_duplicate_nested_key() {
        let error = decode_strict_json(br#"{"outer": {"duplicate": 1, "duplicate": 2}}"#, LIMIT)
            .unwrap_err();
        assert_eq!(error, StrictJsonError::DuplicateObjectKey);
    }

    #[test]
    fn rejects_duplicate_key_inside_array_object() {
        let error = decode_strict_json(
            br#"[{"first": 1}, {"duplicate": 1, "duplicate": 2}]"#,
            LIMIT,
        )
        .unwrap_err();
        assert_eq!(error, StrictJsonError::DuplicateObjectKey);
    }

    #[test]
    fn rejects_malformed_and_trailing_content() {
        for bytes in [
            br#"{"missing": true"#.as_slice(),
            br#"{"valid": true} trailing"#.as_slice(),
            br#"{"first": true} {"second": true}"#.as_slice(),
            b"\xff".as_slice(),
        ] {
            assert_eq!(
                decode_strict_json(bytes, LIMIT),
                Err(StrictJsonError::Malformed)
            );
        }
    }

    #[test]
    fn enforces_the_exact_byte_limit() {
        assert_eq!(decode_strict_json(b"null", Some(4)), Ok(Value::Null));
        assert_eq!(
            decode_strict_json(b"null", Some(3)),
            Err(StrictJsonError::TooLarge { found: 4, limit: 3 })
        );
        assert_eq!(
            decode_strict_json(b"null", Some(0)),
            Err(StrictJsonError::InvalidLimit)
        );
        assert_eq!(decode_strict_json(b"", LIMIT), Err(StrictJsonError::Empty));
    }

    /// The default: no `reply_bytes` host limit, so no reply is too large.
    #[test]
    fn an_absent_limit_accepts_a_value_of_any_size() {
        let long = format!("[{}]", vec!["1"; 100_000].join(","));
        assert!(decode_strict_json(long.as_bytes(), None).is_ok());
        assert_eq!(decode_strict_json(b"", None), Err(StrictJsonError::Empty));
    }
}
