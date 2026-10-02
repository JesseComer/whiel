//! Optional capability negotiation. A declaration can only narrow B's policy.

use std::collections::BTreeSet;
use std::fmt;

use serde::{Deserialize, Serialize};

use super::API_VERSION;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ApiCapabilities {
    /// Highest supported API revision; compatible lower revisions are accepted.
    pub version: String,
    pub supported_operations: Vec<String>,
    pub required_operations: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NegotiatedApi {
    pub version: String,
    pub operations: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ApiNegotiationError(pub String);

impl fmt::Display for ApiNegotiationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for ApiNegotiationError {}

fn version(value: &str) -> Result<[u64; 3], ApiNegotiationError> {
    let parts = value
        .split('.')
        .map(|part| {
            part.parse::<u64>()
                .ok()
                .filter(|number| number.to_string() == part)
        })
        .collect::<Option<Vec<_>>>()
        .and_then(|parts| <[u64; 3]>::try_from(parts).ok());
    parts.ok_or_else(|| ApiNegotiationError("API version must be major.minor.patch".into()))
}

impl ApiCapabilities {
    pub fn current(supported_operations: impl IntoIterator<Item = String>) -> Self {
        Self {
            version: API_VERSION.into(),
            supported_operations: supported_operations.into_iter().collect(),
            required_operations: Vec::new(),
        }
    }

    pub fn negotiate(
        &self,
        permitted_operations: &[&str],
    ) -> Result<NegotiatedApi, ApiNegotiationError> {
        self.negotiate_with(API_VERSION, permitted_operations)
    }

    fn negotiate_with(
        &self,
        host_version: &str,
        permitted_operations: &[&str],
    ) -> Result<NegotiatedApi, ApiNegotiationError> {
        let client = version(&self.version)?;
        let host = version(host_version)?;
        if client[0] != host[0] {
            return Err(ApiNegotiationError(format!(
                "incompatible proposer API major: client {}, host {}",
                self.version, host_version
            )));
        }
        let supported: BTreeSet<_> = self
            .supported_operations
            .iter()
            .map(String::as_str)
            .collect();
        let required: BTreeSet<_> = self
            .required_operations
            .iter()
            .map(String::as_str)
            .collect();
        if supported.len() != self.supported_operations.len()
            || required.len() != self.required_operations.len()
            || supported.len() > 128
            || supported
                .iter()
                .any(|name| name.is_empty() || name.len() > 64)
        {
            return Err(ApiNegotiationError(
                "invalid or duplicate API capability names".into(),
            ));
        }
        for operation in required {
            if !supported.contains(operation) || !permitted_operations.contains(&operation) {
                return Err(ApiNegotiationError(format!(
                    "required API operation is unavailable or forbidden: {operation}"
                )));
            }
        }
        Ok(NegotiatedApi {
            version: if client <= host {
                &self.version
            } else {
                host_version
            }
            .into(),
            operations: permitted_operations
                .iter()
                .filter(|name| supported.contains(**name))
                .map(|name| (*name).into())
                .collect(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn older_client_never_sees_an_optional_addition() {
        let client = ApiCapabilities {
            version: "1.0.0".into(),
            supported_operations: vec!["history".into()],
            required_operations: Vec::new(),
        };
        let agreement = client
            .negotiate_with("1.1.0", &["history", "future_read"])
            .unwrap();
        assert_eq!(agreement.version, "1.0.0");
        assert_eq!(agreement.operations, ["history"]);
        assert!(client.negotiate_with("2.0.0", &["history"]).is_err());
    }

    /// The production Python client intentionally declares 3.0.0 while B's own
    /// constant moves ahead, so keep that compatibility covered on purpose
    /// rather than as a side effect of whichever revision a fixture advertises.
    #[test]
    fn lower_and_higher_client_revisions_negotiate_against_the_real_constant() {
        let host = version(API_VERSION).unwrap();
        assert!(
            ([3, 0, 0]..[3, 2, 9]).contains(&host),
            "update this test's client revisions for API_VERSION {API_VERSION}"
        );
        let mut client = ApiCapabilities {
            version: "3.0.0".into(),
            supported_operations: vec!["ledger".into(), "history".into()],
            required_operations: vec!["ledger".into()],
        };
        let agreement = client.negotiate(&["ledger", "countermodel"]).unwrap();
        assert_eq!(agreement.version, "3.0.0");
        assert_eq!(agreement.operations, ["ledger"]);

        client.version = "3.2.9".into();
        let agreement = client.negotiate(&["ledger", "countermodel"]).unwrap();
        assert_eq!(agreement.version, API_VERSION);
        assert_eq!(agreement.operations, ["ledger"]);

        client.version = "2.0.0".into();
        assert!(client.negotiate(&["ledger", "countermodel"]).is_err());
    }

    #[test]
    fn capabilities_cannot_grant_permission() {
        let mut client = ApiCapabilities::current(["history".into()]);
        assert!(client.negotiate(&[]).unwrap().operations.is_empty());
        client.required_operations.push("history".into());
        assert!(client.negotiate(&[]).is_err());
        client.version = "01.0.0".into();
        assert!(client.negotiate(&["history"]).is_err());
    }
}
