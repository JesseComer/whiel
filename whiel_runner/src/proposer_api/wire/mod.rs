//! Provider-neutral process contract. The endpoint lives for one verifier input.
//!
//! Framing, directions and public lifecycle are specified in README.md. This
//! module owns no process, worker or Houdini state.

use serde::{Deserialize, Serialize};
use std::fmt;
use std::future::Future;
use std::io;
use std::pin::Pin;

use super::{ApiCapabilities, NegotiatedApi};
use crate::framework2::strict_json::decode_strict_json;

pub const WIRE_VERSION: u64 = 3;
pub const SOCKET_ENV: &str = "WHIEL_PROPOSER_SOCKET";
pub const TOKEN_ENV: &str = "WHIEL_PROPOSER_TOKEN";
pub const MAX_PACKET_BYTES: usize = 64 * 1024 * 1024;
pub const MAX_HEADER_BYTES: usize = 16 * 1024;
pub const MAX_CONTROL_HEADER_BYTES: usize = 1024;
pub const HEADER_PREFIX_BYTES: usize = 4;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    ToVerifier,
    ToProposer,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Frame {
    pub wire_version: u64,
    pub endpoint_token: String,
    pub sequence: u64,
    #[serde(deserialize_with = "required_nullable")]
    pub request_id: Option<u64>,
    pub operation: Operation,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Operation {
    Hello {
        capabilities: ApiCapabilities,
    },
    Ready {
        api: NegotiatedApi,
    },
    Request {
        observation_bytes: u32,
        response_example_bytes: u32,
        #[serde(deserialize_with = "required_nullable")]
        remaining_request_budget_ns: Option<String>,
    },
    Query {
        query_id: u64,
        name: String,
        args_bytes: u32,
    },
    QueryResult {
        query_id: u64,
        result_bytes: u32,
    },
    Submit {
        bytes: u32,
    },
    Submitted {},
    Rejected {
        code: TransportRejection,
    },
    Complete {
        outcome: RequestOutcome,
    },
    RequestClosed {},
    Cancel {
        reason: CancellationReason,
    },
    Shutdown {
        reason: ShutdownReason,
    },
    Closed {},
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TransportRejection {
    TooLarge,
    DuplicateSubmission,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RequestOutcome {
    Response,
    SourceExhausted,
    NoResponse,
    Failure,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CancellationReason {
    Deadline,
    Cancelled,
    Failure,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ShutdownReason {
    Complete,
    Cancelled,
    Failure,
}

/// Cleanup failure is operational, never a proposal or proof verdict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProposerCleanupError {
    Failed,
    TimedOut,
}

impl fmt::Display for ProposerCleanupError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Failed => "proposer cleanup failed",
            Self::TimedOut => "proposer cleanup timed out",
        })
    }
}

impl std::error::Error for ProposerCleanupError {}

pub type ProposerCleanupFuture<'a> =
    Pin<Box<dyn Future<Output = Result<(), ProposerCleanupError>> + Send + 'a>>;

fn required_nullable<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: serde::Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

pub fn valid_endpoint_token(token: &str) -> bool {
    token.len() == 64
        && token
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

pub fn next_sequence(sequence: u64) -> io::Result<u64> {
    sequence
        .checked_add(1)
        .ok_or_else(|| invalid("proposer sequence exhausted"))
}

/// Decode the length prefix before allocating a header buffer.
pub fn header_length(prefix: [u8; HEADER_PREFIX_BYTES]) -> io::Result<usize> {
    let length = u32::from_be_bytes(prefix) as usize;
    if length == 0 || length > MAX_HEADER_BYTES {
        return Err(invalid("proposer header exceeds its bound"));
    }
    Ok(length)
}

impl Operation {
    pub fn direction(&self) -> Direction {
        match self {
            Self::Hello { .. }
            | Self::Query { .. }
            | Self::Submit { .. }
            | Self::Complete { .. }
            | Self::Closed {} => Direction::ToVerifier,
            Self::Ready { .. }
            | Self::Request { .. }
            | Self::QueryResult { .. }
            | Self::Submitted {}
            | Self::Rejected { .. }
            | Self::RequestClosed {}
            | Self::Cancel { .. }
            | Self::Shutdown { .. } => Direction::ToProposer,
        }
    }

    pub fn is_endpoint_scoped(&self) -> bool {
        matches!(
            self,
            Self::Hello { .. } | Self::Ready { .. } | Self::Shutdown { .. } | Self::Closed {}
        )
    }

    pub fn is_control(&self) -> bool {
        matches!(
            self,
            Self::Submitted {}
                | Self::Rejected { .. }
                | Self::Complete { .. }
                | Self::RequestClosed {}
                | Self::Cancel { .. }
                | Self::Shutdown { .. }
                | Self::Closed {}
        )
    }

    pub fn attachment_lengths(&self) -> Vec<usize> {
        match self {
            Self::Request {
                observation_bytes,
                response_example_bytes,
                ..
            } => vec![
                *observation_bytes as usize,
                *response_example_bytes as usize,
            ],
            Self::Query { args_bytes, .. } => vec![*args_bytes as usize],
            Self::QueryResult { result_bytes, .. } => vec![*result_bytes as usize],
            Self::Submit { bytes } => vec![*bytes as usize],
            _ => Vec::new(),
        }
    }

    fn validate_fields(&self) -> io::Result<()> {
        match self {
            Self::Query { query_id, name, .. } => {
                if *query_id == 0
                    || name.is_empty()
                    || name.len() > 64
                    || !name.bytes().enumerate().all(|(index, byte)| {
                        byte.is_ascii_alphabetic()
                            || byte == b'_'
                            || (index > 0 && byte.is_ascii_digit())
                    })
                {
                    return Err(invalid("invalid proposer query identity"));
                }
            }
            Self::QueryResult { query_id: 0, .. } => {
                return Err(invalid("invalid proposer query identity"));
            }
            Self::Request {
                remaining_request_budget_ns: Some(value),
                ..
            } => {
                if value
                    .parse::<u64>()
                    .ok()
                    .is_none_or(|amount| amount.to_string() != *value)
                {
                    return Err(invalid("invalid proposer request budget"));
                }
            }
            _ => {}
        }
        Ok(())
    }
}

impl Frame {
    pub fn new(
        endpoint_token: String,
        sequence: u64,
        request_id: Option<u64>,
        operation: Operation,
    ) -> Self {
        Self {
            wire_version: WIRE_VERSION,
            endpoint_token,
            sequence,
            request_id,
            operation,
        }
    }

    pub fn validate(
        &self,
        endpoint_token: &str,
        sequence: u64,
        direction: Direction,
    ) -> io::Result<()> {
        if self.wire_version != WIRE_VERSION
            || !valid_endpoint_token(&self.endpoint_token)
            || self.endpoint_token != endpoint_token
            || self.sequence != sequence
            || self.operation.direction() != direction
            || self.operation.is_endpoint_scoped() != self.request_id.is_none()
            || self.request_id == Some(0)
        {
            return Err(invalid(
                "proposer version, identity, sequence or direction mismatch",
            ));
        }
        self.operation.validate_fields()
    }

    /// Validate the aggregate before the host allocates or reads attachments.
    pub fn packet_length(&self, encoded_header_bytes: usize) -> io::Result<usize> {
        let maximum = if self.operation.is_control() {
            MAX_CONTROL_HEADER_BYTES
        } else {
            MAX_HEADER_BYTES
        };
        if encoded_header_bytes == 0 || encoded_header_bytes > maximum {
            return Err(invalid("proposer header exceeds its bound"));
        }
        self.operation.attachment_lengths().into_iter().try_fold(
            HEADER_PREFIX_BYTES + encoded_header_bytes,
            |total, length| {
                total
                    .checked_add(length)
                    .filter(|bytes| *bytes <= MAX_PACKET_BYTES)
                    .ok_or_else(|| invalid("proposer aggregate packet exceeds its bound"))
            },
        )
    }

    pub fn encode_header(&self) -> io::Result<Vec<u8>> {
        self.validate(
            &self.endpoint_token,
            self.sequence,
            self.operation.direction(),
        )?;
        let bytes = crate::framing::bounded_json(self, MAX_HEADER_BYTES)?;
        self.packet_length(bytes.len())?;
        Ok(bytes)
    }

    /// Duplicate keys, unknown fields, invalid UTF-8 and wrong JSON types fail.
    /// Direction, endpoint identity and expected sequence are checked by the host.
    pub fn decode_header(bytes: &[u8]) -> io::Result<Self> {
        if bytes.is_empty() || bytes.len() > MAX_HEADER_BYTES {
            return Err(invalid("proposer header exceeds its bound"));
        }
        let value = decode_strict_json(bytes, Some(MAX_HEADER_BYTES))
            .map_err(|_| invalid("invalid proposer header JSON"))?;
        let frame: Self =
            serde_json::from_value(value).map_err(|_| invalid("invalid proposer header schema"))?;
        frame.validate(
            &frame.endpoint_token,
            frame.sequence,
            frame.operation.direction(),
        )?;
        frame.packet_length(bytes.len())?;
        Ok(frame)
    }
}

#[cfg(test)]
mod tests;
