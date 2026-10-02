//! Bounded packet I/O and cumulative accounting for the public generic API.

use std::io;
use std::sync::{Arc, Mutex};

use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};

use crate::proposer_api::wire::{Direction, Frame, HEADER_PREFIX_BYTES, Operation, header_length};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ApiTrafficLimits {
    pub bytes: u64,
    pub messages: u64,
}

impl Default for ApiTrafficLimits {
    fn default() -> Self {
        Self {
            bytes: 1024 * 1024 * 1024,
            messages: 16_384,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ApiTrafficUsage {
    pub bytes: u64,
    pub messages: u64,
}

#[derive(Debug)]
struct BudgetState {
    limits: ApiTrafficLimits,
    usage: ApiTrafficUsage,
    reserved_bytes: u64,
    reserved_messages: u64,
    failure: Option<String>,
}

#[derive(Clone, Debug)]
pub(crate) struct Budget(Arc<Mutex<BudgetState>>);

impl Budget {
    pub(crate) fn new(limits: ApiTrafficLimits) -> Self {
        Self(Arc::new(Mutex::new(BudgetState {
            limits,
            usage: ApiTrafficUsage::default(),
            reserved_bytes: 0,
            reserved_messages: 0,
            failure: None,
        })))
    }

    pub(crate) fn usage(&self) -> ApiTrafficUsage {
        self.0.lock().unwrap_or_else(|p| p.into_inner()).usage
    }

    pub(crate) fn failure(&self) -> Option<String> {
        self.0
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .failure
            .clone()
    }

    fn reserve(&self, bytes: usize) -> io::Result<Reservation> {
        let mut state = self.0.lock().unwrap_or_else(|p| p.into_inner());
        if let Some(failure) = &state.failure {
            return Err(io::Error::other(failure.clone()));
        }
        let bytes = u64::try_from(bytes).map_err(io::Error::other)?;
        let fits_bytes = state
            .usage
            .bytes
            .checked_add(state.reserved_bytes)
            .and_then(|total| total.checked_add(bytes))
            .is_some_and(|total| total <= state.limits.bytes);
        let fits_messages = state
            .usage
            .messages
            .checked_add(state.reserved_messages)
            .and_then(|total| total.checked_add(1))
            .is_some_and(|total| total <= state.limits.messages);
        if !fits_bytes || !fits_messages {
            let failure = format!(
                "resource_exhausted: proposer API traffic allowance ({} bytes, {} messages)",
                state.limits.bytes, state.limits.messages
            );
            state.failure = Some(failure.clone());
            return Err(io::Error::other(failure));
        }
        state.reserved_bytes += bytes;
        state.reserved_messages += 1;
        Ok(Reservation {
            budget: self.clone(),
            remaining: bytes,
            message: true,
        })
    }

    // A bounded incoming header necessarily arrives before its attachment length
    // is known. Count those observed bytes even when reservation then fails.
    fn refused_header(&self, bytes: usize) {
        let mut state = self.0.lock().unwrap_or_else(|p| p.into_inner());
        state.usage.bytes = state.usage.bytes.saturating_add(bytes as u64);
        state.usage.messages = state.usage.messages.saturating_add(1);
    }
}

struct Reservation {
    budget: Budget,
    remaining: u64,
    message: bool,
}

impl Reservation {
    fn observed(&mut self, bytes: usize) {
        let bytes = bytes as u64;
        let mut state = self.budget.0.lock().unwrap_or_else(|p| p.into_inner());
        self.remaining -= bytes;
        state.reserved_bytes -= bytes;
        state.usage.bytes += bytes;
        if self.message && bytes != 0 {
            self.message = false;
            state.reserved_messages -= 1;
            state.usage.messages += 1;
        }
    }
}

impl Drop for Reservation {
    fn drop(&mut self) {
        let mut state = self.budget.0.lock().unwrap_or_else(|p| p.into_inner());
        state.reserved_bytes -= self.remaining;
        state.reserved_messages -= u64::from(self.message);
    }
}

#[derive(Debug)]
pub(crate) struct Packet {
    pub(crate) frame: Frame,
    pub(crate) attachments: Vec<Vec<u8>>,
}

struct HeaderObservation<'a> {
    budget: &'a Budget,
    bytes: usize,
}

impl Drop for HeaderObservation<'_> {
    fn drop(&mut self) {
        if self.bytes != 0 {
            self.budget.refused_header(self.bytes);
        }
    }
}

async fn read_header_part(
    input: &mut (impl AsyncRead + Unpin),
    target: &mut [u8],
    observation: &mut HeaderObservation<'_>,
) -> io::Result<()> {
    let mut offset = 0;
    while offset < target.len() {
        let read = input.read(&mut target[offset..]).await?;
        if read == 0 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "truncated proposer header",
            ));
        }
        observation.bytes += read;
        offset += read;
    }
    Ok(())
}

pub(crate) async fn read_packet(
    input: &mut (impl AsyncRead + Unpin),
    token: &str,
    sequence: u64,
    budget: &Budget,
) -> io::Result<Packet> {
    // Retain observed partial headers on EOF, I/O error, or cancellation. Their
    // bounded length is the only traffic read before the packet can be reserved.
    let mut observation = HeaderObservation { budget, bytes: 0 };
    let mut prefix = [0; HEADER_PREFIX_BYTES];
    read_header_part(input, &mut prefix, &mut observation).await?;
    let length = header_length(prefix)?;
    let mut header = vec![0; length];
    read_header_part(input, &mut header, &mut observation).await?;
    let frame = Frame::decode_header(&header)?;
    frame.validate(token, sequence, Direction::ToVerifier)?;
    let mut reservation = budget.reserve(frame.packet_length(length)?)?;
    reservation.observed(observation.bytes);
    observation.bytes = 0;
    let mut attachments = Vec::new();
    for length in frame.operation.attachment_lengths() {
        let mut attachment = vec![0; length];
        let mut offset = 0;
        while offset < length {
            let read = input.read(&mut attachment[offset..]).await?;
            if read == 0 {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "truncated proposer attachment",
                ));
            }
            reservation.observed(read);
            offset += read;
        }
        attachments.push(attachment);
    }
    Ok(Packet { frame, attachments })
}

pub(crate) async fn write_packet(
    output: &mut (impl AsyncWrite + Unpin),
    frame: &Frame,
    attachments: &[&[u8]],
    budget: &Budget,
    emergency: bool,
) -> io::Result<()> {
    let header = frame.encode_header()?;
    if frame.operation.attachment_lengths()
        != attachments
            .iter()
            .map(|part| part.len())
            .collect::<Vec<_>>()
    {
        return Err(io::Error::other("proposer attachment length mismatch"));
    }
    if emergency
        && (!matches!(
            frame.operation,
            Operation::Cancel { .. } | Operation::Shutdown { .. } | Operation::RequestClosed { .. }
        ) || !attachments.is_empty())
    {
        return Err(io::Error::other(
            "data cannot bypass proposer API accounting",
        ));
    }
    let mut reservation = if emergency {
        None
    } else {
        Some(budget.reserve(frame.packet_length(header.len())?)?)
    };
    let mut emergency_observation = HeaderObservation { budget, bytes: 0 };
    let prefix = (header.len() as u32).to_be_bytes();
    for part in std::iter::once(prefix.as_slice())
        .chain(std::iter::once(header.as_slice()))
        .chain(attachments.iter().copied())
    {
        let mut offset = 0;
        while offset < part.len() {
            let written = output.write(&part[offset..]).await?;
            if written == 0 {
                return Err(io::Error::new(
                    io::ErrorKind::WriteZero,
                    "proposer packet write stopped",
                ));
            }
            if let Some(reservation) = &mut reservation {
                reservation.observed(written);
            } else {
                emergency_observation.bytes += written;
            }
            offset += written;
        }
    }
    output.flush().await
}
