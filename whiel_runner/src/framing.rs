//! Shared bounded big-endian JSON framing for worker and provider sockets.

use serde::{Deserialize, Serialize};
use std::io::{self, Read, Write};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};

pub fn bounded_json<T: Serialize>(value: &T, maximum: usize) -> io::Result<Vec<u8>> {
    struct Buffer {
        bytes: Vec<u8>,
        maximum: usize,
    }
    impl Write for Buffer {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            if bytes.len() > self.maximum.saturating_sub(self.bytes.len()) {
                return Err(io::Error::other(format!(
                    "too_large: encoded transport limit {} bytes; encoded message was not sent",
                    self.maximum
                )));
            }
            let needed = self.bytes.len() + bytes.len();
            if needed > self.bytes.capacity() {
                let capacity = self
                    .bytes
                    .capacity()
                    .saturating_mul(2)
                    .max(256)
                    .max(needed)
                    .min(self.maximum);
                self.bytes
                    .try_reserve_exact(capacity - self.bytes.len())
                    .map_err(io::Error::other)?;
            }
            self.bytes.extend_from_slice(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }
    let mut buffer = Buffer {
        bytes: Vec::new(),
        maximum,
    };
    serde_json::to_writer(&mut buffer, value).map_err(io::Error::other)?;
    Ok(buffer.bytes)
}

fn payload<T: Serialize>(value: &T, maximum: usize) -> io::Result<([u8; 4], Vec<u8>)> {
    let bytes = bounded_json(value, maximum.min(u32::MAX as usize))?;
    Ok(((bytes.len() as u32).to_be_bytes(), bytes))
}

fn length(header: [u8; 4], maximum: usize) -> io::Result<usize> {
    let size = u32::from_be_bytes(header) as usize;
    if size == 0 || size > maximum {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("worker frame length {size} is outside 1..={maximum}"),
        ));
    }
    Ok(size)
}

pub fn write_frame<T: Serialize>(
    writer: &mut impl Write,
    value: &T,
    maximum: usize,
) -> io::Result<()> {
    let (header, bytes) = payload(value, maximum)?;
    writer.write_all(&header)?;
    writer.write_all(&bytes)?;
    writer.flush()
}

pub fn read_frame<T: for<'de> Deserialize<'de>>(
    reader: &mut impl Read,
    maximum: usize,
) -> io::Result<T> {
    let mut header = [0; 4];
    reader.read_exact(&mut header)?;
    let mut bytes = vec![0; length(header, maximum)?];
    reader.read_exact(&mut bytes)?;
    serde_json::from_slice(&bytes)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
}

pub async fn write_frame_async<T: Serialize>(
    writer: &mut (impl AsyncWrite + Unpin),
    value: &T,
    maximum: usize,
) -> io::Result<()> {
    let (header, bytes) = payload(value, maximum)?;
    writer.write_all(&header).await?;
    writer.write_all(&bytes).await?;
    writer.flush().await
}

pub async fn read_frame_async<T: for<'de> Deserialize<'de>>(
    reader: &mut (impl AsyncRead + Unpin),
    maximum: usize,
) -> io::Result<T> {
    let mut header = [0; 4];
    reader.read_exact(&mut header).await?;
    let mut bytes = vec![0; length(header, maximum)?];
    reader.read_exact(&mut bytes).await?;
    serde_json::from_slice(&bytes)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Value, json};

    #[test]
    fn encoding_caps_escaped_bytes_before_transport_output() {
        let value = json!({"bytes":[0,255],"text":"\n\"\\"});
        let expected = serde_json::to_vec(&value).unwrap();
        let encoded = bounded_json(&value, expected.len()).unwrap();
        assert!(encoded.capacity() <= expected.len());
        assert_eq!(encoded, expected);
        let mut output = Vec::new();
        assert!(write_frame(&mut output, &value, expected.len() - 1).is_err());
        assert!(output.is_empty());
    }

    #[test]
    fn serializer_stops_traversing_when_the_buffer_is_full() {
        use serde::ser::SerializeSeq;
        struct Long;
        impl Serialize for Long {
            fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                let mut sequence = serializer.serialize_seq(None)?;
                for n in 0..1_000_000 {
                    assert!(n < 100, "serializer traversed beyond cap");
                    sequence.serialize_element(&n)?;
                }
                sequence.end()
            }
        }
        assert!(bounded_json(&Long, 32).is_err());
    }

    #[tokio::test]
    async fn sync_and_async_frames_are_identical() {
        let value = json!({"kind":"fixture","bytes":[0,255]});
        let mut bytes = Vec::new();
        write_frame(&mut bytes, &value, 1024).unwrap();
        let mut reader = bytes.as_slice();
        assert_eq!(
            read_frame_async::<Value>(&mut reader, 1024).await.unwrap(),
            value
        );
        let mut asynchronous = Vec::new();
        write_frame_async(&mut asynchronous, &value, 1024)
            .await
            .unwrap();
        assert_eq!(asynchronous, bytes);
    }

    #[test]
    fn malformed_lengths_and_incomplete_payloads_fail() {
        for mut bytes in [
            &[0, 0, 0, 0][..],
            &[0, 0, 0, 9][..],
            &[0, 0, 0, 2, b'{'][..],
        ] {
            assert!(read_frame::<Value>(&mut bytes, 8).is_err());
        }
        assert!(write_frame(&mut Vec::new(), &json!({"large":"fixture"}), 2).is_err());
    }
}
