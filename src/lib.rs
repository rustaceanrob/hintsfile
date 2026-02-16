use core::fmt;
use std::{
    collections::BTreeMap,
    io::{Read, Write},
};

/// An encoding scheme for representing a list of monotonically increasing elements.
#[derive(Debug)]
pub struct EliasFano {
    n: u16,
    m: u16,
    low: Vec<u8>,
    high: Vec<u8>,
}

impl EliasFano {
    /// Compress a unique, ordered set of elements.
    pub fn compress(elements: &[u16]) -> Self {
        debug_assert!(elements.is_sorted());
        debug_assert!(elements.len() < u16::MAX as usize);
        if elements.is_empty() {
            return Self {
                n: 0,
                m: 0,
                low: Vec::new(),
                high: Vec::new(),
            };
        }
        let m = *elements.last().expect("elements is non-empty.");
        let n = elements.len() as u16;
        let l = Self::l(m, n);
        let low = Self::pack_low_bits(elements, l);
        let high = Self::unary_encode_high_bits(elements, l);
        Self { n, m, low, high }
    }

    #[inline]
    fn pack_low_bits(elements: &[u16], l: u8) -> Vec<u8> {
        let mut packed = Vec::new();
        if l == 0 {
            return packed;
        }
        debug_assert!(l < 16);
        let mask = (1u16 << l) - 1;
        let mut curr_byte = 0x00;
        let mut bit_pos = 0x00;
        for &element in elements {
            let low = element & mask;
            for shift in 0..l {
                let bit = ((low >> shift) & 1) as u8;
                curr_byte |= bit << (7 - bit_pos);
                bit_pos += 1;
                if bit_pos == 8 {
                    packed.push(curr_byte);
                    bit_pos = 0x00;
                    curr_byte = 0x00;
                }
            }
        }
        if bit_pos > 0 {
            packed.push(curr_byte);
        }
        packed
    }

    #[inline]
    fn unary_encode_high_bits(elements: &[u16], l: u8) -> Vec<u8> {
        let mut high = Vec::new();
        let mut curr_byte = 0x00;
        let mut bit_pos = 0x00;
        let mut prev = 0x00;
        for &element in elements {
            let current = element >> l;
            let delta = current - prev;
            prev = current;
            for _noop in 0..delta {
                bit_pos += 1;
                if bit_pos == 8 {
                    high.push(curr_byte);
                    bit_pos = 0x00;
                    curr_byte = 0x00;
                }
            }
            curr_byte |= 1 << (7 - bit_pos);
            bit_pos += 1;
            if bit_pos == 8 {
                high.push(curr_byte);
                bit_pos = 0x00;
                curr_byte = 0x00;
            }
        }
        if bit_pos > 0 {
            high.push(curr_byte);
        }
        high
    }

    /// Decompress the ascending indices.
    pub fn decompress(&self) -> Vec<u16> {
        let mut indices = Vec::with_capacity(self.n as usize);
        if self.n == 0 {
            return indices;
        }
        let l = Self::l(self.m, self.n);
        let mut low_byte_pos = 0x00;
        let mut low_bit_pos = 0x00;
        let mut high_byte_pos: usize = 0;
        let mut high_bit_pos: u8 = 0;
        let mut high_prefix: u16 = 0;
        for _ in 0..self.n {
            let mut low_val: u16 = 0;
            for shift in 0..l {
                let bit = (self.low[low_byte_pos] >> (7 - low_bit_pos)) & 1;
                low_val |= (bit as u16) << shift;
                low_bit_pos += 1;
                if low_bit_pos == 8 {
                    low_byte_pos += 1;
                    low_bit_pos = 0;
                }
            }
            loop {
                let bit = (self.high[high_byte_pos] >> (7 - high_bit_pos)) & 1;
                high_bit_pos += 1;
                if high_bit_pos == 8 {
                    high_byte_pos += 1;
                    high_bit_pos = 0;
                }
                if bit == 1 {
                    break;
                }
                high_prefix += 1;
            }
            indices.push((high_prefix << l) | low_val);
        }
        indices
    }

    /// Size of the representation in bytes.
    #[inline]
    pub fn size(&self) -> usize {
        size_of::<u16>() + size_of::<u16>() + self.low.len() + self.high.len()
    }

    /// The number of lower bits in the representation, floor(log_2((`m` + 1)/ `n`)) where `n` is
    /// the size of the list and `m` is the largest element.
    #[inline]
    const fn l(m: u16, n: u16) -> u8 {
        debug_assert!(m != u16::MAX);
        ((m + 1) / n).ilog2() as u8
    }

    /// Read a list representation from disk.
    pub fn from_reader<R: Read>(reader: &mut R) -> Result<Self, std::io::Error> {
        let mut n_buf = [0u8; 2];
        reader.read_exact(&mut n_buf)?;
        let n = u16::from_le_bytes(n_buf);
        if n == 0 {
            return Ok(Self {
                n,
                m: 0x00,
                low: Vec::new(),
                high: Vec::new(),
            });
        }
        let mut m_buf = [0u8; 2];
        reader.read_exact(&mut m_buf)?;
        let m = u16::from_le_bytes(m_buf);
        let l = Self::l(m, n);
        let low_bytes = (n as usize * l as usize).div_ceil(8);
        let mut low_buf = vec![0u8; low_bytes];
        reader.read_exact(&mut low_buf)?;
        debug_assert!(m != u16::MAX);
        let high_bytes = (n as usize + (m >> l) as usize).div_ceil(8);
        let mut high_buf = vec![0u8; high_bytes];
        reader.read_exact(&mut high_buf)?;
        Ok(Self {
            n,
            m,
            low: low_buf,
            high: high_buf,
        })
    }

    /// Serialize this representation to bytes.
    #[inline]
    pub fn serialize(self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(self.size());
        bytes.extend_from_slice(&self.n.to_le_bytes());
        if self.n == 0 {
            return bytes;
        }
        bytes.extend_from_slice(&self.m.to_le_bytes());
        bytes.extend_from_slice(&self.low);
        bytes.extend_from_slice(&self.high);
        bytes
    }

    #[inline]
    pub fn write<W: Write>(self, writer: &mut W) -> Result<(), std::io::Error> {
        writer.write_all(&self.serialize())
    }
}

/// A file of hints for the UTXO set.
#[derive(Debug)]
pub struct Hintsfile {
    map: BTreeMap<u32, EliasFano>,
}

impl Hintsfile {
    const MAGIC: [u8; 4] = [0x55, 0x54, 0x58, 0x4f];
    const VERSION: u8 = 0x00;
    /// Build a hintsfile from a buffer, like a file on disk. This reads the entire hintsfile into
    /// memory. To query one block at a time from a file, see [`EliasFano::from_reader`].
    pub fn from_reader<R: Read>(reader: &mut R) -> Result<Self, ReadError> {
        let mut magic_buf = [0u8; 4];
        reader.read_exact(&mut magic_buf)?;
        if magic_buf != (Self::MAGIC) {
            return Err(ReadError::UnknownMagic(magic_buf));
        }
        let mut version_buf = [0u8; 1];
        reader.read_exact(&mut version_buf)?;
        let version = u8::from_le_bytes(version_buf);
        if version != Self::VERSION {
            return Err(ReadError::UnsupportedVersion(version));
        }
        let mut height = 1;
        let mut map = BTreeMap::new();
        while let Ok(ef) = EliasFano::from_reader(reader) {
            map.insert(height, ef);
            height += 1;
        }
        Ok(Self { map })
    }

    /// Get the unspent indices for a block height. Returns `None` if unavailable.
    pub fn indices_at_height(&self, height: u32) -> Option<Vec<u16>> {
        self.map.get(&height).map(|ef| ef.decompress())
    }

    /// The last height this file encodes for.
    pub fn stop_height(&self) -> u32 {
        self.map.keys().max().copied().unwrap_or_default()
    }
}

/// Error reading a hintsfile from a buffer.
#[derive(Debug)]
pub enum ReadError {
    Io(std::io::Error),
    UnknownMagic([u8; 4]),
    UnsupportedVersion(u8),
}

impl fmt::Display for ReadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(io) => write!(f, "io error: {io}"),
            Self::UnknownMagic(magic) => write!(f, "unknown magic: {magic:?}"),
            Self::UnsupportedVersion(v) => write!(f, "unsupported version: {v}"),
        }
    }
}

impl std::error::Error for ReadError {}

impl From<std::io::Error> for ReadError {
    fn from(value: std::io::Error) -> Self {
        Self::Io(value)
    }
}

/// Build a hintsfile iteratively.
#[derive(Debug)]
pub struct HintsfileBuilder<W: Write> {
    writer: W,
}

impl<W: Write> HintsfileBuilder<W> {
    /// Initialize a hintsfile to be written to.
    pub fn start(mut writer: W) -> Result<Self, std::io::Error> {
        writer.write_all(&Hintsfile::MAGIC)?;
        writer.write_all(&[Hintsfile::VERSION])?;
        Ok(Self { writer })
    }

    /// Append hints for a block, starting from height one.
    pub fn append(&mut self, encoding: EliasFano) -> Result<(), std::io::Error> {
        encoding.write(&mut self.writer)
    }

    /// Flush the buffer.
    pub fn finish(&mut self) -> Result<(), std::io::Error> {
        self.writer.flush()
    }
}

#[cfg(test)]
mod tests {
    use std::io::BufReader;

    use crate::{Hintsfile, HintsfileBuilder};

    use super::EliasFano;

    #[test]
    fn compress_decompress() {
        let mut elms = Vec::new();
        let ef = EliasFano::compress(&elms);
        assert!(ef.decompress().is_empty());
        elms.push(42);
        let ef = EliasFano::compress(&elms);
        let items = ef.decompress();
        assert_eq!(items, elms);
        elms.clear();
        for i in 0..(u16::MAX - 1) {
            if !i.is_multiple_of(7) || i.is_power_of_two() || !i.is_multiple_of(13) {
                elms.push(i);
            }
        }
        let ef = EliasFano::compress(&elms);
        let items = ef.decompress();
        assert_eq!(items, elms);
    }

    #[test]
    fn serde() {
        let mut want = Vec::new();
        for i in 0..(u16::MAX - 1) {
            if !i.is_multiple_of(21) || !i.is_multiple_of(11) {
                want.push(i);
            }
        }
        let ef = EliasFano::compress(&want);
        let mut ef_buf = Vec::new();
        ef.write(&mut ef_buf).unwrap();
        let mut buf_reader = BufReader::new(ef_buf.as_slice());
        let ef = EliasFano::from_reader(&mut buf_reader).unwrap();
        let got = ef.decompress();
        assert_eq!(want, got);
    }

    #[test]
    fn hintsfile_roundtrip() {
        let want = Vec::new();
        let mut builder = HintsfileBuilder::start(want).unwrap();
        for j in 12..16 {
            let mut nums = Vec::new();
            for i in 0..(u16::MAX - 1) {
                if !i.is_multiple_of(j) || !i.is_multiple_of(j >> 1) || i.is_multiple_of(7) {
                    nums.push(i)
                }
            }
            let ef = EliasFano::compress(&nums);
            builder.append(ef).unwrap();
        }
        let mut buf_reader = BufReader::new(builder.writer.as_slice());
        let hintsfile = Hintsfile::from_reader(&mut buf_reader).unwrap();
        assert_eq!(hintsfile.stop_height(), 4);
        let mut nums = Vec::new();
        for i in 0..(u16::MAX - 1) {
            if !i.is_multiple_of(14) || !i.is_multiple_of(14 >> 1) || i.is_multiple_of(7) {
                nums.push(i)
            }
        }
        assert_eq!(hintsfile.indices_at_height(3).unwrap(), nums);
    }
}
