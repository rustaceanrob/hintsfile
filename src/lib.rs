use std::io::Read;

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
        let high_bytes = (n as usize + (m >> l) as usize + 1).div_ceil(8);
        let mut high_buf = vec![0u8; high_bytes];
        reader.read_exact(&mut high_buf)?;
        Ok(Self {
            n,
            m,
            low: low_buf,
            high: high_buf,
        })
    }
}

#[cfg(test)]
mod tests {
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
}
