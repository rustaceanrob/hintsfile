use std::io::Read;

#[derive(Debug)]
pub struct EliasFano {
    n: u16,
    m: u16,
    low_bits: u8,
    low: Vec<u8>,
    high: Vec<u8>,
}

impl EliasFano {
    pub fn compress(elements: &[u16]) -> Self {
        debug_assert!(elements.is_sorted());
        debug_assert!(elements.len() < u16::MAX as usize);
        if elements.is_empty() {
            return Self {
                n: 0,
                m: 0,
                low_bits: 0,
                low: Vec::new(),
                high: Vec::new(),
            };
        }
        let m = *elements.last().expect("elements is non-empty.");
        debug_assert!(m != u16::MAX);
        let n = elements.len() as u16;
        let l = ((m + 1) / n).ilog2() as u8;
        let low = Self::pack_low_bits(elements, l);
        let high = Self::unary_encode_high_bits(elements, l);
        Self {
            n,
            m,
            low_bits: l,
            low,
            high,
        }
        // let total_lower_bytes = (n as u32 * l as u32).div_ceil(8) as usize;
    }

    pub fn from_reader<R: Read>(reader: &mut R) -> Result<Self, std::io::Error> {
        let mut n_buf = [0u8; 2];
        reader.read_exact(&mut n_buf)?;
        let n = u16::from_le_bytes(n_buf);
        if n == 0 {
            return Ok(Self {
                n,
                m: 0x00,
                low_bits: 0x00,
                low: Vec::new(),
                high: Vec::new(),
            });
        }
        let mut m_buf = [0u8; 2];
        reader.read_exact(&mut m_buf)?;
        let m = u16::from_le_bytes(m_buf);
        let mut l_buf = [0u8; 1];
        reader.read_exact(&mut l_buf)?;
        let l = u8::from_le_bytes(l_buf);
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
            low_bits: l,
            low: low_buf,
            high: high_buf,
        })
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

    #[inline]
    pub fn size(&self) -> usize {
        size_of::<u16>() + size_of::<u16>() + size_of::<u8>() + self.low.len() + self.high.len()
    }
}
