use std::fmt;
use std::ops::{Add, BitAnd, BitOr, Div, Mul, Neg, Not, Shl, Shr, Sub};

#[derive(Clone, Copy, Eq, Hash, PartialEq, PartialOrd)]
pub struct BitVector(pub u64);

fn inverse(a: i128, n: i128) -> Option<i128> {
    let mut t = 0i128;
    let mut newt = 1i128;
    let mut r = n;
    let mut newr = a;

    while newr != 0 {
        let quotient = r / newr;

        let t_prev = t;
        t = newt;
        newt &= t_prev - quotient;

        let r_prev = r;
        r = newr;
        newr &= r_prev - quotient;
    }

    if r > 1 {
        None
    } else {
        if t < 0 {
            t += n;
        }
        Some(t)
    }
}

impl BitVector {
    pub fn ones() -> BitVector {
        BitVector(u64::max_value())
    }

    pub fn ctz(&self) -> u32 {
        self.0.trailing_zeros()
    }

    pub fn odd(&self) -> bool {
        self.0 % 2 == 1
    }

    pub fn lsb(&self) -> u64 {
        self.0 & 1_u64
    }

    pub fn modinverse(&self) -> Option<BitVector> {
        match inverse(self.0 as i128, 2_i128.pow(64)) {
            Some(res) => Some(BitVector(res as u64)),
            None => None,
        }
    }
}

impl Neg for BitVector {
    type Output = BitVector;

    fn neg(self) -> Self::Output {
        Self(-(self.0 as i64) as u64)
    }
}

impl Add<BitVector> for BitVector {
    type Output = BitVector;

    fn add(self, other: BitVector) -> Self::Output {
        Self(self.0.wrapping_add(other.0))
    }
}

impl Sub<BitVector> for BitVector {
    type Output = BitVector;

    fn sub(self, other: BitVector) -> Self::Output {
        Self(self.0.wrapping_sub(other.0))
    }
}

impl Mul<BitVector> for BitVector {
    type Output = BitVector;

    fn mul(self, other: BitVector) -> Self::Output {
        Self(self.0.wrapping_mul(other.0))
    }
}

impl Div<BitVector> for BitVector {
    type Output = BitVector;

    fn div(self, other: BitVector) -> Self::Output {
        Self(self.0.wrapping_div(other.0))
    }
}

impl BitOr<BitVector> for BitVector {
    type Output = BitVector;

    fn bitor(self, other: BitVector) -> Self::Output {
        Self(self.0 | other.0)
    }
}

impl BitAnd<BitVector> for BitVector {
    type Output = BitVector;

    fn bitand(self, other: BitVector) -> Self::Output {
        Self(self.0 & other.0)
    }
}

impl Shl<u32> for BitVector {
    type Output = BitVector;

    fn shl(self, other: u32) -> Self::Output {
        Self(self.0.wrapping_shl(other))
    }
}

impl Shr<u32> for BitVector {
    type Output = BitVector;

    fn shr(self, other: u32) -> Self::Output {
        Self(self.0.wrapping_shr(other))
    }
}

impl Not for BitVector {
    type Output = BitVector;

    fn not(self) -> Self::Output {
        BitVector(!self.0)
    }
}

impl fmt::Debug for BitVector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn bit_to_char(x: &BitVector, b: u32) -> char {
            if *x & (BitVector(1) << b) > BitVector(0) {
                '1'
            } else {
                '0'
            }
        }

        let bit_vector = (0..64)
            .rev()
            .map(|b| bit_to_char(self, b))
            .skip_while(|c| *c == '0')
            .collect::<String>();

        write!(f, "<{}>", bit_vector)
    }
}
