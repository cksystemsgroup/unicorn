#![allow(dead_code)]

use crate::bitvec::BitVector;
use std::fmt;
use std::ops::Shl;

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
pub struct TernaryBitVector(BitVector, BitVector);

impl TernaryBitVector {
    pub fn new(xlo: u64, xhi: u64) -> Self {
        let xlo = BitVector(xlo);
        let xhi = BitVector(xhi);

        assert!(Self::valid(xlo, xhi), "is not a valid ternary bit vector");

        Self(xlo, xhi)
    }

    pub fn lo(&self) -> BitVector {
        self.0
    }

    pub fn hi(&self) -> BitVector {
        self.1
    }

    pub const fn lit(literal: &'static str) -> TernaryBitVector {
        let len = literal.len();

        // not allowed in const functions
        // assert!(len <= 64, "cannot handle bit vector literals larger than 64 bit");

        const fn add(t: TernaryBitVector, xlo: u32, xhi: u32) -> TernaryBitVector {
            TernaryBitVector(
                BitVector((t.0).0.wrapping_shl(1) + (xlo as u64)),
                BitVector((t.1).0.wrapping_shl(1) + (xhi as u64)),
            )
        }

        let mut acc = TernaryBitVector(BitVector(0), BitVector(0));

        let mut i = 0;

        while i < len {
            let cs = literal.as_bytes();

            acc = match cs[i] {
                0x30 => add(acc, 0, 0),
                0x31 => add(acc, 1, 1),
                0x2A => add(acc, 0, 1),
                _ => TernaryBitVector(BitVector(0), BitVector(0)), // unreachable!(),
            };

            i += 1;
        }

        acc
    }

    /// verifies that these two values can form a valid ternary bit vector
    pub fn valid(xlo: BitVector, xhi: BitVector) -> bool {
        !xlo | xhi == BitVector::ones()
    }

    /// verifies that all constant bits of a ternary bit vector match a bit vector
    #[allow(dead_code)]
    pub fn mcb(&self, other: BitVector) -> bool {
        (self.1 & other == other) && (self.0 | other == other)
    }

    pub fn is_const(&self) -> bool {
        self.0 == self.1
    }

    pub fn constant_bit_mask(&self) -> BitVector {
        !(!self.0 & self.1)
    }

    pub fn constant_bits(&self) -> BitVector {
        self.0 & self.1
    }

    /*pub fn mulo(s: BitVector, x: TernaryBitVector) -> bool {
        s.0.overflowing_mul(x.0).1
    }

    pub fn addo(s: BitVector, x: TernaryBitVector) -> bool {
        s.0.overflowing_add(x.0).1
    }*/
}

impl Shl<u32> for TernaryBitVector {
    type Output = TernaryBitVector;

    fn shl(self, shift: u32) -> Self::Output {
        TernaryBitVector(self.0 << shift, self.1 << shift)
    }
}

impl fmt::Debug for TernaryBitVector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn bit_to_char(x: &TernaryBitVector, b: u32) -> char {
            let lo = x.0 & (BitVector(1) << b) > BitVector(0);
            let hi = x.1 & (BitVector(1) << b) > BitVector(0);

            match (lo, hi) {
                (false, false) => '0',
                (false, true) => '*',
                (true, false) => panic!("trying to print invalid ternary bit vector"),
                (true, true) => '1',
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
