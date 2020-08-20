use crate::bitvec::BitVector;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct TernaryBitVector {
    xlo: u64,
    xhi: u64,
}

impl TernaryBitVector {
    pub fn new(xlo: u64, xhi: u64) -> Self {
        assert!(Self::valid(xlo, xhi), "is not a valid ternary bit vector");
        Self { xlo, xhi }
    }

    /// verifies that these two values can form a valid ternary bit vector
    pub fn valid(xlo: u64, xhi: u64) -> bool {
        !xlo | xhi == u64::max_value()
    }

    /// verifies that all constant bits of a ternary bit vector match a bit vector
    #[allow(dead_code)]
    pub fn mcb(&self, other: &BitVector) -> bool {
        (self.xhi & other.value == other.value) && (self.xlo | other.value == other.value)
    }
}
