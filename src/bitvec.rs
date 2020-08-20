//! # Handle bit vectors

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct BitVector {
    pub(crate) value: u64,
}

impl BitVector {
    #[allow(dead_code)]
    fn new(value: u64) -> Self {
        BitVector { value }
    }
}
