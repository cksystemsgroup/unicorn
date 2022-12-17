use crate::guinea::giraphe::MachineWord::Concrete;
use crate::guinea::giraphe::{MachineWord, Value};
use std::cmp::Ordering;
use std::cmp::Ordering::{Equal, Greater, Less};
use std::ops::{Add, BitAnd, Div, Mul, Not, Rem, Shl, Shr, Sub};

// ----------------------------
//         NODE VALUES
// ----------------------------
impl Add for Value {
    type Output = Value;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Bitvector(lhs), Self::Bitvector(rhs)) => Self::Bitvector(lhs + rhs),
            (x, y) => panic!("Can't add {:?} and {:?}", x, y),
        }
    }
}

impl Sub for Value {
    type Output = Value;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Bitvector(lhs), Self::Bitvector(rhs)) => Self::Bitvector(lhs - rhs),
            (x, y) => panic!("Can't sub {:?} and {:?}", x, y),
        }
    }
}

impl Mul for Value {
    type Output = Value;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Bitvector(lhs), Self::Bitvector(rhs)) => Self::Bitvector(lhs * rhs),
            (x, y) => panic!("Can't mul {:?} and {:?}", x, y),
        }
    }
}

impl Div for Value {
    type Output = Value;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Bitvector(lhs), Self::Bitvector(rhs)) => Self::Bitvector(lhs / rhs),
            (x, y) => panic!("Can't divide {:?} and {:?}", x, y),
        }
    }
}

impl Rem for Value {
    type Output = Value;

    fn rem(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Bitvector(lhs), Self::Bitvector(rhs)) => Self::Bitvector(lhs % rhs),
            (x, y) => panic!("Can't remainder {:?} and {:?}", x, y),
        }
    }
}

impl Shl for Value {
    type Output = Value;

    fn shl(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Bitvector(lhs), Self::Bitvector(rhs)) => Self::Bitvector(lhs << rhs),
            (x, y) => panic!("Can't shift left {:?} and {:?}", x, y),
        }
    }
}

impl Shr for Value {
    type Output = Value;

    fn shr(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Bitvector(lhs), Self::Bitvector(rhs)) => Self::Bitvector(lhs >> rhs),
            (x, y) => panic!("Can't shift right {:?} and {:?}", x, y),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bitvector(lhs), Self::Bitvector(rhs)) => lhs == rhs,
            (x, y) => panic!("Can't equal {:?} and {:?}", x, y),
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Self::Bitvector(lhs), Self::Bitvector(rhs)) => Some(if lhs < rhs {
                Less
            } else if lhs > rhs {
                Greater
            } else {
                Equal
            }),
            (x, y) => panic!("Can't order {:?} and {:?}", x, y),
        }
    }
}

impl BitAnd for Value {
    type Output = Value;

    fn bitand(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Boolean(lhs), Self::Boolean(rhs)) => Self::Boolean(lhs && rhs),
            (x, y) => panic!("Can't and {:?} and {:?}", x, y),
        }
    }
}

impl Not for Value {
    type Output = Value;

    fn not(self) -> Self::Output {
        match self {
            Self::Boolean(x) => Self::Boolean(!x),
            x => panic!("Can't not {:?}", x),
        }
    }
}

// ----------------------------
//        MACHINE WORDS
// ----------------------------
impl Add for MachineWord {
    type Output = MachineWord;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Concrete(x), Concrete(y)) => Concrete(x + y),
        }
    }
}

impl Sub for MachineWord {
    type Output = MachineWord;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Concrete(x), Concrete(y)) => Concrete(x - y),
        }
    }
}

impl Mul for MachineWord {
    type Output = MachineWord;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Concrete(x), Concrete(y)) => Concrete(x * y),
        }
    }
}

impl Div for MachineWord {
    type Output = MachineWord;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Concrete(x), Concrete(y)) => Concrete(x / y),
        }
    }
}

impl Rem for MachineWord {
    type Output = MachineWord;

    fn rem(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Concrete(x), Concrete(y)) => Concrete(x % y),
        }
    }
}

impl Shl for MachineWord {
    type Output = MachineWord;

    fn shl(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Concrete(x), Concrete(y)) => Concrete(x << y),
        }
    }
}

impl Shr for MachineWord {
    type Output = MachineWord;

    fn shr(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Concrete(x), Concrete(y)) => Concrete(x >> y),
        }
    }
}

impl PartialEq<Self> for MachineWord {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Concrete(lhs), Concrete(rhs)) => lhs == rhs,
        }
    }
}

impl PartialOrd for MachineWord {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Concrete(lhs), Concrete(rhs)) => Some(lhs.cmp(rhs)),
        }
    }
}
