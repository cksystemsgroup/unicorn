use std::ops::{Index, IndexMut};

use bytesize::ByteSize;

#[derive(Debug, Clone)]
pub struct VirtualMemory<T> {
    memory_size: usize,
    segment_mask: usize,
    segment_shift: u32,
    default: T,
    data: Vec<Vec<T>>,
}

impl<T: Copy + Default> Index<usize> for VirtualMemory<T> {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        let segment_index = index >> self.segment_shift;
        let segment_offset = index & self.segment_mask;
        if self.data[segment_index].is_empty() {
            return &self.default;
        }
        Index::index(&self.data[segment_index], segment_offset)
    }
}

impl<T: Copy + Default> IndexMut<usize> for VirtualMemory<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let segment_index = index >> self.segment_shift;
        let segment_offset = index & self.segment_mask;
        if self.data[segment_index].is_empty() {
            self.data[segment_index] = vec![T::default(); self.segment_mask + 1];
        }
        IndexMut::index_mut(&mut self.data[segment_index], segment_offset)
    }
}

impl<T: Copy + Default> VirtualMemory<T> {
    pub fn new(memory_size: usize, segment_size: usize) -> Self {
        assert!(
            memory_size % segment_size == 0,
            "memory size must be multiple of segment size"
        );
        assert!(
            segment_size.is_power_of_two(),
            "segment size must be a power of two"
        );
        let segment_mask = segment_size - 1;
        let segment_shift = segment_size.trailing_zeros();
        let segments = memory_size / segment_size;
        Self {
            memory_size,
            segment_mask,
            segment_shift,
            default: T::default(),
            data: vec![[].to_vec(); segments],
        }
    }

    /// Returns an iterator over values in mapped memory segments.
    ///
    /// Note that the iterator does not cover un-mapped segments (i.e. segments that have not been
    /// written to before). This essentially skips over segments that would exclusively contain
    /// [`T::default()`] values. It also means that iteration likely yields fewer elements than
    /// calls of [`size()`] report.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.data.iter().filter(|x| !x.is_empty()).flatten()
    }

    pub fn size(&self) -> usize {
        self.memory_size
    }

    pub fn allocated(&self) -> ByteSize {
        ByteSize::b(
            self.data
                .iter()
                .filter(|x| !x.is_empty())
                .fold(0, |acc, _| acc + (self.segment_mask as u64) + 1),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn load_default() {
        let m = VirtualMemory::<i32>::new(32, 16);
        assert_eq!(m[0], 0);
        assert_eq!(m[15], 0);
        assert_eq!(m[16], 0);
        assert_eq!(m[31], 0);
    }

    #[test]
    #[should_panic]
    fn load_out_of_bounds() {
        let m = VirtualMemory::<i32>::new(32, 16);
        let _this_will_panic = m[32];
    }

    #[test]
    fn store_value() {
        let mut m = VirtualMemory::<i32>::new(32, 16);
        assert_eq!(m[0], 0);
        assert_eq!(m[1], 0);
        m[0] = 7;
        assert_eq!(m[0], 7);
        assert_eq!(m[1], 0);
    }

    #[test]
    #[should_panic]
    fn store_out_of_bounds() {
        let mut m = VirtualMemory::<i32>::new(32, 16);
        m[32] = 7; // this will panic
    }

    #[test]
    fn iter_values() {
        let mut m = VirtualMemory::<i32>::new(8, 2);
        m[0] = 23; // targets first segment
        m[3] = 42; // targets second segment
        assert_eq!(m.iter().copied().collect::<Vec<i32>>(), vec![23, 0, 0, 42]);
    }
}
