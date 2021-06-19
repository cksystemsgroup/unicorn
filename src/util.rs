use std::{
    collections::HashMap,
    convert::TryFrom,
    hash::Hash,
    ops::{Add, Div},
};

macro_rules! time_info {
    ($name:expr, $f:block) => {{
        let start = std::time::Instant::now();
        let result = $f;
        let end = std::time::Instant::now();
        log::info!("{} (took {:?})", $name, end.duration_since(start));
        result
    }};
}
macro_rules! time_debug {
    ($name:expr, $f:block) => {{
        let start = std::time::Instant::now();
        let result = $f;
        let end = std::time::Instant::now();
        log::debug!("{} (took {:?})", $name, end.duration_since(start));
        result
    }};
}

#[allow(unused_macros)]
macro_rules! time_trace {
    ($name:expr, $f:block) => {{
        let start = std::time::Instant::now();
        let result = $f;
        let end = std::time::Instant::now();
        log::trace!("{} (took {:?})", $name, end.duration_since(start));
        result
    }};
}

#[allow(unused_macros)]
macro_rules! time {
    ($f:block) => {{
        let start = std::time::Instant::now();
        let result = $f;
        let end = std::time::Instant::now();

        (result, end.duration_since(start))
    }};
}

pub fn mean<T>(data: &[T]) -> Option<T>
where
    T: Copy + Default + Add<T, Output = T> + Div<T, Output = T> + TryFrom<usize> + Ord,
{
    if let Ok(len) = T::try_from(data.len()) {
        if len == T::default() {
            None
        } else {
            let sum = data.iter().fold(T::default(), |acc, x| acc + *x);

            Some(sum / len)
        }
    } else {
        None
    }
}

pub fn mean_with_floating_point<T>(data: &[T]) -> Option<f64>
where
    T: Copy,
    i128: From<T>,
{
    let len = data.len();

    if len == 0 {
        None
    } else {
        let sum = data.iter().fold(0_i128, |acc, x| acc + (i128::from(*x)));

        Some((sum as f64) / (len as f64))
    }
}

pub fn median_of_sorted<T>(data: &[T]) -> Option<T>
where
    T: Add<T, Output = T> + Div<T, Output = T> + From<u32> + Copy,
{
    let size = data.len();

    match size {
        0 => None,
        even if even % 2 == 0 => {
            let fst_med = data[(size / 2) - 1];
            let snd_med = data[size / 2];

            Some((fst_med + snd_med) / T::from(2))
        }
        odd if odd % 2 == 1 => Some(data[odd / 2]),
        _ => unreachable!(),
    }
}

pub fn mode<C>(data: C) -> Option<C::Item>
where
    C: IntoIterator,
    C::Item: Ord + Hash,
{
    let frequencies = data.into_iter().fold(HashMap::new(), |mut freqs, value| {
        *freqs.entry(value).or_insert(0) += 1;
        freqs
    });

    frequencies
        .into_iter()
        .max_by_key(|&(_, count)| count)
        .map(|(value, _)| value)
}
