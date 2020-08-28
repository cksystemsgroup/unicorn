pub trait ForEachUntilSome<Iter, T, R> {
    fn for_each_until_some<F>(&mut self, f: F) -> Option<R>
    where
        Iter: Iterator<Item = T>,
        F: FnMut(T) -> Option<R>;
}

impl<Iter, T, R> ForEachUntilSome<Iter, T, R> for Iter {
    fn for_each_until_some<F>(&mut self, mut f: F) -> Option<R>
    where
        Iter: Iterator<Item = T>,
        F: FnMut(T) -> Option<R>,
    {
        for element in self {
            if let Some(result) = f(element) {
                return Some(result);
            }
        }

        None
    }
}
