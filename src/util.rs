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
