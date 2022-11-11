use std::panic::{catch_unwind, UnwindSafe};

pub fn unpanic<F, R, G>(panic_generator: F, if_not_panic_fn: G, error_message: &mut String)
where
    F: FnOnce() -> R + UnwindSafe,
    G: FnOnce(R),
{
    match catch_unwind(panic_generator) {
        Ok(x) => {
            if_not_panic_fn(x);
        }
        Err(err) => {
            let msg = match err.downcast_ref::<&'static str>() {
                Some(s) => *s,
                None => match err.downcast_ref::<String>() {
                    Some(s) => &s[..],
                    None => "Sorry, unknown payload type",
                },
            };

            *error_message = String::from(msg);
        }
    };
}
