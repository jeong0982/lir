pub trait Translate<S> {
    type Target;
    type Error;
    fn translate(&mut self, source: &S) -> Result<Self::Target, Self::Error>;
}

#[macro_export]
/// Some or executing the given expression.
macro_rules! some_or {
    ($e:expr, $err:expr) => {{
        match $e {
            Some(r) => r,
            None => $err,
        }
    }};
}

#[macro_export]
/// Ok or exiting the process.
macro_rules! ok_or_exit {
    ($e:expr, $code:expr) => {{
        match $e {
            Ok(r) => r,
            Err(e) => {
                eprintln!("{:?}", e);
                std::process::exit($code);
            }
        }
    }};
}
