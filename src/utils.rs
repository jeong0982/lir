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
