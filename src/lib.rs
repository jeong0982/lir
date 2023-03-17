mod frontend;
pub mod ir;
mod irgen;
mod opt;
pub mod utils;

pub use frontend::utils as frontutils;
pub use frontend::Parse;

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
