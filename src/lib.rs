mod frontend;
pub mod ir;
mod irgen;
mod opt;
mod utils;

pub use frontend::utils as frontutils;
pub use frontend::Parse;
pub use irgen::Irgen;
pub use utils::*;
pub use opt::{
    Deadcode, FunctionPass, Optimize, Repeat, SimplifyCfg, SimplifyCfgConstProp,
    SimplifyCfgEmpty, SimplifyCfgMerge, SimplifyCfgReach,
};
