mod write_base;
mod frontend;
pub mod ir;
mod irgen;
mod opt;
mod utils;

pub use write_base::write;
pub use frontend::utils as frontutils;
pub use frontend::Parse;
pub use irgen::Irgen;
pub use opt::{
    Deadcode, FunctionPass, Optimize, Repeat, SimplifyCfg, SimplifyCfgConstProp, SimplifyCfgEmpty,
    SimplifyCfgMerge, SimplifyCfgReach, Mem2reg,
};
pub use utils::*;
