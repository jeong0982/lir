mod backend;
mod frontend;
pub mod ir;
mod irgen;
mod opt;
mod utils;
mod vm;
mod write_base;

pub use frontend::utils as frontutils;
pub use frontend::Parse;
pub use irgen::Irgen;
pub use opt::{
    Deadcode, FunctionPass, Gvn, Mem2reg, Optimize, Repeat, SimplifyCfg, SimplifyCfgConstProp,
    SimplifyCfgEmpty, SimplifyCfgMerge, SimplifyCfgReach, O0, O1,
};
pub use utils::*;
pub use vm::execute;
pub use write_base::write;
