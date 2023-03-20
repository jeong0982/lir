use crate::ir;
use crate::*;

mod deadcode;
pub mod opt_utils;
mod simplify_cfg;

pub use deadcode::Deadcode;
pub use simplify_cfg::{
    SimplifyCfg, SimplifyCfgConstProp, SimplifyCfgEmpty, SimplifyCfgMerge, SimplifyCfgReach,
};

pub trait Optimize<T> {
    fn optimize(&mut self, code: &mut T) -> bool;
}

#[derive(Default, Clone, Copy, Debug)]
pub struct Null;

#[derive(Default, Debug)]
pub struct Repeat<O> {
    inner: O,
}

impl<T, O1: Optimize<T>, O2: Optimize<T>> Optimize<T> for (O1, O2) {
    fn optimize(&mut self, code: &mut T) -> bool {
        let changed1 = self.0.optimize(code);
        let changed2 = self.1.optimize(code);
        changed1 || changed2
    }
}

impl<T, O: Optimize<T>> Optimize<T> for Repeat<O> {
    fn optimize(&mut self, code: &mut T) -> bool {
        if !self.inner.optimize(code) {
            return false;
        }

        while self.inner.optimize(code) {}
        true
    }
}

#[derive(Default, Debug)]
pub struct FunctionPass<T: Optimize<ir::FunctionDefinition>> {
    inner: T,
}

impl<T> Optimize<ir::TranslationUnit> for FunctionPass<T>
where
    T: Optimize<ir::FunctionDefinition>,
{
    fn optimize(&mut self, code: &mut ir::TranslationUnit) -> bool {
        code.decls
            .values_mut()
            .map(|decl| self.optimize(decl))
            .fold(false, |l, r| l | r)
    }
}

impl<T> Optimize<ir::Declaration> for FunctionPass<T>
where
    T: Optimize<ir::FunctionDefinition>,
{
    fn optimize(&mut self, code: &mut ir::Declaration) -> bool {
        let (_, fdef) = some_or!(code.get_function_mut(), return false);
        let fdef = some_or!(fdef, return false);
        self.inner.optimize(fdef)
    }
}
