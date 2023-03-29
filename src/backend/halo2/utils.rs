use halo2_proofs::{halo2curves::FieldExt, plonk::Expression};

/// Trait that implements functionality to get a constant expression from
/// commonly used types.
pub trait Expr<F: FieldExt> {
    /// Returns an expression for the type.
    fn expr(&self) -> Expression<F>;
}

/// Implementation trait `Expr` for type able to be casted to u64
#[macro_export]
macro_rules! impl_expr {
    ($type:ty) => {
        impl<F: halo2_proofs::arithmetic::FieldExt> $crate::backend::halo2::utils::Expr<F>
            for $type
        {
            #[inline]
            fn expr(&self) -> Expression<F> {
                Expression::Constant(F::from(*self as u64))
            }
        }
    };
    ($type:ty, $method:path) => {
        impl<F: halo2_proofs::arithmetic::FieldExt> $crate::backend::halo2::utils::Expr<F>
            for $type
        {
            #[inline]
            fn expr(&self) -> Expression<F> {
                Expression::Constant(F::from($method(self) as u64))
            }
        }
    };
}
