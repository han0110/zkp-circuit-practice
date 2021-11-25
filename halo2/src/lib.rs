pub mod gadget;

#[macro_export]
macro_rules! const_expr {
    ($const:expr) => {
        halo2::plonk::Expression::Constant(F::from_u64($const as u64))
    };
}
