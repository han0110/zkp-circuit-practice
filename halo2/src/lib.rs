pub mod gadget;
pub mod util;

#[macro_export]
macro_rules! const_expr {
    ($const:expr) => {
        halo2::plonk::Expression::Constant(F::from_u64($const as u64))
    };
}

#[macro_export]
macro_rules! lookup_error_at {
    ($lookup_index:expr, $row:expr) => {
        halo2::dev::VerifyFailure::Lookup {
            lookup_index: $lookup_index,
            row: $row,
        }
    };
}
