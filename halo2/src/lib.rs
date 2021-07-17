pub mod gadget;

#[macro_export]
macro_rules! lookup_error_at {
    ($lookup_index:expr, $row:expr) => {
        halo2::dev::VerifyFailure::Lookup {
            lookup_index: $lookup_index,
            row: $row,
        }
    };
}
