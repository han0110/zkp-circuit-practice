use zkp_stark::{primefield::*, *};

// SampleClaim claims y = x^3 + x + 5
// The trace table will be:
//       row   c0    c1
// T =  ----- ----- -------------
//       1     x     x^2
//       2     x^3   x^3 + x + 5
struct SampleClaim {
    y: FieldElement,
}

impl Verifiable for SampleClaim {
    fn constraints(&self) -> Constraints {
        use RationalExpression::*;

        let (trace_nrows, trace_ncolumns) = (2, 2);
        let g = Constant(FieldElement::root(trace_nrows).unwrap());
        let on_row = |index| (X - g.pow(index)).inv();

        let c = Constraints::from_expressions(
            (trace_nrows, trace_ncolumns),
            self.y.as_montgomery().to_bytes_be().to_vec(),
            vec![
                // T[0][0] * T[0][0] - T[0][1] = 0 (x * x - x^2 = 0)
                (Trace(0, 0) * Trace(0, 0) - Trace(1, 0)) * on_row(0),
                // T[0][1] * T[0][0] - T[1][0] = 0 (x^2 * x - x^3 = 0)
                (Trace(0, 0) * Trace(1, 0) - Trace(0, 1)) * on_row(0),
                // T[1][0] + T[0][0] + 5 - T[1][1] = 0 (x^3 + x + 5 - y = 0)
                (Trace(0, 1) + Trace(0, 0) + Constant(5.into()) - Trace(1, 1)) * on_row(0),
                // T[1][1] - y = 0 (boundary condition)
                (Trace(1, 0) - Constant(self.y.clone())) * on_row(1),
            ],
        )
        .unwrap();
        c
    }
}

impl Provable<&FieldElement> for SampleClaim {
    fn trace(&self, x: &FieldElement) -> TraceTable {
        let (trace_nrows, trace_ncolumns) = (2, 2);
        let mut trace = TraceTable::new(trace_nrows, trace_ncolumns);

        let x_square = x * x;
        let x_cubic = x_square.clone() * x;

        trace[(0, 0)] = x.clone();
        trace[(0, 1)] = x_square;
        trace[(1, 0)] = x_cubic.clone();
        trace[(1, 1)] = x_cubic + x + FieldElement::from(5);

        trace
    }
}

macro_rules! run {
    ($x:expr, $y:expr, $ok_or_err_fn:ident) => {{
        let claim = SampleClaim { y: $y.into() };
        let proof = claim.prove(&$x.into());
        assert!(proof.$ok_or_err_fn());
        if let Ok(proof) = proof {
            assert!(claim.verify(&proof).is_ok());
        }
    }};
}

pub fn main() {
    // valid proofs
    run!(1, 7, is_ok);
    run!(3, 35, is_ok);
    run!(5, 135, is_ok);
    // invalid proofs
    run!(1, 8, is_err);
    run!(3, 36, is_err);
    run!(5, 134, is_err);
}
