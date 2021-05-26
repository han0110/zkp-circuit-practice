use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand;

// SampleProof checks whether y = x^3 + x + 5 with committed V = (x, y).
// The linear combination weights in paper's notation will be:
//                            ┌      ┐  ┌     ┐  ┌     ┐  ┌      ┐  ┌    ┐
//                            │ 1  0 │  │ 0 0 │  │ 0 0 │  │  1 0 │  │  0 │
//                            │ 0  0 │  │ 1 0 │  │ 0 0 │  │  1 0 │  │  0 │
// (W_L, W_R, W_O, W_V, c) = (│ 0 -1 │, │ 0 0 │, │ 1 0 │, │  0 0 │, │  0 │)
//                            │ 0  0 │  │ 0 1 │  │ 0 0 │  │  1 0 │  │  0 │
//                            │ 0  0 │  │ 0 0 │  │ 0 1 │  │ -1 1 │  │ -5 │
//                            └      ┘  └     ┘  └     ┘  └      ┘  └    ┘
struct SampleProof(R1CSProof);

impl SampleProof {
    fn gadget<CS: ConstraintSystem>(cs: &mut CS, &x: &Variable, &y: &Variable) {
        let (one, five) = (Scalar::one(), Scalar::from(5u8));

        // x^2 = x * x
        let x_square = cs.multiply(x * one, x * one).2;
        // x^3 = x^2 * x
        let x_cubic = cs.multiply(x_square * one, x * one).2;
        // x^3 + x + 5 - y = 0
        cs.constrain(x_cubic + x + five - y);
    }

    pub fn prove<'a, 'b>(
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        x: &Scalar,
        y: &Scalar,
    ) -> Result<(SampleProof, CompressedRistretto, CompressedRistretto), R1CSError> {
        let mut prover = Prover::new(&pc_gens, transcript);

        let mut blinding_rng = rand::thread_rng();

        let (x_com, x_var) = prover.commit(*x, Scalar::random(&mut blinding_rng));
        let (y_com, y_var) = prover.commit(*y, Scalar::random(&mut blinding_rng));

        SampleProof::gadget(&mut prover, &x_var, &y_var);

        let proof = prover.prove(&bp_gens)?;

        Ok((SampleProof(proof), x_com, y_com))
    }

    pub fn verify<'a, 'b>(
        &self,
        pc_gens: &'b PedersenGens,
        bp_gens: &'b BulletproofGens,
        transcript: &'a mut Transcript,
        x_com: &CompressedRistretto,
        y_com: &CompressedRistretto,
    ) -> Result<(), R1CSError> {
        let mut verifier = Verifier::new(transcript);

        let x_var = verifier.commit(*x_com);
        let y_var = verifier.commit(*y_com);

        SampleProof::gadget(&mut verifier, &x_var, &y_var);

        verifier.verify(&self.0, &pc_gens, &bp_gens)
    }
}

macro_rules! run {
    ($x:expr, $y:expr, $pc_gens:expr, $bp_gens:expr, $ok_or_err_fn:ident) => {{
        let (x, y) = (Scalar::from($x as u64), Scalar::from($y as u64));

        let mut prover_transcript = Transcript::new(b"SampleProof");
        let (proof, x_com, y_com) =
            SampleProof::prove($pc_gens, $bp_gens, &mut prover_transcript, &x, &y).unwrap();

        let mut verifier_transcript = Transcript::new(b"SampleProof");
        assert!(proof
            .verify($pc_gens, $bp_gens, &mut verifier_transcript, &x_com, &y_com)
            .$ok_or_err_fn());
    }};
}

fn main() {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(1 << 3, 1);

    // valid proofs
    run!(1, 7, &pc_gens, &bp_gens, is_ok);
    run!(3, 35, &pc_gens, &bp_gens, is_ok);
    run!(5, 135, &pc_gens, &bp_gens, is_ok);
    // invalid proofs
    run!(1, 8, &pc_gens, &bp_gens, is_err);
    run!(3, 36, &pc_gens, &bp_gens, is_err);
    run!(5, 134, &pc_gens, &bp_gens, is_err);
}
