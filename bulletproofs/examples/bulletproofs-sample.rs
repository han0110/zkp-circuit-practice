use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand;

// SampleProof checks whether y = x^3 + x + 5
struct SampleProof(R1CSProof);

impl SampleProof {
    fn gadget<CS: ConstraintSystem>(cs: &mut CS, &x: &Variable, &y: &Variable) {
        let (one, five) = (Scalar::one(), Scalar::from(5u32));

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

fn main() {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(1 << 3, 1);

    // valid proof
    {
        let (x, y) = (Scalar::from(3u64), Scalar::from(35u64));

        let (proof, input_commitments, output_commitments) = {
            let mut prover_transcript = Transcript::new(b"SampleProof");
            SampleProof::prove(&pc_gens, &bp_gens, &mut prover_transcript, &x, &y).unwrap()
        };

        let mut verifier_transcript = Transcript::new(b"SampleProof");
        assert!(proof
            .verify(
                &pc_gens,
                &bp_gens,
                &mut verifier_transcript,
                &input_commitments,
                &output_commitments
            )
            .is_ok());
    }

    // invalid proof
    {
        let (x, y) = (Scalar::from(3u64), Scalar::from(10u64));

        let (proof, input_commitments, output_commitments) = {
            let mut prover_transcript = Transcript::new(b"SampleProof");
            SampleProof::prove(&pc_gens, &bp_gens, &mut prover_transcript, &x, &y).unwrap()
        };

        let mut verifier_transcript = Transcript::new(b"SampleProof");
        assert!(proof
            .verify(
                &pc_gens,
                &bp_gens,
                &mut verifier_transcript,
                &input_commitments,
                &output_commitments
            )
            .is_err());
    }
}
