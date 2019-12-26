extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;

use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::thread_rng;


fn is_zero_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    x: LinearCombination,
    x_inv: Option<Scalar>,
) -> Result<(), R1CSError> {
    let avr_x_inv = cs.allocate(x_inv)?;
    let x_inv_lc: LinearCombination = avr_x_inv.into();
    let (_, _, o1) = cs.multiply(x.clone(), x_inv_lc);

    let y_lc = LinearCombination::from(Scalar::one());
    let y_minus_one_lc: LinearCombination = LinearCombination::from(Variable::One()) - y_lc.clone();

    cs.constrain(o1 - y_lc);

    
    let (_, _, o2) = cs.multiply(x.clone(), y_minus_one_lc);

    cs.constrain(o2.into());
    Ok(())
}
// #[test]
fn is_zero_test() -> Result<(), R1CSError> {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);

    let x = Scalar::from(100u64);
    let x_inv = x.invert();

    let (proof, commitment) = {
        let mut prover_transcript = Transcript::new(b"is_zeroTest");
        let mut rng = rand::thread_rng();

        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let (com, var) = prover.commit(x, Scalar::random(&mut rng));
        assert!(is_zero_gadget(&mut prover, var.into(), Some(x_inv)).is_ok());
        let proof = prover.prove(&bp_gens)?;
        (proof, com)
    };

    let mut verifier_transcript = Transcript::new(b"is_zeroTest");
    let mut verifier = Verifier::new(&mut verifier_transcript);

    let var = verifier.commit(commitment);
    assert!(is_zero_gadget(&mut verifier, var.into(), None).is_ok());
    Ok(verifier.verify(&proof, &pc_gens, &bp_gens)?)
}

#[test]
    fn test_bit() {
        let msg = Scalar::from(10u64);
        let var = Some(msg);
        let mut count = 0u64;
        println!("{:?}", msg);
        var.map(|q| {
            for t in q.as_bytes() {
                for j in 0..8 {
                    let bit: u8 = (t>>j) & 1u8;
                    print!("{:?}", bit);
                    count = count + 1;
                }
            }            
        });
        println!("{:?}", count);

        let x: u8 = 1;
        let y: u8 = match x>1 {
            true => 21,
            false => 20,
        };
        println!("{:?}", y);
            
    }