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

fn example_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    a: LinearCombination,
    b: LinearCombination,
    a_inv: Option<Scalar>,
    b_inv: Option<Scalar>,
    output: Scalar,
) -> Result<(), R1CSError> {
    //新增input转为LinearCombination，约束a*a_inv-1=0
    let var_a_inv = cs.allocate(a_inv)?;
    let a_inv_lc: LinearCombination = var_a_inv.into();
    let (_, _, o1) = cs.multiply(a.clone(), a_inv_lc.clone());
    let one_lc: LinearCombination = LinearCombination::from(Variable::One());
    cs.constrain(o1 - one_lc.clone());

    //新增input转为LinearCombination，约束b*b_inv-1=0
    let var_b_inv = cs.allocate(b_inv)?;
    let b_inv_lc: LinearCombination = var_b_inv.into();
    let (_, _, o2) = cs.multiply(b.clone(), b_inv_lc.clone());
    cs.constrain(o2 - one_lc.clone());

    //let y_lc: LinearCombination = LinearCombination::from(Scalar::from(100u8));
    let y_lc: LinearCombination = LinearCombination::from(output);
    cs.constrain(a_inv_lc + b_inv_lc - y_lc);
    Ok(())
}

#[test]
fn example_test() -> Result<(), R1CSError> {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(128, 1);

    let a = Scalar::from(10u8);
    let b = Scalar::from(20u8);
    let a_inv = a.invert();
    let b_inv = b.invert();
    let output = a_inv+b_inv;
    println!("{:?}", output);

    let (proof, commitments) = {
        let mut prover_transcript = Transcript::new(b"exampleTest");
        let mut rng = rand::thread_rng();

        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);

        let (com, var): (Vec<_>, Vec<_>) = [a, b]
            .into_iter()
            .map(|x| prover.commit(*x, Scalar::random(&mut rng)))
            .unzip();
        
        assert!(example_gadget(&mut prover, var[0].into(), var[1].into(), Some(a_inv), Some(b_inv), output).is_ok());
        let proof = prover.prove(&bp_gens)?;
        (proof, com)
    };

    let mut verifier_transcript = Transcript::new(b"exampleTest");
    let mut verifier = Verifier::new(&mut verifier_transcript);

    let vars: Vec<_> = commitments.iter().map(|V| verifier.commit(*V)).collect();

    assert!(example_gadget(&mut verifier, vars[0].into(), vars[1].into(), None, None, output).is_ok());
    Ok(verifier.verify(&proof, &pc_gens, &bp_gens)?)
}