extern crate bulletproofs;
extern crate curve25519_dalek;
extern crate merlin;
extern crate rand;
extern crate crypto;

use bulletproofs::r1cs::*;
use bulletproofs::{BulletproofGens, PedersenGens};
use curve25519_dalek::ristretto::CompressedRistretto;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::thread_rng;
use std::fmt;
use crypto::sha2::Sha256;
use crypto::digest::Digest;


const V_H: [&str; 8] = 
["6a09e667", "bb67ae85", "3c6ef372", "a54ff53a", "510e527f", "9b05688c", "1f83d9ab", "5be0cd19"];

const V_K: [&str; 64] = 
    ["428a2f98", "71374491", "b5c0fbcf", "e9b5dba5", "3956c25b", "59f111f1", "923f82a4", "ab1c5ed5",
   "d807aa98", "12835b01", "243185be", "550c7dc3", "72be5d74", "80deb1fe", "9bdc06a7", "c19bf174",
   "e49b69c1", "efbe4786", "0fc19dc6", "240ca1cc", "2de92c6f", "4a7484aa", "5cb0a9dc", "76f988da",
   "983e5152", "a831c66d", "b00327c8", "bf597fc7", "c6e00bf3", "d5a79147", "06ca6351", "14292967",
   "27b70a85", "2e1b2138", "4d2c6dfc", "53380d13", "650a7354", "766a0abb", "81c2c92e", "92722c85",
   "a2bfe8a1", "a81a664b", "c24b8b70", "c76c51a3", "d192e819", "d6990624", "f40e3585", "106aa070",
   "19a4c116", "1e376c08", "2748774c", "34b0bcb5", "391c0cb3", "4ed8aa4a", "5b9cca4f", "682e6ff3",
   "748f82ee", "78a5636f", "84c87814", "8cc70208", "90befffa", "a4506ceb", "bef9a3f7", "c67178f2"];

#[derive(Copy, Clone, Debug)]
pub struct AllocatedScalar {
    pub variable: Variable,
    pub assignment: Option<Scalar>
}

type word = Vec<AllocatedScalar>;

fn sha256_v_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    vl: AllocatedScalar,
    vr: AllocatedScalar,
) -> Result<(), R1CSError> {
    let mut l_exp_2 = Scalar::one();
    let mut r_exp_2 = Scalar::one();
    let mut W: Vec<word> = Vec::with_capacity(64);
    let mut vl_lc: LinearCombination = vl.variable.into();
    let mut vr_lc: LinearCombination = vr.variable.into();

    // 将msg转为bit，并生成W[0..16]
    for i in 0..8 {
        
        let mut w: word = Vec::with_capacity(32);
        for j in 0..32 {
            let mut temp: AllocatedScalar = AllocatedScalar {
                variable: Variable::One(),
                assignment: None,
            };
            let (a, b, o) = cs.allocate_multiplier(vl.assignment.map(|q| {
                let bytes = q.as_bytes();
                let bit: u8 = ((bytes[(i*32+j)>>3] >> ((i*32+j)&7)) & 1u8) as u8;

                temp.assignment = Some(Scalar::from(bit));
                ((1-bit).into(), bit.into())
            }))?;
            temp.variable = b;
            w.push(temp);
            cs.constrain(o.into());
            cs.constrain(a+(b-1u8));
            vl_lc = vl_lc - b * l_exp_2;
            l_exp_2 = l_exp_2 + l_exp_2;
        }
        W.push(w);
    }

    for i in 0..8 {
        
        let mut w: word = Vec::with_capacity(32);
        for j in 0..32 {
            let mut temp: AllocatedScalar = AllocatedScalar {
                variable: Variable::One(),
                assignment: None,
            };
            let (a, b, o) = cs.allocate_multiplier(vr.assignment.map(|q| {
                let bytes = q.as_bytes();
                let bit: u8 = ((bytes[(i*32+j)>>3] >> ((i*32+j)&7)) & 1u8) as u8;
                temp.assignment = Some(Scalar::from(bit));
                ((1-bit).into(), bit.into())
            }))?;
            temp.variable = b;
            w.push(temp);
            cs.constrain(o.into());
            cs.constrain(a+(b-1u8));
            vr_lc = vr_lc - b * r_exp_2;
            r_exp_2 = r_exp_2 + r_exp_2;
        }
        W.push(w);
    }
    
    cs.constrain(vl_lc);
    cs.constrain(vr_lc);
    // let a: AllocatedScalar = xor(cs, W[0][1], W[8][1])?;
    // println!("{:?}", a);
    
    // generate W[64]
    for i in 16..64 {
        let sig_1: word = small_sigma(cs, &W[i-2], 17usize, 19usize, 10usize)?;
        let sig_0: word = small_sigma(cs, &W[i-15], 7usize, 18usize, 3usize)?;
        
        let sum_1: word = add(cs, &sig_1, &W[i-7])?;
        let sum_2: word = add(cs, &sum_1, &sig_0)?;
        let out: word = add(cs, &sum_2, &W[i-16])?;
        
        W.push(out);
    }
    //println!("{:?}", W[63]);
    
    // get H,K
    let mut H_I: Vec<word> = Vec::with_capacity(8);
    let mut K_I: Vec<word> = Vec::with_capacity(64);
    for i in 0..8 {
        let s_u: u32 = u32::from_str_radix(V_H[i], 16).unwrap();
        let s: Scalar = Scalar::from(s_u);
        let o_ass: Option<Scalar> = Some(s);
        let o = cs.allocate(o_ass)?;
        let out: AllocatedScalar = AllocatedScalar {
            variable: o,
            assignment: o_ass,
        };
        let out_vec: word = to_bits(cs, out, 32usize)?;
        H_I.push(out_vec);
    }
    for i in 0..64 {
        let s_u: u32 = u32::from_str_radix(V_K[i], 16).unwrap();
        let s: Scalar = Scalar::from(s_u);
        let o_ass: Option<Scalar> = Some(s);
        let o = cs.allocate(o_ass)?;
        let out: AllocatedScalar = AllocatedScalar {
            variable: o,
            assignment: o_ass,
        };
        let out_vec: word = to_bits(cs, out, 32usize)?;
        K_I.push(out_vec);
    }

    //start
    let mut a: word = H_I[0].clone();
    let mut b: word = H_I[1].clone();
    let mut c: word = H_I[2].clone();
    let mut d: word = H_I[3].clone();
    let mut e: word = H_I[4].clone();
    let mut f: word = H_I[5].clone();
    let mut g: word = H_I[6].clone();
    let mut h: word = H_I[7].clone();

    for i in 0..64 {
        let s_a: word = big_sigma(cs, &a, 2usize, 13usize, 22usize)?;
        let ma_a_b_c: word = MA(cs, &a, &b, &c)?;
        let t_2: word = add(cs, &s_a, &ma_a_b_c)?;

        let s_e: word = big_sigma(cs, &e, 6usize, 11usize, 25usize)?;
        let ch_e_f_g: word = CH(cs, &e, &f, &g)?;
        let t_1_1: word = add(cs, &h, &s_e)?;
        let t_1_2: word = add(cs, &t_1_1, &ch_e_f_g)?;
        let t_1_3: word = add(cs, &t_1_2, &K_I[i])?;
        let t_1: word = add(cs, &t_1_3, &W[i])?;

        h = g.clone();
        g = f.clone();
        f = e.clone();
        e = add(cs, &d, &t_1)?;
        d = c.clone();
        c = b.clone();
        b = a.clone();
        a = add(cs, &t_1, &t_2)?;
    }

    H_I[0] = add(cs, &H_I[0], &a)?;
    H_I[1] = add(cs, &H_I[1], &b)?;
    H_I[2] = add(cs, &H_I[2], &c)?;
    H_I[3] = add(cs, &H_I[3], &d)?;
    H_I[4] = add(cs, &H_I[4], &e)?;
    H_I[5] = add(cs, &H_I[5], &f)?;
    H_I[6] = add(cs, &H_I[6], &g)?;
    H_I[7] = add(cs, &H_I[7], &h)?;
    println!("{:?}", H_I[0]);




    Ok(())
}

fn xor<CS: ConstraintSystem>(
    cs: &mut CS,
    a: AllocatedScalar,
    b: AllocatedScalar
) -> Result<AllocatedScalar, R1CSError> {
    // generate r1cs witness
    
    let tmp_assignment: Option<Scalar> = a.assignment.map(|p| {
        let mut t: Scalar = Scalar::zero();
        b.assignment.map(|q| {
            let y: Scalar = Scalar::from(2u8) * p;
            t = p + q - y * q;
        });
        t
    });

    // generate r1cs constarint
    let tmp: Variable = cs.allocate(tmp_assignment)?;
    let (_, _, a_b) = cs.multiply(a.variable.into(), b.variable.into());
    let two_a_b: LinearCombination = vec![(a_b, Scalar::from(2u8))].iter().collect();
    cs.constrain(a.variable + b.variable - two_a_b - tmp);

    
    let tmp_alloc: AllocatedScalar = AllocatedScalar {
        variable: tmp,
        assignment: tmp_assignment,
    };
    Ok(tmp_alloc)
}

fn xor_3<CS: ConstraintSystem>(
    cs: &mut CS,
    a: AllocatedScalar,
    b: AllocatedScalar,
    c: AllocatedScalar
) -> Result<AllocatedScalar, R1CSError> {
    // generate r1cs witness
    
    
    let tmp_assignment: Option<Scalar> = a.assignment.map(|p| {
        let mut t: Scalar = Scalar::zero();
        b.assignment.map(|q| {
            let y: Scalar = Scalar::from(2u8) * p;
            t = p + q - y * q;
        });
        t
    });
    // out = tmp xor c
    // let mut 2t_c: Option<(Scalar, Scalar)> = None;
    let out_assignment: Option<Scalar> = tmp_assignment.map(|p| {
        let mut t: Scalar = Scalar::zero();
        c.assignment.map(|q| {
            let y: Scalar = Scalar::from(2u8) * p;
            t = p + q - y * q;
        });
        t
    });

    // generate r1cs constarint
    let tmp: Variable = cs.allocate(tmp_assignment)?;
    let (_, _, a_b) = cs.multiply(a.variable.into(), b.variable.into());
    let two_a_b: LinearCombination = vec![(a_b, Scalar::from(2u8))].iter().collect();
    cs.constrain(a.variable + b.variable - two_a_b - tmp);

    let out: Variable = cs.allocate(out_assignment)?;
    let (_, _, t_c) = cs.multiply(tmp.into(), c.variable.into());
    let two_t_c: LinearCombination = vec![(t_c, Scalar::from(2u8))].iter().collect();
    cs.constrain(tmp + c.variable - two_t_c - out);

    
    let out_alloc: AllocatedScalar = AllocatedScalar {
        variable: out,
        assignment: out_assignment,
    };
    Ok(out_alloc)
}

fn and<CS: ConstraintSystem>(
    cs: &mut CS,
    a: AllocatedScalar,
    b: AllocatedScalar
) -> Result<AllocatedScalar, R1CSError> {
    // generate r1cs witness of a AND b
        let a_mul_b_assignment: Option<Scalar> = a.assignment.map(|q| {
            let mut t: Scalar = Scalar::zero();
            b.assignment.map(|p| {
                t = q * p;
            });
            t
        });
        // generate r1cs constraint of a AND b
        let a_mul_b: Variable = cs.allocate(a_mul_b_assignment)?;
        let (_, _, a_b) = cs.multiply(a.variable.into(), b.variable.into());
        cs.constrain(a_b - a_mul_b);

        let a_mul_b_alloc: AllocatedScalar = AllocatedScalar {
            variable: a_mul_b,
            assignment: a_mul_b_assignment,
        };
    Ok(a_mul_b_alloc)
}

fn naab<CS: ConstraintSystem>(
    cs: &mut CS,
    a: AllocatedScalar,
    c: AllocatedScalar
) -> Result<AllocatedScalar, R1CSError> {
        // generate r1cs witness of a NAAB b
        let a_naab_c_assignment: Option<Scalar> = a.assignment.map(|q| {
            let mut t: Scalar = Scalar::zero();
            c.assignment.map(|p| {
                t = (Scalar::one() - q) * p;
            });
            t
        });
        // generate r1cs constraint of a NAAB b
        let a_naab_c: Variable = cs.allocate(a_naab_c_assignment)?;
        let (_, _, a_c) = cs.multiply((Variable::One() - a.variable), c.variable.into());
        cs.constrain(a_c - a_naab_c);

        let a_naab_c_alloc: AllocatedScalar = AllocatedScalar {
            variable: a_naab_c,
            assignment: a_naab_c_assignment,
        };

        Ok(a_naab_c_alloc)
}

fn CH<CS: ConstraintSystem>(
    cs: &mut CS,
    a: &word,
    b: &word,
    c: &word
) -> Result<word, R1CSError> {
    let mut out_vec: word = Vec::with_capacity(32);
    for i in 0..32 {
        let temp_1: AllocatedScalar = and(cs, a[i], b[i])?;
        let temp_2: AllocatedScalar = naab(cs, a[i], c[i])?;
        let temp_out: AllocatedScalar = xor(cs, temp_1, temp_2)?;
        out_vec.push(temp_out);
    }
    
    Ok(out_vec)
}

fn MA<CS: ConstraintSystem>(
    cs: &mut CS,
    a: &word,
    b: &word,
    c: &word,
) -> Result<word, R1CSError> {
    let mut out_vec: word = Vec::with_capacity(32);
    for i in 0..32 {
        let temp_1: AllocatedScalar = and(cs, a[i], b[i])?;
        let temp_2: AllocatedScalar = and(cs, a[i], c[i])?;
        let temp_3: AllocatedScalar = and(cs, b[i], c[i])?;
        let temp_4: AllocatedScalar = xor(cs, temp_1, temp_2)?;
        let temp_out: AllocatedScalar = xor(cs, temp_4, temp_3)?;
        out_vec.push(temp_out);
    }
    
    Ok(out_vec)
}

// 右移n位
fn word_r_n<CS: ConstraintSystem>(cs: &mut CS, l: &word, n: usize) -> Result<word, R1CSError> {
    let mut out: word = Vec::with_capacity(32);
    out.extend(l[n..].iter().clone());
    for i in 0..n {
        let ass: Option<Scalar> = l[i].assignment.map(|q| Scalar::zero());
        let o = cs.allocate(ass)?;
        let t: AllocatedScalar = AllocatedScalar {
            variable: o,
            assignment: ass,
        };
        out.push(t);
    }
    Ok(out)
}

// 循环右移n位
fn word_s_n<CS: ConstraintSystem>(cs: &mut CS, l: &word, n: usize) -> Result<word, R1CSError> {
    let mut out: word = Vec::with_capacity(32);
    out.extend(l[n..].iter().clone());
    out.extend(l[..n].iter().clone());
    Ok(out)
}
fn small_sigma<CS: ConstraintSystem>(
    cs: &mut CS,
    x: &word,
    // y: AllocatedScalar
    rot1: usize,
    rot2: usize,
    shift: usize,
) -> Result<word, R1CSError> {
    //let x: word = to_bits(cs, y, 32usize)
    let t: Option<Scalar> = x[0].assignment.map(|q| Scalar::zero());
    let zero: AllocatedScalar = AllocatedScalar{
        variable: Variable::One(),
        assignment: t
    };

    let mut out_vec: word = Vec::with_capacity(32);
    let a: word = word_s_n(cs, x, rot1)?;
    let b: word = word_s_n(cs, x, rot2)?;
    let c: word = word_r_n(cs, x, shift)?;


    for i in 0usize..32usize {
        
        let temp_out: AllocatedScalar = xor_3(
            cs,
            a[i],
            b[i],
            c[i],
        )?;
        out_vec.push(temp_out);
    }
    
    Ok(out_vec)

}

fn big_sigma<CS: ConstraintSystem>(
    cs: &mut CS,
    x: &word,
    rot1: usize,
    rot2: usize,
    rot3: usize,
) -> Result<word, R1CSError> {
    // let t: Option<Scalar> = x[0].assignment.map(|q| 0);
    // let zero: AllocatedScalar = AllocatedScalar{
    //     variable: Variable::One(),
    //     assignment: t
    // };

    let mut out_vec: word = Vec::with_capacity(32);

    for i in 0usize..32usize {
        
        let temp_out: AllocatedScalar = xor_3(
            cs,
            x[(i+rot1)%32usize],
            x[(i+rot2)%32usize],
            x[(i+rot3)%32usize],
        )?;
        out_vec.push(temp_out);
    }
    
    Ok(out_vec)

}

fn from_32bits<CS: ConstraintSystem>(cs: &mut CS, x: &word) -> Result<AllocatedScalar, R1CSError> {
    let mut exp_2 = Scalar::one();
    let mut sum = Scalar::zero();
    let mut out_assignment: Option<Scalar> = None;
    let mut l_sum: LinearCombination = LinearCombination::from(Scalar::zero());

    
    for i in 0..32 {
        // generate r1cs witness
        out_assignment = x[i].assignment.map(|q| {
            sum = sum + q * exp_2;
            sum
        });

        // generate every LinearCombination
        let l: LinearCombination = vec![(x[i].variable, Scalar::from(exp_2))].iter().collect();
        l_sum = l_sum + l;

        exp_2 = exp_2 + exp_2;
    }
    // generate r1cs constraint
    let out: Variable = cs.allocate(out_assignment)?;
    cs.constrain(l_sum - out);

    let out_alloc: AllocatedScalar = AllocatedScalar{
        variable: out,
        assignment: out_assignment,
    };
    Ok(out_alloc)
}

fn to_bits<CS: ConstraintSystem>(cs: &mut CS, x: AllocatedScalar, n: usize) -> Result<Vec<AllocatedScalar>, R1CSError> {
    let mut w: Vec<AllocatedScalar> = Vec::new();
    let mut x_lc: LinearCombination = LinearCombination::from(x.variable);
    let mut exp_2 = Scalar::one();
    for j in 0..n {
        let mut tmp_assignment: Option<Scalar> = None;
            
        let (a, b, o) = cs.allocate_multiplier(x.assignment.map(|q| {
            let bytes = q.as_bytes();
            let bit: u8 = ((bytes[j>>3] >> (j&7)) & 1u8) as u8;
            tmp_assignment = Some(Scalar::from(bit));
            ((1-bit).into(), bit.into())
        }))?;
        let tmp: AllocatedScalar = AllocatedScalar {
            variable: b,
            assignment: tmp_assignment,
        };
        w.push(tmp);
        cs.constrain(o.into());
        cs.constrain(a+(b-1u8));
        x_lc = x_lc - b * exp_2;
        exp_2 = exp_2 + exp_2;
    }
    cs.constrain(x_lc);
    Ok(w)
}

fn add<CS: ConstraintSystem>(
    cs: &mut CS,
    l: &word,
    r: &word,
) -> Result<word, R1CSError> {
    let a: AllocatedScalar = from_32bits(cs, l)?;
    let b: AllocatedScalar = from_32bits(cs, r)?;

    let mut c_ass: Option<Scalar> = None;
    let o_ass: Option<Scalar> = a.assignment.map(|x| {
        let mut  t = Scalar::default();
        c_ass = b.assignment.map(|y| {
            let c: Scalar = x + y;
            let mut bytes: [u8; 32] = [0u8; 32];
            for i in 0..4 {
                bytes[i] = c.as_bytes()[i];
            }
            t  = Scalar::from_bits(bytes);
            c
        });
        t
    });

    let o: Variable = cs.allocate(o_ass)?;
    let c: Variable = cs.allocate(c_ass)?;

    let out: AllocatedScalar = AllocatedScalar {
        variable: o,
        assignment: o_ass,
    };
    let com: AllocatedScalar = AllocatedScalar {
        variable: c,
        assignment: c_ass,
    };

    let out_bits: Vec<AllocatedScalar> = to_bits(cs, out, 32usize)?;
    let com_bits: Vec<AllocatedScalar> = to_bits(cs, com, 33usize)?;
    for i in 0..32 {
        cs.constrain(out_bits[i].variable - com_bits[i].variable);
    }
    
    
    Ok(out_bits)
}

#[test]
#[ignore]
fn test_sha256() -> Result<(), R1CSError> {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(50000, 1);

    //let mut rng = thread_rng();

    let v_l = Scalar::from(2u32);
    let v_r = Scalar::from(4u32);
    //let v_r = Scalar::random(&mut rng);
    // println!("{:?}", v_l);
    // println!("{:?}", v_r);

    // let vl_bytes: [u8; 32] = v_l.to_bytes();
    // let vr_bytes: [u8; 32] = v_r.to_bytes();
    // let mut v_bytes: Vec<u8> = Vec::new();
    // for i in 0..32 {
    //     v_bytes.push(vl_bytes[i]);
    // }
    // for i in 0..32 {
    //     v_bytes.push(vr_bytes[i]);
    // }
    // println!("{:?}", v_bytes.len());

    // let mut hasher = Sha256::new();
    // hasher.input(&v_bytes);
    // let mut ou: [u8; 32] = [0; 32];
    // hasher.result(&mut ou);
    // println!("{:?}", ou);

    //let image: Scalar = Scalar::from_bytes_mod_order(ou);



    let (proof, commitments): (R1CSProof, Vec<CompressedRistretto>) = {
        let mut prover_transcript = Transcript::new(b"SHA256Test");
        let mut rng = thread_rng();

        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);
        let (com, var): (Vec<_>, Vec<_>) = [v_l, v_r]
            .into_iter()
            .map(|x| prover.commit(*x, Scalar::random(&mut rng)))
            .unzip();
        
        let alloc_vl: AllocatedScalar = AllocatedScalar{
            variable: var[0],
            assignment: Some(v_l),
        };
        let alloc_vr: AllocatedScalar = AllocatedScalar{
            variable: var[1],
            assignment: Some(v_r),
        };
        assert!(sha256_v_gadget(&mut prover, alloc_vl, alloc_vr).is_ok());
        let proof = prover.prove(&bp_gens)?;
        

        (proof, com)
    };

    let mut verifier_transcript = Transcript::new(b"SHA256Test");
    let mut verifier = Verifier::new(&mut verifier_transcript);

    let vars: Vec<_> = commitments.iter().map(|V| verifier.commit(*V)).collect();
    let alloc_vl: AllocatedScalar = AllocatedScalar{
            variable: vars[0],
            assignment: None,
    };
    let alloc_vr: AllocatedScalar = AllocatedScalar{
            variable: vars[1],
            assignment: None,
    };
    assert!(sha256_v_gadget(&mut verifier, alloc_vl, alloc_vr).is_ok());

    Ok(verifier.verify(&proof, &pc_gens, &bp_gens)?)
}

#[test]
fn test_gadget() -> Result<(), R1CSError> {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(131072, 1);

    //let mut rng = thread_rng();

    let v_l = Scalar::from(4294967295u32);
    let v_r = Scalar::from(4u32);
   
 


    let (proof, commitments): (R1CSProof, Vec<CompressedRistretto>) = {
        let mut prover_transcript = Transcript::new(b"SHA256Test");
        let mut rng = thread_rng();

        let mut prover = Prover::new(&pc_gens, &mut prover_transcript);
        let (com, var): (Vec<_>, Vec<_>) = [v_l, v_r]
            .into_iter()
            .map(|x| prover.commit(*x, Scalar::random(&mut rng)))
            .unzip();
        
        let alloc_vl: AllocatedScalar = AllocatedScalar{
            variable: var[0],
            assignment: Some(v_l),
        };
        let alloc_vr: AllocatedScalar = AllocatedScalar{
            variable: var[1],
            assignment: Some(v_r),
        };
        assert!(sha256_v_gadget(&mut prover, alloc_vl, alloc_vr).is_ok());
        let proof = prover.prove(&bp_gens)?;
        

        (proof, com)
    };

    let mut verifier_transcript = Transcript::new(b"SHA256Test");
    let mut verifier = Verifier::new(&mut verifier_transcript);

    let vars: Vec<_> = commitments.iter().map(|V| verifier.commit(*V)).collect();
    let alloc_vl: AllocatedScalar = AllocatedScalar{
            variable: vars[0],
            assignment: None,
    };
    let alloc_vr: AllocatedScalar = AllocatedScalar{
            variable: vars[1],
            assignment: None,
    };
    assert!(sha256_v_gadget(&mut verifier, alloc_vl, alloc_vr).is_ok());

    Ok(verifier.verify(&proof, &pc_gens, &bp_gens)?)
}