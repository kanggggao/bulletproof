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



pub mod scalar_utils {
    use super::*;
    pub struct ScalarBits {
    pub bit_array: Vec<u8>
    }

    impl fmt::Debug for ScalarBits {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{:?}", self.bit_array)
        }
    }

    impl ScalarBits {
        pub fn from_scalar(scalar: &Scalar, process_bits: usize) -> Self {
            let s = scalar.reduce();
            Self {
                bit_array: get_bits(&s, process_bits)
            }
        }

        pub fn to_scalar(&self) -> Scalar {
            self.to_non_reduced_scalar().reduce()
        }

        pub fn to_non_reduced_scalar(&self) -> Scalar {
            let mut bytes: [u8; 32] = [0; 32];
            let powers_of_2: [u8; 8] = [1, 2, 4, 8, 16, 32, 64, 128];
            let mut i = 0;
            let mut current_byte = 0u8;
            for b in self.bit_array.iter() {
                if *b == 1 {
                    current_byte += powers_of_2[i % 8];
                }
                i += 1;
                if (i % 8) == 0 {
                    bytes[(i / 8) - 1] = current_byte;
                    current_byte = 0;
                }
            }
            bytes[31] = current_byte;
            Scalar::from_bits(bytes)
        }
    }

    pub fn get_bits(scalar: &Scalar, process_bits: usize) -> Vec<u8> {
        let mut bits = vec![0u8; process_bits];
        let bytes = scalar.as_bytes();
        for i in 0..process_bits {
            // As i runs from 0..256, the bottom 3 bits index the bit,
            // while the upper bits index the byte.
            bits[i] = ((bytes[i>>3] >> (i&7)) & 1u8) as u8;
        }
        bits
    }

}


#[derive(Copy, Clone, Debug)]
pub struct AllocatedScalar {
    pub variable: Variable,
    pub assignment: Option<Scalar>
}

type word = Vec<AllocatedScalar>;

fn sha256_gadget<CS: ConstraintSystem>(
    cs: &mut CS,
    vl: AllocatedScalar,
    vr: AllocatedScalar,
) -> Result<(), R1CSError> {
    let mut l_exp_2 = Scalar::one();
    let mut r_exp_2 = Scalar::one();
    let mut W: Vec<AllocatedScalar> = Vec::with_capacity(64);
    let mut vl_lc: LinearCombination = vl.variable.into();
    let mut vr_lc: LinearCombination = vr.variable.into();

    // 将msg转为bit，并生成W[0..16]
    for i in 0..8 {
        let mut temp: AllocatedScalar = AllocatedScalar {
            variable: Variable::One(),
            assignment: None,
        };
        let mut w: word = Vec::with_capacity(32);
        for j in 0..32 {
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
        let w_a: AllocatedScalar = from_32bits(cs, &w)?;
        W.push(w_a);
    }

    for i in 0..8 {
        let mut temp: AllocatedScalar = AllocatedScalar {
            variable: Variable::One(),
            assignment: None,
        };
        let mut w: word = Vec::with_capacity(32);
        for j in 0..32 {
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
        let w_a: AllocatedScalar = from_32bits(cs, &w)?;
        W.push(w_a);
    }
    cs.constrain(vl_lc);
    cs.constrain(vr_lc);
    
    //let out: word = word_s_n(cs, &W[0], 5)?;
    
    
    // 生成其他W[16..64], Wt = sigma1(Wt-2) + Wt-7 + sigma0(Wt-15) + Wt-16
    for i in 16..64 {
        let s_w_t_2: AllocatedScalar = sigma1(cs, W[i-2])?;

        let s_w_t_15: AllocatedScalar = sigma0(cs, W[i-15])?;

        let temp_1: AllocatedScalar = all_add(cs, s_w_t_2, W[i-7])?;
        let temp_2: AllocatedScalar = all_add(cs, temp_1, s_w_t_15)?;
        let out: AllocatedScalar = all_add(cs, temp_2, W[i-16])?;
        
        W.push(out);

    }
    //println!("{:?}", W[0]);

    // get H,K
    let mut H_I: Vec<AllocatedScalar> = Vec::with_capacity(8);
    let mut K_I: Vec<AllocatedScalar> = Vec::with_capacity(64);
    for i in 0..8 {
        let s_u: u32 = u32::from_str_radix(V_H[i], 16).unwrap();
        let s: Scalar = Scalar::from(s_u);
        let o_ass: Option<Scalar> = Some(s);
        let o = cs.allocate(o_ass)?;
        let out: AllocatedScalar = AllocatedScalar {
            variable: o,
            assignment: o_ass,
        };
        H_I.push(out);
    }
    for i in 0..2 {
        let s_u: u32 = u32::from_str_radix(V_K[i], 16).unwrap();
        let s: Scalar = Scalar::from(s_u);
        let o_ass: Option<Scalar> = Some(s);
        let o = cs.allocate(o_ass)?;
        let out: AllocatedScalar = AllocatedScalar {
            variable: o,
            assignment: o_ass,
        };
        K_I.push(out);
    }

    let mut a: AllocatedScalar = H_I[0].clone();
    let mut b: AllocatedScalar = H_I[1].clone();
    let mut c: AllocatedScalar = H_I[2].clone();
    let mut d: AllocatedScalar = H_I[3].clone();
    let mut e: AllocatedScalar = H_I[4].clone();
    let mut f: AllocatedScalar = H_I[5].clone();
    let mut g: AllocatedScalar = H_I[6].clone();
    let mut h: AllocatedScalar = H_I[7].clone();

    for i in 0..2 {
        let s_0_a: AllocatedScalar = Sigma0(cs, a)?;
        let ma_a_b_c: AllocatedScalar = MA(cs, a, b, c)?;
        let t_2: AllocatedScalar = all_add(cs, s_0_a, ma_a_b_c)?;

        let s_1_e: AllocatedScalar = Sigma1(cs, e)?;
        let ch_e_f_g: AllocatedScalar = CH(cs, e, f, g)?;
        let temp_1: AllocatedScalar = all_add(cs, h, s_1_e)?;
        let temp_2: AllocatedScalar = all_add(cs, temp_1, ch_e_f_g)?;
        let temp_3: AllocatedScalar = all_add(cs, temp_2, K_I[i])?;
        let t_1: AllocatedScalar = all_add(cs, temp_3, W[i])?;

        h = g;
        g = f;
        f = e;
        e = all_add(cs, d, t_1)?;
        d = c;
        c = b;
        b = a;
        a = all_add(cs, t_1, t_2)?;
    }

    let h_0: AllocatedScalar = all_add(cs, H_I[0], a)?;
    let h_1: AllocatedScalar = all_add(cs, H_I[1], b)?;
    let h_2: AllocatedScalar = all_add(cs, H_I[2], c)?;
    let h_3: AllocatedScalar = all_add(cs, H_I[3], d)?;
    let h_4: AllocatedScalar = all_add(cs, H_I[4], e)?;
    let h_5: AllocatedScalar = all_add(cs, H_I[5], f)?;
    let h_6: AllocatedScalar = all_add(cs, H_I[6], g)?;
    let h_7: AllocatedScalar = all_add(cs, H_I[7], h)?;

    //println!("{:?}", h_7);
    let mut h_bits: Vec<word> = Vec::new();
    h_bits.push(to_32bits(cs, h_0)?);
    h_bits.push(to_32bits(cs, h_1)?);
    h_bits.push(to_32bits(cs, h_2)?);
    h_bits.push(to_32bits(cs, h_3)?);
    h_bits.push(to_32bits(cs, h_4)?);
    h_bits.push(to_32bits(cs, h_5)?);
    h_bits.push(to_32bits(cs, h_6)?);
    h_bits.push(to_32bits(cs, h_7)?);


    let mut sha_lc: Vec<LinearCombination> = Vec::new();
    for i in 0..8 {
        for j in 0..32 {
            let bit_lc: LinearCombination = h_bits[i][j].variable.into();
            sha_lc.push(bit_lc);
        }
    }
    println!("{:?}", sha_lc);

    


    Ok(())
}

fn all_and<CS: ConstraintSystem>(
    cs: &mut CS,
    l: AllocatedScalar,
    r: AllocatedScalar
) -> Result<AllocatedScalar, R1CSError> {
    let mut tup: Option<(Scalar, Scalar)> = None;
    let out_assignment: Option<Scalar> = l.assignment.map(|p| {
        let mut t: Scalar = Scalar::zero();
        tup = r.assignment.map(|q| {
            t = p * q;
            (p, q)
        });
        t
    });

    let (_, _, o) = cs.allocate_multiplier(tup)?;
    
    let out: AllocatedScalar = AllocatedScalar {
        variable: o,
        assignment: out_assignment,
    };
    Ok(out)
}


fn all_xor_3<CS: ConstraintSystem>(
    cs: &mut CS,
    a: AllocatedScalar,
    b: AllocatedScalar,
    c: AllocatedScalar
) -> Result<AllocatedScalar, R1CSError> {
    // generate r1cs witness

    // tmp = a xor b
    let mut 2a_b: Option<(Scalar, Scalar)> = None;
    
    let tmp_assignment: Option<Scalar> = a.assignment.map(|p| {
        let mut t: Scalar = Scalar::zero();
        2a_b = b.assignment.map(|q| {
            let y: Scalar = Scalar::from(2u8) * p;
            t = p + q - y * q;
            (y, q)
        });
        t
    });
    // out = tmp xor c
    let mut 2t_c: Option<(Scalar, Scalar)> = None;
    let out_assignment: Option<Scalar> = tmp.assignment.map(|p| {
        let mut t: Scalar = Scalar::zero();
        2t_c = c.assignment.map(|q| {
            let y: Scalar = Scalar::from(2u8) * p;
            t = p + q - y * q;
            (y, q)
        });
        t
    });

    // generate r1cs constarint
    let tmp: Variable = cs.allocate(tmp_assignment)?;
    let (_, _, a_b) = cs.multiply(a, b);
    let 2_a_b: LinearCombination = vec![(a_b, Scalar::from(2u8))].iter().collect();
    cs.constrain(a + b - 2_a_b - tmp);

    let out: Variable = cs.allocate(out_assignment)?;
    let (_, _, t_c) = cs.multiply(tmp, c);
    let 2_t_c: LinearCombination = vec![(t_c, Scalar::from(2u8))].iter().collect();
    cs.constrain(t + c - 2_t_c - out);

    
    let out_alloc: AllocatedScalar = AllocatedScalar {
        variable: out,
        assignment: out_assignment,
    };
    Ok(out_alloc)
}

fn all_naab<CS: ConstraintSystem>(
    cs: &mut CS,
    l: AllocatedScalar,
    r: AllocatedScalar
) -> Result<AllocatedScalar, R1CSError> {
    let mut tup: Option<(Scalar, Scalar)> = None;
    let out_assignment: Option<Scalar> = l.assignment.map(|p| {
        let mut t: Scalar = Scalar::zero();
        tup = r.assignment.map(|q| {
            t = q - p * q;
            (p, q)
        });
        t
    });

    let (_, b, a_mul_b) = cs.allocate_multiplier(tup)?;
    let (_, _, o) = cs.multiply((b - a_mul_b), LinearCombination::from(Scalar::one()));

    let out: AllocatedScalar = AllocatedScalar {
        variable: o,
        assignment: out_assignment,
    };
    Ok(out)
}

// AND
fn word_and<CS: ConstraintSystem>(cs: &mut CS, l: &word, r: &word) -> Result<word, R1CSError> {
    let mut out: word = Vec::with_capacity(32);

    for i in 0..32 {
        let o: AllocatedScalar = all_and(cs, l[i], r[i])?;
        out.push(o)
    }
    Ok(out)

}

// XOR
fn word_xor<CS: ConstraintSystem>(cs: &mut CS, l: &word, r: &word) -> Result<word, R1CSError> {
    let mut out: word = Vec::with_capacity(32);

    for i in 0..32 {
        let o: AllocatedScalar = all_xor(cs, l[i], r[i])?;
        out.push(o)
    }
    Ok(out)

}

// NAAB
fn word_naab<CS: ConstraintSystem>(cs: &mut CS, l: &word, r: &word) -> Result<word, R1CSError> {
    let mut out: word = Vec::with_capacity(32);

    for i in 0..32 {
        let o: AllocatedScalar = all_naab(cs, l[i], r[i])?;
        out.push(o)
    }
    Ok(out)

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

// CH = (x AND y) XOR (NOTx AND z)
fn CH<CS: ConstraintSystem>(cs: &mut CS, a: AllocatedScalar, b: AllocatedScalar, c: AllocatedScalar) -> Result<AllocatedScalar, R1CSError> {
    let x: word = to_32bits(cs, a)?;
    let y: word = to_32bits(cs, b)?;
    let z: word = to_32bits(cs, c)?;
    let x_and_y = word_and(cs, &x, &y)?;
    let not_x_and_z = word_naab(cs, &x, &z)?;
    let temp = word_xor(cs, &x_and_y, &not_x_and_z)?;
    let out: AllocatedScalar = from_32bits(cs, &temp)?;
    Ok(out)
}

// MA = (x AND y) XOR (x AND z) XOR (y AND z)
fn MA<CS: ConstraintSystem>(cs: &mut CS, a: AllocatedScalar, b: AllocatedScalar, c: AllocatedScalar) -> Result<AllocatedScalar, R1CSError> {
    let x: word = to_32bits(cs, a)?;
    let y: word = to_32bits(cs, b)?;
    let z: word = to_32bits(cs, c)?;

    let x_and_y = word_and(cs, &x, &y)?;
    let x_and_z = word_and(cs, &x, &z)?;
    let y_and_z = word_and(cs, &y, &z)?;
    let temp_1 = word_xor(cs, &x_and_y, &x_and_z)?;
    let temp = word_xor(cs, &temp_1, &y_and_z)?;

    let out: AllocatedScalar = from_32bits(cs, &temp)?;
    Ok(out)
}

// Sigma0 = s2 XOR s13 XOR s22
fn Sigma0<CS: ConstraintSystem>(cs: &mut CS, a: AllocatedScalar) -> Result<AllocatedScalar, R1CSError> {
    let x: word = to_32bits(cs, a)?;
    let s_2 = word_s_n(cs, &x, 2)?;
    let s_13 = word_s_n(cs, &x, 13)?;
    let s_22 = word_s_n(cs, &x, 22)?;

    let temp_1 = word_xor(cs, &s_2, &s_13)?;
    let temp = word_xor(cs, &temp_1, &s_22)?;
    let out: AllocatedScalar = from_32bits(cs, &temp)?;
    
    Ok(out)
}
// Sigma1 = s6 XOR s11 XOR s25
fn Sigma1<CS: ConstraintSystem>(cs: &mut CS, a: AllocatedScalar) -> Result<AllocatedScalar, R1CSError> {
    let x: word = to_32bits(cs, a)?;

    let s_6 = word_s_n(cs, &x, 6)?;
    let s_11 = word_s_n(cs, &x, 11)?;
    let s_25 = word_s_n(cs, &x, 25)?;

    let temp_1 = word_xor(cs, &s_6, &s_11)?;
    let temp = word_xor(cs, &temp_1, &s_25)?;
    let out: AllocatedScalar = from_32bits(cs, &temp)?;
    Ok(out)
}
// sigma0 = s7 XOR s18 XOR r3
fn sigma0<CS: ConstraintSystem>(cs: &mut CS, a: AllocatedScalar) -> Result<AllocatedScalar, R1CSError> {
    let x: word = to_32bits(cs, a)?;

    let s_7 = word_s_n(cs, &x, 7)?;
    let s_18 = word_s_n(cs, &x, 18)?;
    let r_3 = word_r_n(cs, &x, 3)?;

    let temp_1 = word_xor(cs, &s_7, &s_18)?;
    let temp = word_xor(cs, &temp_1, &r_3)?;

    let out: AllocatedScalar = from_32bits(cs, &temp)?;
    
    Ok(out)
}
// sigma1 = s17 XOR s19 XOR r10
fn sigma1<CS: ConstraintSystem>(cs: &mut CS, a: AllocatedScalar) -> Result<AllocatedScalar, R1CSError> {
    let x: word = to_32bits(cs, a)?;

    let s_17 = word_s_n(cs, &x, 17)?;
    let s_19 = word_s_n(cs, &x, 19)?;
    let r_10 = word_r_n(cs, &x, 10)?;

    let temp_1 = word_xor(cs, &s_17, &s_19)?;
    let temp = word_xor(cs, &temp_1, &r_10)?;

    let out: AllocatedScalar = from_32bits(cs, &temp)?;
    Ok(out)
}

fn from_32bits<CS: ConstraintSystem>(cs: &mut CS, x: &word) -> Result<AllocatedScalar, R1CSError> {
    let mut exp_2 = Scalar::one();
    let mut sum = Scalar::zero();
    let mut out_ass: Option<Scalar> = None;
    let mut out_v_lc: LinearCombination = LinearCombination::from(Scalar::zero());
    let mut one_lc: LinearCombination = LinearCombination::from(Scalar::one());
    for i in 0..32 {
        out_ass = x[i].assignment.map(|q| {
            sum = sum + q * exp_2;
            sum
        });
        let (_, _, o) = cs.allocate_multiplier(x[i].assignment.map(|q| (q, Scalar::from(exp_2))))?;
        out_v_lc = out_v_lc + o;
        exp_2 = exp_2 + exp_2;
    }
    let (_, _, out_v) = cs.multiply(out_v_lc, one_lc);

    let out: AllocatedScalar = AllocatedScalar{
        variable: out_v,
        assignment: out_ass,
    };
    Ok(out)
}

fn to_32bits<CS: ConstraintSystem>(cs: &mut CS, x: AllocatedScalar) -> Result<word, R1CSError> {
        let mut w: word = Vec::with_capacity(32);
        let mut x_lc: LinearCombination = LinearCombination::from(x.variable);
        let mut exp_2 = Scalar::one();
        for j in 0..32 {
            let mut temp: AllocatedScalar = AllocatedScalar {
                variable: Variable::One(),
                assignment: None,
            };
            
            let (a, b, o) = cs.allocate_multiplier(x.assignment.map(|q| {
                let bytes = q.as_bytes();
                let bit: u8 = ((bytes[j>>3] >> (j&7)) & 1u8) as u8;
                temp.assignment = Some(Scalar::from(bit));
                ((1-bit).into(), bit.into())
            }))?;
            temp.variable = b;
            w.push(temp);
            cs.constrain(o.into());
            cs.constrain(a+(b-1u8));
            x_lc = x_lc - b * exp_2;
            exp_2 = exp_2 + exp_2;
        }
        cs.constrain(x_lc);
        Ok(w)
}

fn all_add<CS: ConstraintSystem>(
    cs: &mut CS,
    l: AllocatedScalar,
    r: AllocatedScalar,
) -> Result<AllocatedScalar, R1CSError> {
    // let mut one_lc: LinearCombination = LinearCombination::from(Scalar::one());
    // let var_sum: LinearCombination = l.variable + r.variable;
    // let (_, _, o) = cs.multiply(var_sum.into(), one_lc);
    let o_ass: Option<Scalar> = l.assignment.map(|x| {
        let mut  t = Scalar::default();
        r.assignment.map(|y| {
            let o: Scalar = x + y;
            let mut bytes: [u8; 32] = [0u8; 32];
            for i in 0..4 {
                bytes[i] = o.as_bytes()[i];
            }
            t  = Scalar::from_bits(bytes);
        });
        t
    });

    let o: Variable = cs.allocate(o_ass)?;

    let out: AllocatedScalar = AllocatedScalar {
        variable: o,
        assignment: o_ass,
    };
    Ok(out)
}

#[test]
fn test_sha256() -> Result<(), R1CSError> {
    let pc_gens = PedersenGens::default();
    let bp_gens = BulletproofGens::new(524288, 1);

    let mut rng = thread_rng();

    let v_l = Scalar::random(&mut rng);
    let v_r = Scalar::random(&mut rng);
    // println!("{:?}", v_l);
    // println!("{:?}", v_r);

    let vl_bytes: [u8; 32] = v_l.to_bytes();
    let vr_bytes: [u8; 32] = v_r.to_bytes();
    let mut v_bytes: Vec<u8> = Vec::new();
    for i in 0..32 {
        v_bytes.push(vl_bytes[i]);
    }
    for i in 0..32 {
        v_bytes.push(vr_bytes[i]);
    }
    println!("{:?}", v_bytes.len());

    let mut hasher = Sha256::new();
    hasher.input(&v_bytes);
    let mut ou: [u8; 32] = [0; 32];
    hasher.result(&mut ou);
    println!("{:?}", ou);

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
        assert!(sha256_gadget(&mut prover, alloc_vl, alloc_vr).is_ok());
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
    assert!(sha256_gadget(&mut verifier, alloc_vl, alloc_vr).is_ok());

    Ok(verifier.verify(&proof, &pc_gens, &bp_gens)?)
}