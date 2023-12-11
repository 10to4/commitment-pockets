// aggregatable subvector commitments for stateless cryptocurrencies
// https://eprint.iacr.org/2020/527.pdf

// a single polynomial
// multi points
// an uni polynomial
// no hiding
use super::PocketError;
use super::{multiexp, multiexp2, MultiProofParameters, UniPolynomial};
use crate::pockets::EvaluationDomain;
use ark_ec::{pairing::Pairing, AffineRepr};
use ark_ff::{Field, One, Zero};
use std::ops::{Div, Mul, Neg, Sub};

pub struct ASvcupdatePk<E: Pairing> {
    pub ai_commit: E::G1Affine,
    pub ui_commit: E::G1Affine,
}

pub struct ASvcprk<E: Pairing> {
    pub upks: Vec<ASvcupdatePk<E>>,
    pub params: MultiProofParameters<E>,
    pub l_commits: Vec<E::G1Affine>,
}

pub struct ASvcvrk<E: Pairing> {
    pub params: MultiProofParameters<E>,
    pub a_commit: E::G1Affine,
}

pub struct ASvckey<E: Pairing> {
    pub prk: ASvcprk<E>,
    pub vrk: ASvcvrk<E>,
}

impl<E: Pairing> ASvckey<E> {
    pub fn key_gen(params: MultiProofParameters<E>) -> Result<Self, PocketError> {
        let n = params.degree();
        assert!(n.is_power_of_two());

        let domain = EvaluationDomain::new(&vec![E::ScalarField::zero(); n]).unwrap();

        // x^n - 1
        let mut a_coeffs = vec![E::ScalarField::zero(); n + 1];
        a_coeffs[0] = E::ScalarField::one().neg();
        a_coeffs[n] = E::ScalarField::one();
        let a_poly = UniPolynomial::new(a_coeffs);
        let a_commit = multiexp::<E>(
            &vec![params.powers_of_g1[0], params.powers_of_g1[n]],
            vec![E::ScalarField::one().neg(), E::ScalarField::one()],
        )
        .unwrap();

        let mut l_commits = vec![params.powers_of_g1[0]; n];
        let upks = (0..n)
            .map(|i| {
                // div = x - w^i
                let div_poly = UniPolynomial::new(vec![
                    domain.omega().pow([i as u64]).neg(),
                    E::ScalarField::one(),
                ]);
                // ai = A(x)/(x - w^i)
                let ai_poly: UniPolynomial<E> = a_poly.div(&div_poly).unwrap();
                let ai_commit = multiexp::<E>(
                    &params.g1_vec(ai_poly.degree() + 1).unwrap(),
                    ai_poly.deref().to_vec(),
                )
                .unwrap();

                // A'(omega^i) = n (omega^i)^{n-1} = n (omega^{-i}) = n (omega^{n-i})
                // li = A(x) / ((x - w^i) * A'(omega^i)) = ai / A'(omega^i)
                let li_poly: UniPolynomial<E> = ai_poly
                    .mulvalue(
                        domain
                            .omega()
                            .pow([i as u64])
                            .div(E::ScalarField::from(n as u32)),
                    )
                    .unwrap();
                l_commits[i] = multiexp::<E>(
                    &params.g1_vec(li_poly.degree() + 1).unwrap(),
                    li_poly.deref().to_vec(),
                )
                .unwrap();

                // ui = (li - 1) / (x - w^i)
                let mut ui_coeff = li_poly.deref().to_vec();
                ui_coeff[0] = ui_coeff[0].sub(E::ScalarField::one());
                let ui_poly = UniPolynomial::new(ui_coeff).div(&div_poly).unwrap();

                let ui_commit = multiexp::<E>(
                    &params.g1_vec(ui_poly.degree() + 1).unwrap(),
                    ui_poly.deref().to_vec(),
                )
                .unwrap();

                ASvcupdatePk {
                    ai_commit,
                    ui_commit,
                }
            })
            .collect();

        Ok(Self {
            prk: ASvcprk {
                upks,
                params: params.clone(),
                l_commits,
            },
            vrk: ASvcvrk { params, a_commit },
        })
    }

    // e(li/g, g) = e(ui, g^tau / g^(omega^i))
    pub fn verify_upk(&self, i: usize) -> bool {
        let n = self.vrk.params.degree();
        assert!(n.is_power_of_two());

        let domain = EvaluationDomain::new(&vec![E::ScalarField::zero(); n]).unwrap();

        let lhs = E::pairing(
            (self.prk.l_commits[i].into_group() - self.vrk.params.powers_of_g1[1]).into(),
            self.vrk.params.powers_of_g2[0],
        );
        let rhs = E::pairing(
            self.prk.upks[i].ui_commit,
            (self.vrk.params.powers_of_g2[1].into_group()
                - self.vrk.params.powers_of_g2[0].mul(domain.omega().pow([i as u64])))
            .into(),
        );

        lhs == rhs
    }
}

pub struct ASvccommit<E: Pairing> {
    pub commit: E::G1Affine,
}

impl<E: Pairing> ASvccommit<E> {
    pub fn commit(prk: &ASvcprk<E>, values: &Vec<E::ScalarField>) -> Result<Self, PocketError> {
        assert_eq!(values.len(), prk.l_commits.len());
        let commit: E::G1Affine = prk
            .l_commits
            .iter()
            .zip(values.iter())
            .map(|(l_commit, value)| l_commit.mul(value))
            .sum::<E::G1>()
            .into();

        Ok(Self { commit })
    }

    pub fn update_comm(
        &mut self,
        delta: E::ScalarField,
        index: usize,
        upk: &ASvcupdatePk<E>,
        n: usize,
    ) {
        assert!(n.is_power_of_two());
        let domain = EvaluationDomain::new(&vec![E::ScalarField::zero(); n]).unwrap();
        let v = delta
            .mul(domain.omega().pow([index as u64]))
            .div(E::ScalarField::from(n as u32));
        self.commit = (self.commit + upk.ai_commit.mul(v)).into();
    }
}

#[derive(Clone)]
pub struct ASvcproof<E: Pairing> {
    pub q_commit: E::G1Affine,
}

impl<E: Pairing> ASvcproof<E> {
    // u_ij = (ai^ci * aj^cj)^{1/A'(\omega^j)}
    pub fn prove_pos(
        prk: &ASvcprk<E>,
        indexs: &Vec<usize>,
        values: &Vec<E::ScalarField>,
        n: usize,
    ) -> Result<Self, PocketError> {
        assert!(n.is_power_of_two());
        assert_eq!(n, values.len());
        let domain = EvaluationDomain::new(&vec![E::ScalarField::zero(); n]).unwrap();
        // 1/a'(w^i) = 1/(n w^{-i}) = w^i / n
        let a_cast_div: Vec<E::ScalarField> = (0..n)
            .map(|i| {
                domain
                    .omega()
                    .pow([i as u64])
                    .div(E::ScalarField::from(n as u32))
            })
            .collect();

        let proofs: Vec<E::G1Affine> = indexs
            .iter()
            .map(|&i| {
                (0..n)
                    .map(|j| {
                        if i == j {
                            // ui^vi
                            prk.upks[i].ui_commit.mul(values[i])
                        } else {
                            // ci = 1 /(w^i - w^j)
                            let ci = E::ScalarField::one().div(
                                domain.omega().pow([i as u64]) - domain.omega().pow([j as u64]),
                            );
                            // cj = 1 / (w^j - w^i)
                            let cj = ci.neg();
                            // u_ij = (ai^ci aj^cj)^(1/a'(w^j))
                            // u_ij ^ vj
                            (prk.upks[i].ai_commit.mul(ci) + prk.upks[j].ai_commit.mul(cj))
                                .mul(a_cast_div[j])
                                .mul(values[j])
                        }
                    })
                    .sum::<E::G1>()
                    .into()
            })
            .collect();

        // c = \prod (x - w^i)
        let mut c_poly: UniPolynomial<E> = UniPolynomial::new(vec![E::ScalarField::one()]);
        for &i in indexs.iter() {
            c_poly = c_poly
                .mulpoly(&UniPolynomial::new(vec![
                    domain.omega().pow([i as u64]).neg(),
                    E::ScalarField::one(),
                ]))
                .unwrap();
        }
        // c'(x)
        let mut c_cast_poly: UniPolynomial<E> = UniPolynomial::new(vec![E::ScalarField::zero()]);
        for &i in indexs.iter() {
            c_cast_poly = c_cast_poly
                .addpoly(
                    &c_poly
                        .div(&UniPolynomial::new(vec![
                            domain.omega().pow([i as u64]).neg(),
                            E::ScalarField::one(),
                        ]))
                        .unwrap(),
                )
                .unwrap();
        }

        let mut q_commit = prk.params.powers_of_g1[0]
            .mul(E::ScalarField::zero())
            .into();
        for (k, &i) in indexs.iter().enumerate() {
            // println!("a_cast_div[{}] = {:?}, proofs[0] = {:?}", i, c_cast_poly.evaluate(&domain.omega().pow([i as u64])), proofs[i]);
            q_commit = (q_commit.into_group()
                + proofs[k].mul(c_cast_poly.evaluate(&domain.omega().pow([i as u64]))))
            .into();
        }

        Ok(Self { q_commit })
    }

    pub fn verify_pos(
        &self,
        commit: &ASvccommit<E>,
        vrk: &ASvcvrk<E>,
        indexs: &Vec<usize>,
        values: &Vec<E::ScalarField>,
        n: usize,
    ) -> bool {
        assert!(n.is_power_of_two());
        let domain = EvaluationDomain::new(&vec![E::ScalarField::zero(); n]).unwrap();

        // \prod (x - w^i)
        let mut div_poly: UniPolynomial<E> = UniPolynomial::new(vec![E::ScalarField::one()]);
        for &i in indexs.iter() {
            let apoly = UniPolynomial::new(vec![
                domain.omega().pow([i as u64]).neg(),
                E::ScalarField::one(),
            ]);
            div_poly = div_poly.mulpoly(&apoly).unwrap();
        }
        let div_commit = multiexp2::<E>(
            &vrk.params.g2_vec(div_poly.degree() + 1).unwrap(),
            div_poly.deref().to_vec(),
        )
        .unwrap();

        let mut ipoly_coeffs = vec![E::ScalarField::zero(); indexs.len()];
        for &i in indexs.iter() {
            // \prod (w^i - w^j)
            let mut coeff: E::ScalarField = indexs
                .iter()
                .map(|&j| {
                    if i == j {
                        E::ScalarField::one()
                    } else {
                        domain.omega().pow([i as u64]) - domain.omega().pow([j as u64])
                    }
                })
                .product();
            coeff = coeff.div(values[i]);

            // (x - w^i) * /prod (w^i - w^j) / value
            let apoly =
                UniPolynomial::new(vec![domain.omega().pow([i as u64]).neg().mul(coeff), coeff]);
            let ipoly = div_poly.div(&apoly).unwrap();

            for j in 0..ipoly.deref().len() {
                ipoly_coeffs[j] = ipoly_coeffs[j] + ipoly.deref()[j]
            }
        }
        let ipoly: UniPolynomial<E> = UniPolynomial::new(ipoly_coeffs);
        let ipoly_commit = multiexp::<E>(
            &vrk.params.g1_vec(ipoly.degree() + 1).unwrap(),
            ipoly.deref().to_vec(),
        )
        .unwrap();

        let lhs = E::pairing(
            (commit.commit.into_group() - ipoly_commit).into(),
            vrk.params.powers_of_g2[0],
        );
        let rhs = E::pairing(self.q_commit, div_commit);

        lhs == rhs
    }

    pub fn update_proof(
        &mut self,
        delta: E::ScalarField,
        i: usize,
        j: usize,
        upk_i: &ASvcupdatePk<E>,
        upk_j: &ASvcupdatePk<E>,
        n: usize,
    ) {
        assert!(n.is_power_of_two());
        let domain = EvaluationDomain::new(&vec![E::ScalarField::zero(); n]).unwrap();

        if i == j {
            self.q_commit = (self.q_commit.into_group() + upk_i.ui_commit.mul(delta)).into();
        } else {
            let ci = E::ScalarField::one()
                .div(domain.omega().pow([i as u64]) - domain.omega().pow([j as u64]));
            let cj = ci.neg();
            let a_cast = E::ScalarField::one().div(
                domain
                    .omega()
                    .pow([(n - j) as u64])
                    .mul(E::ScalarField::from(n as u32)),
            );
            self.q_commit = (self.q_commit.into_group()
                + (upk_i.ai_commit.mul(ci) + upk_j.ai_commit.mul(cj))
                    .mul(a_cast)
                    .mul(delta))
            .into();
        }
    }

    pub fn aggregate_proof(
        indexs: Vec<usize>,
        proofs: &Vec<ASvcproof<E>>,
        n: usize,
    ) -> Result<Self, PocketError> {
        assert!(n.is_power_of_two());
        let domain = EvaluationDomain::new(&vec![E::ScalarField::zero(); n]).unwrap();

        // c = \prod (x - w^i)
        let mut c_poly: UniPolynomial<E> = UniPolynomial::new(vec![E::ScalarField::one()]);
        for &i in indexs.iter() {
            c_poly = c_poly
                .mulpoly(&UniPolynomial::new(vec![
                    domain.omega().pow([i as u64]).neg(),
                    E::ScalarField::one(),
                ]))
                .unwrap();
        }
        // c'(x)
        let mut c_cast_poly: UniPolynomial<E> = UniPolynomial::new(vec![E::ScalarField::zero()]);
        for &i in indexs.iter() {
            c_cast_poly = c_cast_poly
                .addpoly(
                    &c_poly
                        .div(&UniPolynomial::new(vec![
                            domain.omega().pow([i as u64]).neg(),
                            E::ScalarField::one(),
                        ]))
                        .unwrap(),
                )
                .unwrap();
        }
        let q_commit = indexs
            .iter()
            .enumerate()
            .map(|(k, &i)| {
                let a_cast = c_cast_poly.evaluate(&domain.omega().pow([i as u64]));
                proofs[k].q_commit.mul(E::ScalarField::one().div(a_cast))
            })
            .sum::<E::G1>()
            .into();

        Ok(Self { q_commit })
    }
}

#[cfg(test)]
mod basic {
    use super::ASvcproof;
    use super::{ASvccommit, ASvckey, MultiProofParameters};
    use ark_bls12_381::Bls12_381;
    use ark_bls12_381::Fr;
    use ark_ff::UniformRand;
    use rand::thread_rng;

    #[test]
    fn test_asvc() {
        let n = 16;

        let rng: &mut rand::rngs::ThreadRng = &mut thread_rng();
        let params = MultiProofParameters::<Bls12_381>::new(n, rng).unwrap();

        let keys = ASvckey::key_gen(params.clone()).unwrap();

        let mut values = vec![
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
        ];
        let mut commit = ASvccommit::commit(&keys.prk, &values).unwrap();

        let index1 = vec![0];
        let mut proof1 = ASvcproof::prove_pos(&keys.prk, &index1, &values, n).unwrap();
        let result = proof1.verify_pos(&commit, &keys.vrk, &index1, &values, n);
        println!("verify pos: pos = {:?} ...{}", index1, result);
        assert!(result);

        let index2 = vec![3];
        let mut proof2 = ASvcproof::prove_pos(&keys.prk, &index2, &values, n).unwrap();
        let result = proof2.verify_pos(&commit, &keys.vrk, &index2, &values, n);
        println!("verify pos: pos = {:?} ...{}", index2, result);
        assert!(result);

        let delta = Fr::rand(rng);
        let index = 3;
        values[index] = values[index] + delta;
        commit.update_comm(delta, index, &keys.prk.upks[index], n);

        proof1.update_proof(delta, 0, index, &keys.prk.upks[0], &keys.prk.upks[index], n);
        let result = proof1.verify_pos(&commit, &keys.vrk, &index1, &values, n);
        println!("verify pos after update: pos = {:?} ...{}", 0, result);
        assert!(result);

        proof2.update_proof(
            delta,
            index,
            index,
            &keys.prk.upks[index],
            &keys.prk.upks[index],
            n,
        );
        let result = proof2.verify_pos(&commit, &keys.vrk, &index2, &values, n);
        println!("verify pos after update: pos = {:?} ...{}", 3, result);
        assert!(result);

        let aproof = ASvcproof::aggregate_proof(vec![0, index], &vec![proof1, proof2], n).unwrap();
        let result = aproof.verify_pos(&commit, &keys.vrk, &vec![0, index], &values, n);
        println!("verify aggregate pos: pos = {:?} ...{}", vec![0, 3], result);
        assert!(result);
    }
}
