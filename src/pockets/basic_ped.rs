use std::ops::Add;

// KZG10 - PolyCommit_PED
// a single polynomial
// a single point
// an univar polynomial
// hiding
use super::PocketError;
use super::{multiexp, UniPolynomial};
use ark_ec::AffineRepr;
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ff::UniformRand;
use ark_std::rand::RngCore;
use ark_std::vec::Vec;
use ark_std::{ops::Mul, vec, One, Zero};

pub struct BasicPEDParameters<E: Pairing> {
    pub powers_of_g: Vec<E::G1Affine>,
    pub powers_of_h: Vec<E::G1Affine>,
    pub g2: E::G2Affine,
    pub g2_tau: E::G2Affine,
}

impl<E: Pairing> BasicPEDParameters<E> {
    pub fn new<R: RngCore>(max_degree: usize, rng: &mut R) -> Result<Self, PocketError> {
        let tau = E::ScalarField::rand(rng);

        let mut cur = E::G1::rand(rng);
        let powers_of_g = (0..max_degree + 1)
            .map(|i| {
                if i != 0 {
                    cur = cur.mul(&tau);
                }
                cur.into()
            })
            .collect();

        let mut cur = E::G1::rand(rng);
        let powers_of_h = (0..max_degree + 1)
            .map(|i| {
                if i != 0 {
                    cur = cur.mul(&tau);
                }
                cur.into()
            })
            .collect();

        let g2 = E::G2::rand(rng).into();
        Ok(Self {
            powers_of_g,
            powers_of_h,
            g2,
            g2_tau: g2.mul(tau).into(),
        })
    }

    fn degree(&self) -> usize {
        assert_eq!(self.powers_of_g.len(), self.powers_of_h.len());

        self.powers_of_g.len() - 1
    }

    fn g_vec(&self, len: usize) -> Result<Vec<E::G1Affine>, PocketError> {
        assert!(self.degree() >= len);
        Ok(self.powers_of_g[0..len].to_vec())
    }

    fn h_vec(&self, len: usize) -> Result<Vec<E::G1Affine>, PocketError> {
        assert!(self.degree() >= len);
        Ok(self.powers_of_h[0..len].to_vec())
    }
}

pub struct BasicPEDPolyCommit<E: Pairing> {
    pub commit: E::G1Affine,
}

impl<E: Pairing> BasicPEDPolyCommit<E> {
    pub fn commit<R: RngCore>(
        params: &BasicPEDParameters<E>,
        poly: &UniPolynomial<E>,
        rng: &mut R,
    ) -> Result<(Self, UniPolynomial<E>), PocketError> {
        let poly_degree = poly.degree();
        let param_degree = params.degree();
        assert!(param_degree >= poly_degree);

        let coeffs = (0..poly_degree + 1)
            .map(|_| E::ScalarField::rand(rng))
            .collect();
        let phi_poly: UniPolynomial<E> = UniPolynomial::new(coeffs);

        let commit = multiexp::<E>(
            &params.g_vec(poly_degree + 1).unwrap(),
            poly.deref().to_vec(),
        )
        .unwrap();
        let phi_commit = multiexp::<E>(
            &params.h_vec(poly_degree + 1).unwrap(),
            phi_poly.deref().to_vec(),
        )
        .unwrap();
        Ok((
            Self {
                commit: commit.add(phi_commit).into(),
            },
            phi_poly,
        ))
    }

    pub fn open(
        &self,
        params: &BasicPEDParameters<E>,
        poly: &UniPolynomial<E>,
        phi_poly: &UniPolynomial<E>,
    ) -> Result<(UniPolynomial<E>, UniPolynomial<E>), PocketError> {
        let poly_degree = poly.degree();
        let phi_degree = phi_poly.degree();
        let param_degree = params.degree();
        assert!(phi_degree == poly_degree);
        assert!(param_degree >= poly_degree);

        let commit = multiexp::<E>(
            &params.g_vec(poly_degree + 1).unwrap(),
            poly.deref().to_vec(),
        )
        .unwrap()
        .add(
            multiexp::<E>(
                &params.h_vec(poly_degree + 1).unwrap(),
                phi_poly.deref().to_vec(),
            )
            .unwrap(),
        )
        .into_affine();

        if self.commit.eq(&commit) {
            Ok((poly.clone(), phi_poly.clone()))
        } else {
            Err(PocketError::ErrorPolynomial)
        }
    }

    pub fn verify_poly(
        &self,
        params: &BasicPEDParameters<E>,
        poly: &UniPolynomial<E>,
        phi_poly: &UniPolynomial<E>,
    ) -> bool {
        let poly_degree = poly.degree();
        let phi_degree = phi_poly.degree();
        let param_degree = params.degree();
        assert!(phi_degree == poly_degree);
        assert!(param_degree >= poly_degree);

        let commit = multiexp::<E>(
            &params.g_vec(poly_degree + 1).unwrap(),
            poly.deref().to_vec(),
        )
        .unwrap()
        .add(
            multiexp::<E>(
                &params.h_vec(poly_degree + 1).unwrap(),
                phi_poly.deref().to_vec(),
            )
            .unwrap(),
        )
        .into_affine();

        self.commit.eq(&commit)
    }
}

pub struct BasicPEDProof<E: Pairing> {
    pub w: E::G1Affine,
    pub value: E::ScalarField,
    pub phi_value: E::ScalarField,
}

impl<E: Pairing> BasicPEDProof<E> {
    pub fn create_witness(
        params: &BasicPEDParameters<E>,
        poly: &UniPolynomial<E>,
        phi_poly: &UniPolynomial<E>,
        point: E::ScalarField,
    ) -> Result<Self, PocketError> {
        let poly = poly.clone();
        let phi_poly = phi_poly.clone();

        let poly_degree = poly.degree();
        let phi_degree = phi_poly.degree();
        let param_degree = params.degree();
        assert!(phi_degree == poly_degree);
        assert!(param_degree >= poly_degree);
        assert!(poly_degree >= 1);

        let div_poly =
            UniPolynomial::new(vec![E::ScalarField::zero() - point, E::ScalarField::one()]);

        let value = poly.evaluate(&point);
        let res_poly = poly.div(&div_poly).unwrap();

        let phi_value = phi_poly.evaluate(&point);
        let res_phi_poly = phi_poly.div(&div_poly).unwrap();

        let w = multiexp::<E>(
            &params.g_vec(res_poly.degree() + 1).unwrap(),
            res_poly.deref().to_vec(),
        )
        .unwrap();
        let phi_w = multiexp::<E>(
            &params.h_vec(res_phi_poly.degree() + 1).unwrap(),
            res_phi_poly.deref().to_vec(),
        )
        .unwrap();

        Ok(Self {
            w: w.add(phi_w).into(),
            value,
            phi_value,
        })
    }

    pub fn verify_eval(
        &self,
        params: &BasicPEDParameters<E>,
        commit: &BasicPEDPolyCommit<E>,
        point: E::ScalarField,
    ) -> bool {
        let lhs = E::pairing(commit.commit, params.g2);

        let rhs = E::multi_pairing(
            [
                &self.w,
                &params.powers_of_g[0]
                    .mul(self.value)
                    .add(params.powers_of_h[0].mul(self.phi_value))
                    .into(),
            ],
            [
                &(params.g2_tau.into_group() - params.g2.mul(point)).into(),
                &params.g2,
            ],
        );

        lhs == rhs
    }
}

#[cfg(test)]
mod basic_ped {

    use super::{BasicPEDParameters, BasicPEDPolyCommit, BasicPEDProof, UniPolynomial};
    use ark_bls12_381::Bls12_381;
    use ark_bls12_381::Fr;
    use ark_ff::UniformRand;
    use rand::thread_rng;

    #[test]
    fn test_basic_ped_poly_commit() {
        let rng: &mut rand::rngs::ThreadRng = &mut thread_rng();
        let params = BasicPEDParameters::<Bls12_381>::new(16, rng).unwrap();

        let poly = UniPolynomial::<Bls12_381>::new(vec![
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
        ]);
        let (commit, phi_poly) =
            BasicPEDPolyCommit::<Bls12_381>::commit(&params, &poly, rng).unwrap();
        let challenge = Fr::rand(rng);
        let proof =
            BasicPEDProof::<Bls12_381>::create_witness(&params, &poly, &phi_poly, challenge)
                .unwrap();
        let result = proof.verify_eval(&params, &commit, challenge);
        println!("basic polynomial commitment result = {}", result);
    }
}
