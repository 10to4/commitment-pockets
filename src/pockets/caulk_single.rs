// caulk -- single element
// a single polynomial
// a single point
// an univar polynomial
// hiding

use super::PocketError;
use super::{UniPolynomial, multiexp, multiexp2, EvaluationDomain};
use ark_std::{ops::Mul, ops::Add, ops::Neg, ops::Sub, vec, Zero};
use ark_std::rand::RngCore;
use ark_ec::pairing::Pairing;
use ark_ff::UniformRand;
use ark_ec::AffineRepr;
use ark_std::vec::Vec;

pub struct CaulkParameters<E: Pairing>{
    pub powers_of_g1: Vec<E::G1Affine>,
    pub g2: E::G2Affine,
    pub g2_tau: E::G2Affine,
    pub h: E::G1Affine,
}

impl <E: Pairing> CaulkParameters<E> {
    pub fn new<R: RngCore>(max_degree :usize, rng: &mut R)-> Result<Self, PocketError> {
        let tau = E::ScalarField::rand(rng);
        
        let mut cur = E::G1::rand(rng); 
        let powers_of_g1 = (0..max_degree+1).map(|i|{
            if i != 0 {
                cur = cur.mul(&tau);
            }
            cur.into()
        }).collect();
        
        let g2 = E::G2::rand(rng).into(); 

        let h = E::G1::rand(rng).into(); 
       
        Ok(Self{
            powers_of_g1,
            g2,
            g2_tau: g2.mul(tau).into(),
            h
        })
    }

    pub fn degree(&self) -> usize{
        self.powers_of_g1.len() - 1
    }

    pub fn g1_vec(&self, len: usize) -> Result<Vec<E::G1Affine>, PocketError>{
        assert!(self.degree() >= len - 1);
        Ok(self.powers_of_g1[0..len].to_vec())
    }
}


pub struct PedersenProof<E: Pairing> {
    pub commit: E::G1Affine,
    pub r_commit: E::G1Affine,
    pub t1: E::ScalarField,
    pub t2: E::ScalarField,
}

impl <E: Pairing> PedersenProof<E>{
    pub fn prove<R: RngCore>(params: &CaulkParameters<E>, v: E::ScalarField, rng: &mut R)->Result<(Self, E::ScalarField), PocketError>{
        let r = E::ScalarField::rand(rng);
        let commit = params.powers_of_g1[0].mul(v).add(params.h.mul(r)).into();

        // todo: fait-shamir
        let s1 = E::ScalarField::rand(rng);
        let s2 = E::ScalarField::rand(rng);

        let r_commit = params.powers_of_g1[0].mul(s1).add(params.h.mul(s2)).into();

        let c = E::ScalarField::rand(rng); // todo: c = hash(cm, R);

        let t1 = s1.add(v.mul(c));
        let t2 = s2.add(r.mul(c));

        Ok((Self{
            commit,
            r_commit,
            t1,
            t2,
        }, r))
    }

    pub fn verify(&self, params: &CaulkParameters<E>) -> bool {
        let c = E::ScalarField::zero(); // todo: c = hash(cm, R);
        let lhs = self.r_commit.add(self.commit.mul(c)).into();
        let rhs = params.powers_of_g1[0].mul(self.t1).add(params.h.mul(self.t2)).into();

        lhs == rhs
    }
}

pub struct UnityProof<E: Pairing> {
    pub z: E::G1Affine,
}

impl <E: Pairing>  UnityProof<E>{
        pub fn prove(params: &CaulkParameters<E>, a: E::ScalarField) -> Result<Self, PocketError>{
            todo!()
        }

        pub fn verify(&self, params: &CaulkParameters<E>) -> bool{
            todo!()
        }
}

pub struct CaulkSinglePolyCommit<E: Pairing> {
    pub commit: E::G1Affine,
}

impl <E: Pairing> CaulkSinglePolyCommit<E>{
    pub fn commit(params: &CaulkParameters<E>, values: Vec<E::ScalarField>)-> Result<(Self, UniPolynomial<E>), PocketError>{
        
        let mut domain: EvaluationDomain<E::ScalarField> = EvaluationDomain::new(&values).unwrap();
        domain.ifft();

        let poly: UniPolynomial<E> =  UniPolynomial::new(domain.as_ref().clone());

        let param_degree = params.degree();
        let poly_degree = poly.degree();
        assert!(param_degree >= poly_degree);
        
        let commit = multiexp::<E>(&params.g1_vec(poly_degree + 1).unwrap(), poly.deref().to_vec()).unwrap();
        Ok((Self { commit }, poly))
    }
}

pub struct CaulkSingleProof<E: Pairing> {
    z_commit: E::G2Affine,
    t_commit: E::G1Affine,
    s_commit: E::G2Affine,
    pi_unity: UnityProof<E>,
    pi_ped: PedersenProof<E>,
}

impl <E: Pairing> CaulkSingleProof<E> {
    pub fn prover<R: RngCore>(params: &CaulkParameters<E>, poly: UniPolynomial<E>, point: E::ScalarField, rng: &mut R)-> Result<Self, PocketError>{

        let a = E::ScalarField::rand(rng);
        let s = E::ScalarField::rand(rng);

        let v = poly.evaluate(&point);

        let g2_vec = vec![params.g2, params.g2_tau];

        let (pi_ped, r) = PedersenProof::prove(params, v, rng).unwrap();
        let pi_unity = UnityProof::prove(params, a).unwrap();

        let z_poly: UniPolynomial<E>  = UniPolynomial::new(vec![a.mul(point).neg(), a]);
        let z_commit = multiexp2::<E>(&g2_vec, z_poly.deref().to_vec()).unwrap();

        let t_poly = poly.div(&z_poly).unwrap();
        let mut t_commit =multiexp::<E>(&params.g1_vec(t_poly.degree() + 1).unwrap(), t_poly.deref().to_vec()).unwrap(); 
        t_commit = t_commit.add(params.h.mul(s)).into();

        let s_poly: UniPolynomial<E>  = UniPolynomial::new(vec![a.mul(point).mul(s).sub(r), a.mul(s).neg()]);
        let s_commit = multiexp2::<E>(&g2_vec, s_poly.deref().to_vec()).unwrap();
        
        Ok(Self { z_commit, t_commit, s_commit, pi_unity, pi_ped })
    }

    pub fn verify(&self, params: &CaulkParameters<E>, commit: &CaulkSinglePolyCommit<E>,) -> bool{

        // e(C - cm, [1]_2) = e([T]_1, [z]_2) + e([h]_1, [S]_2)
        let lhs = E::pairing((commit.commit.into_group() - &self.pi_ped.commit).into(), params.g2);
        let rhs = E::multi_pairing([&self.t_commit, &params.h],[&self.z_commit, &self.s_commit]);

        assert!(lhs == rhs);
        assert!(self.pi_ped.verify(params));
        assert!(self.pi_unity.verify(params));

        lhs == rhs && self.pi_ped.verify(params) && self.pi_unity.verify(params)
    }
}