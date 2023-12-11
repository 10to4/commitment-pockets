

// KZG10 - PolyCommit_DL
// a single polynomial
// a single point
// an univar polynomial
// no hiding
use super::PocketError;
use super::{UniPolynomial, multiexp};
use ark_std::{ops::Mul, vec, Zero, One};
use ark_std::rand::RngCore;
use ark_ec::pairing::Pairing;
use ark_ff::UniformRand;
use ark_ec::AffineRepr;
use ark_std::vec::Vec;

#[derive(Clone)]
pub struct BasicParameters<E: Pairing>{
    pub powers_of_g1: Vec<E::G1Affine>,
    pub g2: E::G2Affine,
    pub g2_tau: E::G2Affine,
}

impl <E: Pairing> BasicParameters<E> {
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
       
        Ok(Self{
            powers_of_g1,
            g2,
            g2_tau: g2.mul(tau).into()
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

pub struct BasicPolyCommit<E: Pairing> {
    pub commit: E::G1Affine,
}
// impl <E: Pairing> PolyCommit<E> for BasicPolyCommit<E>{
impl <E: Pairing> BasicPolyCommit<E>{
    pub fn commit(params: &BasicParameters<E>, poly: &UniPolynomial<E>)-> Result<Self, PocketError>{
        let poly_degree = poly.degree();
        let param_degree = params.degree();
        assert!(param_degree >= poly_degree);
        
        let commit = multiexp::<E>(&params.g1_vec(poly_degree + 1).unwrap(), poly.deref().to_vec()).unwrap();
        Ok(Self { commit })
    }

    pub fn open(&self, params: &BasicParameters<E>, poly: &UniPolynomial<E>) -> Result<UniPolynomial<E>, PocketError>{
        let commit = Self::commit(params, poly).unwrap();
        if self.commit.eq(&commit.commit){
           Ok(poly.clone())
        } else {
            Err(PocketError::ErrorPolynomial)
        }
    }

    pub fn verify_poly(&self, params: &BasicParameters<E>, poly: &UniPolynomial<E>) -> bool{
        let commit = Self::commit(params, poly).unwrap();
        self.commit.eq(&commit.commit)
    }
}

pub struct BasicProof<E: Pairing> {
    pub w: E::G1Affine,
    pub value: E::ScalarField,
}

impl <E: Pairing> BasicProof<E>{

    pub fn create_witness(params: &BasicParameters<E>, poly: &UniPolynomial<E>, point: E::ScalarField) -> Result<Self, PocketError>{
        
        let poly = poly.clone();
        let poly_degree = poly.degree();
        let param_degree = params.degree();
        assert!(param_degree >= poly_degree);
        assert!(poly_degree > 1);

        let value = poly.evaluate(&point);

        let div_poly = UniPolynomial::new(vec![E::ScalarField::zero() - point, E::ScalarField::one()]);

        let res_poly = poly.div(&div_poly).unwrap();

        let w = multiexp::<E>(&params.g1_vec(res_poly.degree() + 1).unwrap(), res_poly.deref().to_vec()).unwrap();
        
        Ok(Self{
            w, value
        })
    }

    pub fn verify_eval(&self, params: &BasicParameters<E>, commit: &BasicPolyCommit<E>, point: E::ScalarField)-> bool{
        
        let lhs = E::pairing(commit.commit,params.g2);
        let rhs = E::multi_pairing([&self.w, &params.powers_of_g1[0].mul(self.value).into()],[&(params.g2_tau.into_group() - &params.g2.mul(point).into()).into(), &params.g2]);

        lhs == rhs
    }
}

#[cfg(test)]
mod basic {
    use rand::thread_rng;
    use ark_bls12_381::Bls12_381;
    use ark_bls12_381::Fr;
    use ark_ff::UniformRand;
    use super::{BasicParameters, BasicPolyCommit, UniPolynomial, BasicProof};
    
    #[test]
    fn test_basic_poly_commit() {
        let rng: &mut rand::rngs::ThreadRng = &mut thread_rng();
        let params = BasicParameters::<Bls12_381>::new(16,rng).unwrap();
        let poly = UniPolynomial::<Bls12_381>::new(vec![Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng)]);
        let commit = BasicPolyCommit::<Bls12_381>::commit(&params, &poly).unwrap();
        let challenge = Fr::rand(rng);
        let proof = BasicProof::<Bls12_381>::create_witness(&params, &poly,challenge).unwrap();
        let result = proof.verify_eval(&params, &commit, challenge);
        println!("basic polynomial commitment result = {}", result);
    }
}