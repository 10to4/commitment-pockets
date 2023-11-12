

// KZG10 - PolyCommit_DL
use super::PocketError;
use super::{UnaryPolynomial, multiexp};
use ark_std::{ops::Mul, ops::Sub, vec, Zero, One};
use ark_std::rand::RngCore;
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ff::UniformRand;
use ark_ec::AffineRepr;
use ark_std::vec::Vec;

pub struct BasicParameters<E: Pairing>{
    pub powers_of_g1: Vec<E::G1Affine>,
    pub g2: E::G2Affine,
    pub g2_tau: E::G2Affine,
}

impl <E: Pairing> BasicParameters<E> {
    pub fn new<R: RngCore>(max_degree :usize, rng: &mut R)-> Result<BasicParameters<E>, PocketError> {
        let tau = E::ScalarField::rand(rng);
        let g1 = E::G1::rand(rng); 
        let g2 = E::G2::rand(rng).into(); 
       
        let mut cur = g1.mul(tau);
        let powers_of_g1 = (0..max_degree+1).map(|_|{
            cur = cur.mul(&tau);
            cur.into()
        }).collect();
        
        Ok(Self{
            powers_of_g1,
            g2,
            g2_tau: g2.mul(tau).into()
        })
    }

    fn degree(&self) -> usize{
        self.powers_of_g1.len()
    }

    fn g1_vec(&self, len: usize) -> Result<Vec<E::G1Affine>, PocketError>{
        assert!(self.degree()>=len);
        Ok(self.powers_of_g1[0..len].to_vec())
    }
}

pub struct BasicPolyCommit<E: Pairing> {
    pub commit: E::G1Affine,
}
// impl <E: Pairing> PolyCommit<E> for BasicPolyCommit<E>{
impl <E: Pairing> BasicPolyCommit<E>{
    pub fn verify_poly(&self, params: &BasicParameters<E>, poly: &UnaryPolynomial<E>) -> Result<UnaryPolynomial<E>, PocketError>{
        let commit = Self::commit(params, poly).unwrap();
        if self.commit.eq(&commit.commit){
            Ok(poly.clone())
        } else {
            Err(PocketError::ErrorPolynomial)
        }
    }

    pub fn commit(params: &BasicParameters<E>, poly: &UnaryPolynomial<E>)-> Result<BasicPolyCommit<E>, PocketError>{
        let poly_degree = poly.degree();
        let param_degree = params.degree();
        assert!(param_degree >= param_degree);
        
        let commit = multiexp::<E>(params.g1_vec(poly_degree).unwrap(), poly.deref().to_vec()).unwrap();
        Ok(Self { commit })
    }
}

pub struct BasicProof<E: Pairing> {
    pub w: E::G1Affine,
    pub value: E::ScalarField,
}

// impl <E: Pairing> PolyCommit<E> for BasicPolyCommit<E>{
impl <E: Pairing> BasicProof<E>{

    pub fn create_witness(param: &BasicParameters<E>, poly: &UnaryPolynomial<E>, point: E::ScalarField) -> Result<Self, PocketError>{
        
        let poly = poly.clone();
        let poly_degree = poly.degree();
        let param_degree = param.degree();
        assert!(param_degree >= poly_degree);
        assert!(poly_degree > 1);

        let value = poly.evaluate(point);

        let div_poly = UnaryPolynomial::new(vec![E::ScalarField::zero() - value, E::ScalarField::one()]);

        let res_poly = poly.div(div_poly).unwrap();

        let w = multiexp::<E>(param.g1_vec(res_poly.degree()).unwrap(), res_poly.deref().to_vec()).unwrap();
        
        Ok(Self{
            w, value
        })
    }

    pub fn verify_eval(&self, params: &BasicParameters<E>, commit: &BasicPolyCommit<E>, point: E::ScalarField)-> bool{
        let v1 = commit.commit.into_group().sub(params.powers_of_g1[1].mul(self.value).into());
        let lhs = E::pairing(&v1, &params.g2.mul(point).into_affine());
        let rhs = E::pairing(&self.w, &(params.g2_tau.into_group() - &params.g2.mul(point).into()).into());

        lhs == rhs
    }
}

#[cfg(test)]
mod basic {
    use rand::thread_rng;
    use ark_bls12_381::Bls12_381;
    use ark_bls12_381::Fr;
    use ark_ff::UniformRand;
    use super::{BasicParameters, BasicPolyCommit, UnaryPolynomial, BasicProof};
    
    #[test]
    fn test_basic_poly_commit() {
        let rng: &mut rand::rngs::ThreadRng = &mut thread_rng();
        let params = BasicParameters::<Bls12_381>::new(16,rng).unwrap();
        let poly = UnaryPolynomial::<Bls12_381>::new(vec![Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng)]);
        let commit = BasicPolyCommit::<Bls12_381>::commit(&params, &poly).unwrap();
        let challenge = Fr::rand(rng);
        let proof = BasicProof::<Bls12_381>::create_witness(&params, &poly,challenge).unwrap();
        let result = proof.verify_eval(&params, &commit, challenge);
        println!("basic polynomial commitment result = {}", result);
    }
}