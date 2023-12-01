
// Multiproofs
// a single polynomial
// multiply points
// an univar polynomial
// no hiding

use super::PocketError;
use super::{UniPolynomial, multiexp, multiexp2};
use ark_std::{ops::Mul, vec, Zero, One};
use ark_std::rand::RngCore;
use ark_ec::pairing::Pairing;
use ark_ff::UniformRand;
use ark_std::vec::Vec;

pub struct MultiProofParameters<E: Pairing>{
    pub powers_of_g1: Vec<E::G1Affine>,
    pub powers_of_g2: Vec<E::G2Affine>,
}

impl <E: Pairing> MultiProofParameters<E> {
    pub fn new<R: RngCore>(max_degree :usize, rng: &mut R)-> Result<Self, PocketError> {
        let tau = E::ScalarField::rand(rng);
        
        let mut cur = E::G1::rand(rng); 
        let powers_of_g1 = (0..max_degree+1).map(|i|{
            if i != 0 {
                cur = cur.mul(&tau);
            }
            cur.into()
        }).collect();

        let mut cur = E::G2::rand(rng); 
        let powers_of_g2 = (0..max_degree+1).map(|i|{
            if i != 0 {
                cur = cur.mul(&tau);
            }
            cur.into()
        }).collect();
       
        Ok(Self{
            powers_of_g1,
            powers_of_g2
        })
    }

    pub fn degree(&self) -> usize{
        self.powers_of_g1.len() - 1
    }

    pub fn g1_vec(&self, len: usize) -> Result<Vec<E::G1Affine>, PocketError>{
        assert!(self.degree() >= len - 1);
        Ok(self.powers_of_g1[0..len].to_vec())
    }

    pub fn g2_vec(&self, len: usize) -> Result<Vec<E::G2Affine>, PocketError>{
        assert!(self.degree() >= len - 1);
        Ok(self.powers_of_g2[0..len].to_vec())
    }
}

pub struct MultiProofPolyCommit<E: Pairing> {
    pub commit: E::G1Affine,
}

// impl <E: Pairing> PolyCommit<E> for BasicPolyCommit<E>{
impl <E: Pairing> MultiProofPolyCommit<E>{
    pub fn commit(params: &MultiProofParameters<E>, poly: &UniPolynomial<E>)-> Result<Self, PocketError>{
        let poly_degree = poly.degree();
        let param_degree = params.degree();
        assert!(param_degree >= poly_degree);
        
        let commit = multiexp::<E>(params.g1_vec(poly_degree + 1).unwrap(), poly.deref().to_vec()).unwrap();
        Ok(Self { commit })
    }

    pub fn open(&self, params: &MultiProofParameters<E>, poly: &UniPolynomial<E>) -> Result<UniPolynomial<E>, PocketError>{
        let commit = Self::commit(params, poly).unwrap();
        if self.commit.eq(&commit.commit){
           Ok(poly.clone())
        } else {
            Err(PocketError::ErrorPolynomial)
        }
    }

    pub fn verify_poly(&self, params: &MultiProofParameters<E>, poly: &UniPolynomial<E>) -> bool{
        let commit = Self::commit(params, poly).unwrap();
        self.commit.eq(&commit.commit)
    }
}

pub struct MultiProofPolyCommit2<E: Pairing> {
    pub commit: E::G2Affine,
}

impl <E: Pairing> MultiProofPolyCommit2<E>{
    pub fn commit(params: &MultiProofParameters<E>, poly: &UniPolynomial<E>)-> Result<Self, PocketError>{
        let poly_degree = poly.degree();
        let param_degree = params.degree();
        assert!(param_degree >= poly_degree);
        
        let commit = multiexp2::<E>(params.g2_vec(poly_degree + 1).unwrap(), poly.deref().to_vec()).unwrap();
        Ok(Self { commit })
    }
}

pub struct MultiProof<E: Pairing> {
    pub w: E::G1Affine,
    pub values: Vec<E::ScalarField>,
}

impl <E: Pairing> MultiProof<E>{

    pub fn create_witness(params: &MultiProofParameters<E>, poly: &UniPolynomial<E>, points: &Vec<E::ScalarField>) -> Result<Self, PocketError>{
        
        let poly = poly.clone();
        let poly_degree = poly.degree();
        let param_degree = params.degree();
        assert!(param_degree >= poly_degree);
        assert!(poly_degree > points.len());

        let mut div_poly = UniPolynomial::new(vec![E::ScalarField::one()]);
        let values = points.iter().map(|point|{
            let apoly = UniPolynomial::new(vec![E::ScalarField::zero() - point, E::ScalarField::one()]);
            div_poly = div_poly.mulpoly(&apoly).unwrap();
            poly.evaluate(point)
        }).collect();
        let res_poly = poly.div(&div_poly).unwrap();

        let w = multiexp::<E>(params.g1_vec(res_poly.degree() + 1).unwrap(), res_poly.deref().to_vec()).unwrap();
        
        Ok(Self{
            w,
            values
        })
    }

    pub fn verify_eval(&self, params: &MultiProofParameters<E>, commit: &MultiProofPolyCommit<E>, points: &Vec<E::ScalarField>) -> bool{
        let mut div_poly = UniPolynomial::new(vec![E::ScalarField::one()]);
        for point in points.iter() {
            let apoly = UniPolynomial::new(vec![E::ScalarField::zero() - point, E::ScalarField::one()]);
            div_poly = div_poly.mulpoly(&apoly).unwrap();
        }
        let div_commit = MultiProofPolyCommit2::commit(params, &div_poly).unwrap();

        let mut ipoly_coeffs = vec![E::ScalarField::zero(); points.len()+1];
        for (i, &point) in points.iter().enumerate() {
            let coeff = points.iter().enumerate().map(|(j, &apoint)|{
                if i == j{
                    E::ScalarField::one()
                } else {
                    point - apoint
                }
            }).product();
            let apoly = UniPolynomial::new(vec![E::ScalarField::zero() - point.mul(coeff), coeff]);
            let coeffs = div_poly.div(&apoly).unwrap();
            for j in 0..coeffs.deref().len() {
                ipoly_coeffs[j] = ipoly_coeffs[j] + coeffs.deref()[j].mul(self.values[i])
            }
        }
        let ipoly = UniPolynomial::new(ipoly_coeffs);
        let ipoly_commit = MultiProofPolyCommit::commit(params, &ipoly).unwrap();
        

        let lhs = E::pairing(commit.commit,params.powers_of_g2[0]);
        let rhs = E::multi_pairing([&self.w, &ipoly_commit.commit],[&div_commit.commit, &params.powers_of_g2[0]]);

        lhs == rhs
    }
}

#[cfg(test)]
mod basic {
    use rand::thread_rng;
    use ark_bls12_381::Bls12_381;
    use ark_bls12_381::Fr;
    use ark_ff::UniformRand;
    use super::{MultiProofParameters, MultiProofPolyCommit, UniPolynomial, MultiProof};
    
    #[test]
    fn test_multi_proof_poly_commit() {
        let rng: &mut rand::rngs::ThreadRng = &mut thread_rng();
        let params = MultiProofParameters::<Bls12_381>::new(16,rng).unwrap();
        let poly = UniPolynomial::<Bls12_381>::new(vec![Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng), Fr::rand(rng)]);
        let commit = MultiProofPolyCommit::<Bls12_381>::commit(&params, &poly).unwrap();
        let points = vec![Fr::rand(rng), Fr::rand(rng), Fr::rand(rng)];
        let proof = MultiProof::<Bls12_381>::create_witness(&params, &poly, &points).unwrap();
        let result = proof.verify_eval(&params, &commit, &points);
        println!("basic polynomial commitment result = {}", result);
    }
}