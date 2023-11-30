use std::ops::MulAssign;

mod error;
use error::PocketError;

mod basic;
pub use basic::{BasicParameters, BasicPolyCommit, BasicProof};

mod basic_ped;
pub use basic_ped::{BasicPEDParameters, BasicPEDPolyCommit, BasicPEDProof};

use ark_ff::Field;
use ark_ec::{pairing::Pairing};
use ark_std::{ops::Mul, ops::Add, ops::Sub, vec, Zero, One};


#[derive(Clone, PartialEq, Eq, Hash, Default)]
pub struct UniPolynomial<E: Pairing> {
   
    coeffs: Vec<E::ScalarField>,
}

impl <E: Pairing> UniPolynomial<E> {
    pub fn new(coeffs: Vec<E::ScalarField>) -> Self{
        Self { coeffs }
    }

    pub fn deref(&self) -> &[E::ScalarField] {
        &self.coeffs
    }

    pub fn deref_mut(&mut self) -> &mut [E::ScalarField] {
        &mut self.coeffs
    }

    pub fn degree(&self) -> usize {
        self.coeffs.len()
    } 

    pub fn is_zero(&self) -> bool {
        self.coeffs.len() == 0
    }

    pub fn zero() -> Self{
        Self::new(vec![])
    }

    pub fn evaluate(&self, value: E::ScalarField) -> E::ScalarField{
        if self.is_zero() {
            return E::ScalarField::zero()
        }
        let mut cur = E::ScalarField::one();
        let mut sum = E::ScalarField::zero();
        for coeff in self.deref() {
            sum += cur.mul(coeff);
            cur.mul_assign(value);
        }
        sum
    }

    pub fn div(self, div_poly: UniPolynomial<E>) -> Result<UniPolynomial<E>, PocketError>{
        if self.is_zero() {
            Ok(UniPolynomial::zero())
        } else if div_poly.is_zero() {
            Err(PocketError::InvalidDivisor)
        } else {
            let mut quotient = vec![E::ScalarField::zero(); self.degree() - div_poly.degree() + 1];
            let mut remainder: UniPolynomial<E> = self.clone();
            let divisor_leading_inv = div_poly.deref().last().unwrap().inverse().unwrap();
            
            while !remainder.is_zero() && remainder.degree() >= div_poly.degree() {
                let mut cur_q_coeff = remainder.coeffs.last().unwrap().clone();
                cur_q_coeff.mul_assign(&divisor_leading_inv);
                
                let cur_q_degree = remainder.degree() - div_poly.degree();
                quotient[cur_q_degree] = cur_q_coeff;

                for (i, div_coeff) in div_poly.coeffs.iter().enumerate() {
                    let mut cq = cur_q_coeff;
                    cq.mul_assign(div_coeff);
                    remainder.coeffs[cur_q_degree + i] = remainder.coeffs[cur_q_degree + i].sub(&cq);
                }
                while let Some(true) = remainder.coeffs.last().map(|c| c.is_zero()) {
                    remainder.coeffs.pop();
                }
            }
            Ok(UniPolynomial::new(quotient))
        }
        
    }
}



pub fn multiexp<E: Pairing>(bases: Vec<E::G1Affine>, exponents: Vec<E::ScalarField>)-> Result<E::G1Affine, PocketError>{
    //TODO: it is a native version, and it will be improved.
    let mut acc = E::G1::zero().into();
    for (e, b) in exponents.iter().zip(bases.iter()) {
        acc = acc.add(&b.mul(e)).into();
    }
    Ok(acc)
}
