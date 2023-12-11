use std::ops::MulAssign;

use super::PocketError;
use ark_ec::pairing::Pairing;
use ark_ff::{Field, PrimeField};
use ark_std::{log2, ops::Mul, ops::Sub, vec, One, Zero};
use std::cmp::max;

#[derive(Clone, PartialEq, Eq, Hash, Default)]
pub struct UniPolynomial<E: Pairing> {
    coeffs: Vec<E::ScalarField>,
}

impl<E: Pairing> UniPolynomial<E> {
    pub fn new(coeffs: Vec<E::ScalarField>) -> Self {
        Self { coeffs }
    }

    pub fn deref(&self) -> &[E::ScalarField] {
        &self.coeffs
    }

    pub fn deref_mut(&mut self) -> &mut [E::ScalarField] {
        &mut self.coeffs
    }

    pub fn degree(&self) -> usize {
        self.coeffs.len() - 1
    }

    pub fn is_zero(&self) -> bool {
        self.coeffs.len() == 0
    }

    pub fn zero() -> Self {
        Self::new(vec![])
    }

    pub fn evaluate(&self, value: &E::ScalarField) -> E::ScalarField {
        if self.is_zero() {
            return E::ScalarField::zero();
        }
        let mut cur = E::ScalarField::one();
        let mut sum = E::ScalarField::zero();
        for coeff in self.deref() {
            sum += cur.mul(coeff);
            cur.mul_assign(value);
        }
        sum
    }

    pub fn mulpoly(&self, multi_poly: &UniPolynomial<E>) -> Result<UniPolynomial<E>, PocketError> {
        if self.is_zero() {
            Ok(UniPolynomial::zero())
        } else if multi_poly.is_zero() {
            Err(PocketError::InvalidDivisor)
        } else {
            let poly_degree = self.degree();
            let multi_degree = multi_poly.degree();
            let poly_coeff = self.deref();
            let multi_coeff = multi_poly.deref();
            let mut res_coeff = vec![E::ScalarField::zero(); poly_degree + multi_degree + 1];
            for i in 0..poly_degree + 1 {
                for j in 0..multi_degree + 1 {
                    res_coeff[i + j] += poly_coeff[i] * multi_coeff[j];
                }
            }
            Ok(UniPolynomial::new(res_coeff))
        }
    }

    pub fn div(&self, div_poly: &UniPolynomial<E>) -> Result<UniPolynomial<E>, PocketError> {
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
                    remainder.coeffs[cur_q_degree + i] =
                        remainder.coeffs[cur_q_degree + i].sub(&cq);
                }
                while let Some(true) = remainder.coeffs.last().map(|c| c.is_zero()) {
                    remainder.coeffs.pop();
                }
            }
            Ok(UniPolynomial::new(quotient))
        }
    }

    pub fn mulvalue(&self, value: E::ScalarField) -> Result<UniPolynomial<E>, PocketError> {
        let coeffs = self.coeffs.iter().map(|coeff| coeff.mul(value)).collect();
        Ok(Self { coeffs })
    }

    pub fn addpoly(&self, poly: &UniPolynomial<E>) -> Result<UniPolynomial<E>, PocketError> {
        if self.is_zero() {
            Ok(UniPolynomial::zero())
        } else if poly.is_zero() {
            Err(PocketError::InvalidDivisor)
        } else {
            let self_degree = self.degree();
            let poly_degree = poly.degree();
            let max_degree = max(self_degree, poly_degree);
            let self_coeff = self.deref();
            let poly_coeff = poly.deref();

            let mut res_coeff = vec![E::ScalarField::zero(); max_degree + 1];
            for i in 0..self_degree + 1 {
                res_coeff[i] += self_coeff[i];
            }
            for j in 0..poly_degree + 1 {
                res_coeff[j] += poly_coeff[j];
            }
            Ok(UniPolynomial::new(res_coeff))
        }
    }
}

pub struct EvaluationDomain<E: PrimeField> {
    coeffs: Vec<E>,
    exp: u32,
    omega: E,
    omegainv: E,
    geninv: E,
    minv: E,
}

impl<E: PrimeField> EvaluationDomain<E> {
    pub fn new(coeffs: &Vec<E>) -> Result<Self, PocketError> {
        let mut coeffs: Vec<E> = coeffs.clone();
        if !coeffs.len().is_power_of_two() {
            let num_coeffs = coeffs.len().checked_next_power_of_two().unwrap();
            coeffs.resize(num_coeffs, E::zero());
        }
        let len = coeffs.len();

        let exp = log2(coeffs.len());

        let mut omega = E::TWO_ADIC_ROOT_OF_UNITY;
        for _ in exp..E::TWO_ADICITY {
            omega.square_in_place();
        }

        Ok(Self {
            coeffs,
            exp,
            omega,
            omegainv: omega.inverse().unwrap(),
            geninv: E::GENERATOR.inverse().unwrap(),
            minv: E::from_be_bytes_mod_order(&len.to_be_bytes())
                .inverse()
                .unwrap(),
        })
    }

    pub fn as_ref(&self) -> &Vec<E> {
        &self.coeffs
    }

    pub fn omega(&self) -> E {
        self.omega
    }

    fn init_reverse(&mut self) {
        let log_n = self.exp;
        assert_eq!(self.coeffs.len(), 1 << log_n);

        for i in 0..self.coeffs.len() {
            let mut r = 0;
            let mut t = i;
            for _ in 0..log_n {
                r = r * 2 + t % 2;
                t /= 2
            }
            assert_eq!(t, 0);

            if r < i {
                self.coeffs.swap(r, i);
            }
        }
    }

    pub fn fft(&mut self) {
        let omega = self.omega;

        let log_n = self.exp;
        self.init_reverse();
        let l = self.coeffs.len();
        let mut f = l / 2;
        let mut t = 2;

        for _ in 0..log_n {
            let m = omega.pow([f as u64]);
            for j in 0..f {
                let mut w = E::one();
                for k in 0..t / 2 {
                    let a_add = self.coeffs[j * t + k];
                    let mut a_sub = self.coeffs[j * t + t / 2 + k];
                    a_sub = a_sub.mul(&w);

                    self.coeffs[j * t + k] = self.coeffs[j * t + k].add(&a_sub);
                    self.coeffs[j * t + t / 2 + k] = a_add;
                    self.coeffs[j * t + t / 2 + k] = self.coeffs[j * t + t / 2 + k].sub(&a_sub);
                    w.mul_assign(&m);
                }
            }
            f /= 2;
            t *= 2;
        }
    }

    pub fn ifft(&mut self) {
        let minv = self.minv;
        let omega = self.omegainv;
        let log_n = self.exp;
        self.init_reverse();
        let l = self.coeffs.len();
        let mut f = l / 2;
        let mut t = 2;

        for _ in 0..log_n {
            let m = omega.pow([f as u64]);
            for j in 0..f {
                let mut w = E::one();
                for k in 0..t / 2 {
                    let a_add = self.coeffs[j * t + k];
                    let mut a_sub = self.coeffs[j * t + t / 2 + k];
                    a_sub = a_sub.mul(&w);

                    self.coeffs[j * t + k] = self.coeffs[j * t + k].add(&a_sub);
                    self.coeffs[j * t + t / 2 + k] = a_add;
                    self.coeffs[j * t + t / 2 + k] = self.coeffs[j * t + t / 2 + k].sub(&a_sub);
                    w.mul_assign(&m);
                }
            }
            f /= 2;
            t *= 2;
        }

        self.coeffs = self.coeffs.iter().map(|coeff| coeff.mul(minv)).collect();
    }

    pub fn coset_fft(&mut self) {
        self.distribute_powers(E::GENERATOR);
        self.fft();
    }

    pub fn coset_ifft(&mut self) {
        let geninv = self.geninv;

        self.ifft();
        self.distribute_powers(geninv);
    }

    pub fn distribute_powers(&mut self, g: E) {
        let mut u = g.pow([0]);

        self.coeffs = self
            .coeffs
            .iter()
            .map(|coeff| {
                let coeff = coeff.mul(&u);
                u.mul_assign(&g);
                coeff
            })
            .collect();
    }
}

#[cfg(test)]
mod evaldomain {
    use super::EvaluationDomain;
    use ark_bls12_381::Fr;
    use ark_ff::UniformRand;
    use rand::thread_rng;

    #[test]
    fn test_evaluation_domain() {
        let rng: &mut rand::rngs::ThreadRng = &mut thread_rng();
        let coeffs = vec![
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
            Fr::rand(rng),
        ];
        println!("coeffs = {:?}", coeffs);
        let mut domain = EvaluationDomain::<Fr>::new(&coeffs).unwrap();
        domain.fft();
        println!("after fft: values = {:?}", domain.as_ref());
        domain.ifft();
        println!("after ifft: coeffs = {:?}", domain.as_ref());
        for i in 0..coeffs.len() {
            assert_eq!(coeffs[i], domain.as_ref()[i]);
        }

        domain.coset_ifft();
        println!("after coset ifft: coeffs = {:?}", domain.as_ref());
        domain.coset_fft();
        println!("after coset fft: coeffs = {:?}", domain.as_ref());
        for i in 0..coeffs.len() {
            assert_eq!(coeffs[i], domain.as_ref()[i]);
        }
    }
}
