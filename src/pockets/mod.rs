mod error;
use error::PocketError;

mod poly;
pub use poly::{UniPolynomial, EvaluationDomain};

mod basic;
pub use basic::{BasicParameters, BasicPolyCommit, BasicProof};

mod basic_ped;
pub use basic_ped::{BasicPEDParameters, BasicPEDPolyCommit, BasicPEDProof};

mod multiproof;
pub use multiproof::{MultiProofParameters, MultiProofPolyCommit, MultiProofPolyCommit2, MultiProof};

// mod caulk_single;

use ark_ec::pairing::Pairing;
use ark_std::{ops::Mul, ops::Add, Zero};


pub fn multiexp<E: Pairing>(bases: Vec<E::G1Affine>, exponents: Vec<E::ScalarField>)-> Result<E::G1Affine, PocketError>{
    //TODO: it is a native version, and it will be improved.
    let mut acc = E::G1::zero().into();
    for (e, b) in exponents.iter().zip(bases.iter()) {
        acc = acc.add(&b.mul(e)).into();
    }
    Ok(acc)
}

pub fn multiexp2<E: Pairing>(bases: Vec<E::G2Affine>, exponents: Vec<E::ScalarField>)-> Result<E::G2Affine, PocketError>{
    //TODO: it is a native version, and it will be improved.
    let mut acc = E::G2::zero().into();
    for (e, b) in exponents.iter().zip(bases.iter()) {
        acc = acc.add(&b.mul(e)).into();
    }
    Ok(acc)
}