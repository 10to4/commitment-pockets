mod error;
use error::PocketError;

mod poly;
pub use poly::{EvaluationDomain, UniPolynomial};

mod basic;
pub use basic::{BasicParameters, BasicPolyCommit, BasicProof};

mod basic_ped;
pub use basic_ped::{BasicPEDParameters, BasicPEDPolyCommit, BasicPEDProof};

mod multiproof;
pub use multiproof::{
    MultiProof, MultiProofParameters, MultiProofPolyCommit, MultiProofPolyCommit2,
};

mod asvc;
pub use asvc::{ASvccommit, ASvckey, ASvcproof};

mod caulk_single;
pub use caulk_single::{CaulkParameters, CaulkSinglePolyCommit, CaulkSingleProof, PedersenProof};

use ark_ec::pairing::Pairing;
use ark_std::{ops::Add, ops::Mul, Zero};

pub fn multiexp<E: Pairing>(
    bases: &Vec<E::G1Affine>,
    exponents: Vec<E::ScalarField>,
) -> Result<E::G1Affine, PocketError> {
    //TODO: it is a native version, and it will be improved.
    let mut acc = E::G1::zero().into();
    for (e, b) in exponents.iter().zip(bases.iter()) {
        acc = acc.add(&b.mul(e)).into();
    }
    Ok(acc)
}

pub fn multiexp2<E: Pairing>(
    bases: &Vec<E::G2Affine>,
    exponents: Vec<E::ScalarField>,
) -> Result<E::G2Affine, PocketError> {
    //TODO: it is a native version, and it will be improved.
    let mut acc = E::G2::zero().into();
    for (e, b) in exponents.iter().zip(bases.iter()) {
        acc = acc.add(&b.mul(e)).into();
    }
    Ok(acc)
}
