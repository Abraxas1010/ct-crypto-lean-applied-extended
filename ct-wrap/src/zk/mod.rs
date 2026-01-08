mod prover;
mod verifier;

pub use prover::{generate_proof, Groth16Proof, ZkProofResult};
pub use verifier::{verify_proof, VerifyResult};
