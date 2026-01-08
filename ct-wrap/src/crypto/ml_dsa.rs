//! ML-DSA wrapper.
//!
//! We use `pqcrypto-dilithium`'s Dilithium5 implementation as the concrete primitive.
//! Dilithium5 corresponds to the ML-DSA-87 parameter set (FIPS 204).

use zeroize::Zeroize;

use pqcrypto_dilithium::dilithium5;
use pqcrypto_traits::sign as sign_traits;

use super::CryptoError;

/// ML-DSA signing key pair.
pub struct MlDsaKeyPair {
    pub public_key: Vec<u8>,
    secret_key: Vec<u8>,
}

impl MlDsaKeyPair {
    /// Generate new ML-DSA-87 key pair.
    pub fn generate() -> Result<Self, CryptoError> {
        let (pk, sk) = dilithium5::keypair();
        Ok(Self {
            public_key: pk.as_bytes().to_vec(),
            secret_key: sk.as_bytes().to_vec(),
        })
    }

    /// Sign a message.
    pub fn sign(&self, message: &[u8]) -> Result<Vec<u8>, CryptoError> {
        let sk = dilithium5::SecretKey::from_bytes(&self.secret_key).map_err(|_| CryptoError::InvalidKey)?;
        let sig = dilithium5::detached_sign(message, &sk);
        Ok(sig.as_bytes().to_vec())
    }
}

impl Drop for MlDsaKeyPair {
    fn drop(&mut self) {
        self.secret_key.zeroize();
    }
}

/// Verify an ML-DSA signature.
pub fn verify_signature(
    public_key: &[u8],
    message: &[u8],
    signature: &[u8],
) -> Result<bool, CryptoError> {
    let pk = dilithium5::PublicKey::from_bytes(public_key).map_err(|_| CryptoError::InvalidKey)?;
    let sig = dilithium5::DetachedSignature::from_bytes(signature).map_err(|_| CryptoError::Signature)?;
    Ok(dilithium5::verify_detached_signature(&sig, message, &pk).is_ok())
}
