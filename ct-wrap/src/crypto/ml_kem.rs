//! ML-KEM wrapper.
//!
//! We use `pqcrypto-kyber`'s Kyber1024 implementation as the concrete primitive.
//! Kyber1024 corresponds to the ML-KEM-1024 parameter set (FIPS 203).

use zeroize::Zeroize;

use pqcrypto_kyber::kyber1024;
use pqcrypto_traits::kem as kem_traits;

use super::CryptoError;

/// ML-KEM key pair for a recipient.
pub struct MlKemKeyPair {
    pub public_key: Vec<u8>,
    pub(crate) secret_key: Vec<u8>,
}

/// Encapsulated key for transmission.
pub struct MlKemEncapsulation {
    pub ciphertext: Vec<u8>,
    pub shared_secret: Vec<u8>,
}

impl MlKemKeyPair {
    /// Generate a new ML-KEM-1024 key pair.
    pub fn generate() -> Result<Self, CryptoError> {
        let (pk, sk) = kyber1024::keypair();
        Ok(Self {
            public_key: pk.as_bytes().to_vec(),
            secret_key: sk.as_bytes().to_vec(),
        })
    }

    /// Decapsulate to recover shared secret.
    pub fn decapsulate(&self, ciphertext: &[u8]) -> Result<Vec<u8>, CryptoError> {
        let sk = kyber1024::SecretKey::from_bytes(&self.secret_key).map_err(|_| CryptoError::InvalidKey)?;
        let ct = kyber1024::Ciphertext::from_bytes(ciphertext).map_err(|_| CryptoError::InvalidCiphertext)?;
        let ss = kyber1024::decapsulate(&ct, &sk);
        Ok(ss.as_bytes().to_vec())
    }

    /// Serialize public key for distribution.
    pub fn public_key_bytes(&self) -> &[u8] {
        &self.public_key
    }

    /// Reconstruct a keypair from raw bytes (e.g. API input).
    pub fn from_bytes(public_key: Vec<u8>, secret_key: Vec<u8>) -> Self {
        Self { public_key, secret_key }
    }
}

impl Drop for MlKemKeyPair {
    fn drop(&mut self) {
        self.secret_key.zeroize();
    }
}

/// Encapsulate a shared secret to a recipient's public key.
pub fn encapsulate(recipient_public_key: &[u8]) -> Result<MlKemEncapsulation, CryptoError> {
    let pk = kyber1024::PublicKey::from_bytes(recipient_public_key).map_err(|_| CryptoError::InvalidKey)?;
    let (ss, ct) = kyber1024::encapsulate(&pk);
    Ok(MlKemEncapsulation {
        ciphertext: ct.as_bytes().to_vec(),
        shared_secret: ss.as_bytes().to_vec(),
    })
}
