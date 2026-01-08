mod aes_gcm_siv;
mod kdf;
mod ml_dsa;
mod ml_kem;

pub use aes_gcm_siv::{decrypt_aes_gcm_siv, encrypt_aes_gcm_siv, EncryptionResult};
pub use kdf::derive_key;
pub use ml_dsa::{verify_signature, MlDsaKeyPair};
pub use ml_kem::{encapsulate, MlKemEncapsulation, MlKemKeyPair};

use thiserror::Error;

#[derive(Debug, Error)]
pub enum CryptoError {
    #[error("invalid key material")]
    InvalidKey,
    #[error("invalid ciphertext")]
    InvalidCiphertext,
    #[error("encryption error")]
    Encryption,
    #[error("decryption error")]
    Decryption,
    #[error("signature error")]
    Signature,
    #[error("verification error")]
    Verification,
}
