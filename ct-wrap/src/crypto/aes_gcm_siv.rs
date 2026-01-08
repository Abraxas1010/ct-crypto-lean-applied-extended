use aes_gcm_siv::{
    aead::{Aead, KeyInit, Payload},
    Aes256GcmSiv, Nonce,
};
use rand::rngs::OsRng;
use rand::RngCore;
use sha3::{Digest, Sha3_256};

use super::CryptoError;

/// Encryption result containing all components.
pub struct EncryptionResult {
    pub nonce: [u8; 12],
    pub ciphertext: Vec<u8>, // includes auth tag
    pub aad_hash: [u8; 32],
}

pub fn encrypt_aes_gcm_siv(
    key: &[u8; 32],
    plaintext: &[u8],
    aad: &[u8],
) -> Result<EncryptionResult, CryptoError> {
    let mut nonce_bytes = [0u8; 12];
    OsRng.fill_bytes(&mut nonce_bytes);
    let nonce = Nonce::from_slice(&nonce_bytes);

    let cipher = Aes256GcmSiv::new_from_slice(key).map_err(|_| CryptoError::InvalidKey)?;
    let ciphertext = cipher
        .encrypt(
            nonce,
            Payload {
                msg: plaintext,
                aad,
            },
        )
        .map_err(|_| CryptoError::Encryption)?;

    let aad_hash: [u8; 32] = Sha3_256::digest(aad).into();

    Ok(EncryptionResult {
        nonce: nonce_bytes,
        ciphertext,
        aad_hash,
    })
}

pub fn decrypt_aes_gcm_siv(
    key: &[u8; 32],
    nonce: &[u8; 12],
    ciphertext: &[u8],
    aad: &[u8],
) -> Result<Vec<u8>, CryptoError> {
    let cipher = Aes256GcmSiv::new_from_slice(key).map_err(|_| CryptoError::InvalidKey)?;
    let nonce = Nonce::from_slice(nonce);
    cipher
        .decrypt(
            nonce,
            Payload {
                msg: ciphertext,
                aad,
            },
        )
        .map_err(|_| CryptoError::Decryption)
}
