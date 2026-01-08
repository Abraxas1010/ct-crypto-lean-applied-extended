use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

/// Derive encryption key from ML-KEM shared secret using SHAKE256.
pub fn derive_key(shared_secret: &[u8], context: &[u8], key_length: usize) -> Vec<u8> {
    let mut hasher = Shake256::default();
    hasher.update(b"CT-WRAP-KDF-v1");
    hasher.update(&(shared_secret.len() as u32).to_le_bytes());
    hasher.update(shared_secret);
    hasher.update(&(context.len() as u32).to_le_bytes());
    hasher.update(context);

    let mut reader = hasher.finalize_xof();
    let mut key = vec![0u8; key_length];
    reader.read(&mut key);
    key
}
