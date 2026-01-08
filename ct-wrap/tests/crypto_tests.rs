use std::collections::HashMap;

use ct_wrap::crypto::{
    decrypt_aes_gcm_siv, encrypt_aes_gcm_siv, encapsulate, derive_key, verify_signature, MlDsaKeyPair,
    MlKemKeyPair,
};
use ct_wrap::wrap::{unwrap as unwrap_pkg, wrap as wrap_pkg, RecipientPublicKey, WrapConfig};

#[test]
fn test_ml_kem_roundtrip() {
    let keypair = MlKemKeyPair::generate().unwrap();
    let encap = encapsulate(&keypair.public_key).unwrap();
    let recovered = keypair.decapsulate(&encap.ciphertext).unwrap();
    assert_eq!(encap.shared_secret, recovered);
}

#[test]
fn test_aes_gcm_siv_roundtrip() {
    let key = [0u8; 32];
    let plaintext = b"Hello, CT-Wrap!";
    let aad = b"metadata";

    let encrypted = encrypt_aes_gcm_siv(&key, plaintext, aad).unwrap();
    let decrypted = decrypt_aes_gcm_siv(&key, &encrypted.nonce, &encrypted.ciphertext, aad).unwrap();
    assert_eq!(plaintext.to_vec(), decrypted);
}

#[test]
fn test_ml_dsa_signature() {
    let keypair = MlDsaKeyPair::generate().unwrap();
    let message = b"Sign this message";

    let signature = keypair.sign(message).unwrap();
    let valid = verify_signature(&keypair.public_key, message, &signature).unwrap();
    assert!(valid);
}

#[test]
fn test_wrap_unwrap_roundtrip() {
    let recipient = MlKemKeyPair::generate().unwrap();
    let data = b"Secret message for testing";

    let config = WrapConfig {
        recipients: vec![RecipientPublicKey {
            ml_kem_pk: recipient.public_key.clone(),
            x25519_pk: None,
        }],
        signer: None,
        generate_zk_proof: false,
        zk_circuit: None,
        content_type: Some("text/plain".to_string()),
        access_policy: None,
        custom_metadata: HashMap::new(),
    };

    let package = wrap_pkg(data, config).unwrap();
    let recovered = unwrap_pkg(&package, &recipient).unwrap();
    assert_eq!(data.to_vec(), recovered);
}
