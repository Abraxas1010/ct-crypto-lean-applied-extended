use std::collections::HashMap;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

use rand::RngCore;
use sha3::{Digest, Sha3_256};

use crate::crypto::{
    decrypt_aes_gcm_siv, derive_key, encapsulate, encrypt_aes_gcm_siv, verify_signature,
    MlDsaKeyPair, MlKemKeyPair,
};
use crate::package::*;
use crate::zk::generate_proof;
use crate::zk::verify_proof;

pub struct RecipientPublicKey {
    pub ml_kem_pk: Vec<u8>,
    pub x25519_pk: Option<[u8; 32]>,
}

pub struct WrapConfig {
    pub recipients: Vec<RecipientPublicKey>,
    pub signer: Option<MlDsaKeyPair>,
    pub generate_zk_proof: bool,
    pub zk_circuit: Option<String>,
    pub content_type: Option<String>,
    pub access_policy: Option<AccessPolicy>,
    pub custom_metadata: HashMap<String, serde_cbor::Value>,
}

pub fn wrap(data: &[u8], config: WrapConfig) -> Result<CTWrapPackage, Box<dyn std::error::Error>> {
    let content_hash: [u8; 32] = Sha3_256::digest(data).into();
    let timestamp = SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs();

    let aad = prepare_aad(&content_hash, timestamp, &config);

    // 1. Generate a fresh content-encryption key (CEK).
    let mut cek = [0u8; 32];
    rand::rngs::OsRng.fill_bytes(&mut cek);

    // 2. For each recipient, encapsulate and wrap the CEK.
    let mut key_encapsulations = Vec::with_capacity(config.recipients.len());

    for recipient in &config.recipients {
        let recipient_id: [u8; 32] = Sha3_256::digest(&recipient.ml_kem_pk).into();
        let encap = encapsulate(&recipient.ml_kem_pk)?;
        let mask = derive_key(&encap.shared_secret, b"CT-WRAP-CEK-MASK-v1", 32);
        let mask32: [u8; 32] = mask.try_into().map_err(|_| "invalid mask length")?;
        let mut wrapped_cek = [0u8; 32];
        for i in 0..32 {
            wrapped_cek[i] = cek[i] ^ mask32[i];
        }
        key_encapsulations.push(KeyEncapsulation {
            recipient_id,
            kem_ciphertext: encap.ciphertext,
            wrapped_cek,
            x25519_ephemeral: None,
        });
    }

    // 3. Encrypt.
    let encrypted = encrypt_aes_gcm_siv(&cek, data, &aad)?;

    // 4. Sign (optional).
    let signature = if let Some(signer) = &config.signer {
        let sign_data =
            prepare_sign_data_fields(&encrypted.nonce, &encrypted.aad_hash, &content_hash);
        let sig = signer.sign(&sign_data)?;
        Some(Signature {
            algorithm: "ML-DSA-87".to_string(),
            public_key: signer.public_key.clone(),
            signature: sig,
            signed_data_hash: Sha3_256::digest(&sign_data).into(),
        })
    } else {
        None
    };

    // 5. ZK proof (optional).
    let zk_proof = if config.generate_zk_proof {
        let circuit = config.zk_circuit.as_deref().unwrap_or("data_commitment");
        let build_dir = Path::new("build/circuits");
        let proof_result = generate_proof(data, circuit, build_dir)?;

        let vk_path = build_dir.join(format!("{circuit}_verification_key.json"));
        let vk_bytes = fs::read(&vk_path).map_err(|_| {
            format!(
                "missing verification key for circuit '{circuit}' at {} (run scripts/setup_circuits.sh)",
                vk_path.display()
            )
        })?;
        let verification_key_hash: [u8; 32] = Sha3_256::digest(&vk_bytes).into();

        Some(ZkProof {
            circuit_id: circuit.to_string(),
            proof: Groth16ProofData {
                pi_a: vec![
                    proof_result.proof.pi_a[0].clone(),
                    proof_result.proof.pi_a[1].clone(),
                ],
                pi_b: vec![
                    vec![
                        proof_result.proof.pi_b[0][0].clone(),
                        proof_result.proof.pi_b[0][1].clone(),
                    ],
                    vec![
                        proof_result.proof.pi_b[1][0].clone(),
                        proof_result.proof.pi_b[1][1].clone(),
                    ],
                ],
                pi_c: vec![
                    proof_result.proof.pi_c[0].clone(),
                    proof_result.proof.pi_c[1].clone(),
                ],
            },
            public_signals: proof_result.public_signals,
            verification_key_hash,
        })
    } else {
        None
    };

    Ok(CTWrapPackage {
        version: 1,
        algorithm_suite: AlgorithmSuite::default(),
        key_encapsulations,
        encrypted_data: EncryptedData {
            nonce: encrypted.nonce,
            ciphertext: encrypted.ciphertext,
            aad_hash: encrypted.aad_hash,
        },
        signature,
        zk_proof,
        metadata: Metadata {
            created_at: timestamp,
            content_type: config.content_type,
            content_hash,
            access_policy: config.access_policy,
            custom: config.custom_metadata,
        },
    })
}

pub struct UnwrapConfig {
    pub verify_zk_proof: bool,
    pub build_dir: Option<PathBuf>,
}

impl Default for UnwrapConfig {
    fn default() -> Self {
        Self {
            verify_zk_proof: false,
            build_dir: None,
        }
    }
}

pub fn unwrap_with_config(
    package: &CTWrapPackage,
    recipient_keypair: &MlKemKeyPair,
    config: UnwrapConfig,
) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let recipient_id: [u8; 32] = Sha3_256::digest(&recipient_keypair.public_key).into();
    let our_encap = package
        .key_encapsulations
        .iter()
        .find(|e| e.recipient_id == recipient_id)
        .ok_or("no key encapsulation for this recipient")?;

    let shared_secret = recipient_keypair.decapsulate(&our_encap.kem_ciphertext)?;
    let mask = derive_key(&shared_secret, b"CT-WRAP-CEK-MASK-v1", 32);
    let mask32: [u8; 32] = mask.try_into().map_err(|_| "invalid mask length")?;
    let mut cek = [0u8; 32];
    for i in 0..32 {
        cek[i] = our_encap.wrapped_cek[i] ^ mask32[i];
    }

    let aad = prepare_aad(
        &package.metadata.content_hash,
        package.metadata.created_at,
        &WrapConfig {
            recipients: vec![],
            signer: None,
            generate_zk_proof: false,
            zk_circuit: None,
            content_type: package.metadata.content_type.clone(),
            access_policy: package.metadata.access_policy.clone(),
            custom_metadata: package.metadata.custom.clone(),
        },
    );

    let expected_hash: [u8; 32] = Sha3_256::digest(&aad).into();
    if expected_hash != package.encrypted_data.aad_hash {
        return Err("AAD hash mismatch".into());
    }

    if let Some(sig) = &package.signature {
        let sign_data = prepare_sign_data_fields(
            &package.encrypted_data.nonce,
            &package.encrypted_data.aad_hash,
            &package.metadata.content_hash,
        );

        let expected_signed_data_hash: [u8; 32] = Sha3_256::digest(&sign_data).into();
        if expected_signed_data_hash != sig.signed_data_hash {
            return Err("signed_data_hash mismatch".into());
        }

        let valid = verify_signature(&sig.public_key, &sign_data, &sig.signature)?;
        if !valid {
            return Err("signature verification failed".into());
        }
    }

    let plaintext = decrypt_aes_gcm_siv(
        &cek,
        &package.encrypted_data.nonce,
        &package.encrypted_data.ciphertext,
        &aad,
    )?;

    let content_hash: [u8; 32] = Sha3_256::digest(&plaintext).into();
    if content_hash != package.metadata.content_hash {
        return Err("content hash mismatch".into());
    }

    if config.verify_zk_proof {
        if let Some(zk) = &package.zk_proof {
            let build_dir = config
                .build_dir
                .ok_or("verify_zk_proof requested but build_dir was not provided")?;
            let result = verify_proof(zk, &build_dir)?;
            if !result.valid {
                return Err("zk proof verification failed".into());
            }
        }
    }

    Ok(plaintext)
}

pub fn unwrap(
    package: &CTWrapPackage,
    recipient_keypair: &MlKemKeyPair,
) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    unwrap_with_config(package, recipient_keypair, UnwrapConfig::default())
}

fn prepare_aad(content_hash: &[u8; 32], timestamp: u64, config: &WrapConfig) -> Vec<u8> {
    let mut aad = Vec::new();
    aad.extend_from_slice(b"CT-WRAP-AAD-v1");
    aad.extend_from_slice(content_hash);
    aad.extend_from_slice(&timestamp.to_le_bytes());
    if let Some(ct) = &config.content_type {
        aad.extend_from_slice(ct.as_bytes());
    }
    aad
}

fn prepare_sign_data_fields(
    nonce: &[u8; 12],
    aad_hash: &[u8; 32],
    content_hash: &[u8; 32],
) -> Vec<u8> {
    let mut data = Vec::new();
    data.extend_from_slice(b"CT-WRAP-SIGN-v1");
    data.extend_from_slice(nonce);
    data.extend_from_slice(aad_hash);
    data.extend_from_slice(content_hash);
    data
}
