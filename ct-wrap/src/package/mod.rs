use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CTWrapPackage {
    pub version: u8,
    pub algorithm_suite: AlgorithmSuite,
    pub key_encapsulations: Vec<KeyEncapsulation>,
    pub encrypted_data: EncryptedData,
    pub signature: Option<Signature>,
    pub zk_proof: Option<ZkProof>,
    pub metadata: Metadata,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlgorithmSuite {
    pub kem: String,
    pub encryption: String,
    pub signature: String,
    pub hash: String,
}

impl Default for AlgorithmSuite {
    fn default() -> Self {
        Self {
            kem: "ML-KEM-1024".to_string(),
            encryption: "AES-256-GCM-SIV".to_string(),
            signature: "ML-DSA-87".to_string(),
            hash: "SHAKE256".to_string(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KeyEncapsulation {
    pub recipient_id: [u8; 32],
    #[serde(with = "serde_bytes")]
    pub kem_ciphertext: Vec<u8>,
    /// KEM-DEM glue: per-recipient wrapping of the content-encryption key (32 bytes).
    ///
    /// Each recipient derives a mask from their ML-KEM shared secret and XORs it with this field
    /// to recover the CEK used for `encrypted_data`.
    pub wrapped_cek: [u8; 32],
    pub x25519_ephemeral: Option<[u8; 32]>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EncryptedData {
    pub nonce: [u8; 12],
    #[serde(with = "serde_bytes")]
    pub ciphertext: Vec<u8>,
    pub aad_hash: [u8; 32],
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Signature {
    pub algorithm: String,
    #[serde(with = "serde_bytes")]
    pub public_key: Vec<u8>,
    #[serde(with = "serde_bytes")]
    pub signature: Vec<u8>,
    pub signed_data_hash: [u8; 32],
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ZkProof {
    pub circuit_id: String,
    pub proof: Groth16ProofData,
    pub public_signals: Vec<String>,
    pub verification_key_hash: [u8; 32],
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Groth16ProofData {
    pub pi_a: Vec<String>,
    pub pi_b: Vec<Vec<String>>,
    pub pi_c: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Metadata {
    pub created_at: u64,
    pub content_type: Option<String>,
    pub content_hash: [u8; 32],
    pub access_policy: Option<AccessPolicy>,
    #[serde(flatten)]
    pub custom: HashMap<String, serde_cbor::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AccessPolicy {
    pub threshold: Option<u32>,
    pub expiry: Option<u64>,
    pub allowed_verifiers: Option<Vec<[u8; 20]>>,
}

impl CTWrapPackage {
    pub fn to_cbor(&self) -> Result<Vec<u8>, serde_cbor::Error> {
        serde_cbor::to_vec(self)
    }

    pub fn from_cbor(bytes: &[u8]) -> Result<Self, serde_cbor::Error> {
        serde_cbor::from_slice(bytes)
    }

    pub fn size(&self) -> usize {
        self.to_cbor().map(|v| v.len()).unwrap_or(0)
    }

    pub fn hash(&self) -> [u8; 32] {
        use sha3::{Digest, Sha3_256};
        let cbor = self.to_cbor().expect("serialization should not fail");
        Sha3_256::digest(&cbor).into()
    }
}
