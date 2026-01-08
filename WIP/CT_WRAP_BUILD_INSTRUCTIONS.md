# CT-Wrap: Quantum-Safe Data Wrapper with ZK Proofs
## Complete LLM Coding Agent Build Instructions

**Product:** CT-Wrap by AgentPMT
**Purpose:** Universal data wrapper providing post-quantum encryption + zero-knowledge proof generation for blockchain storage and verification
**Target:** Standalone product where users submit data → receive encrypted package + ZK proof → can store anywhere and prove validity without decryption

---

## Table of Contents

1. [System Architecture Overview](#1-system-architecture-overview)
2. [Technology Stack](#2-technology-stack)
3. [Phase 1: Core Cryptographic Layer](#3-phase-1-core-cryptographic-layer)
4. [Phase 2: ZK Proof System](#4-phase-2-zk-proof-system)
5. [Phase 3: Wrapper Serialization](#5-phase-3-wrapper-serialization)
6. [Phase 4: API Service Layer](#6-phase-4-api-service-layer)
7. [Phase 5: Smart Contract Verification](#7-phase-5-smart-contract-verification)
8. [Phase 6: SDK and Client Libraries](#8-phase-6-sdk-and-client-libraries)
9. [Testing Requirements](#9-testing-requirements)
10. [Security Considerations](#10-security-considerations)

---

## 1. System Architecture Overview

### 1.1 High-Level Data Flow

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              CT-WRAP SYSTEM                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  INPUT                                                                      │
│  ──────                                                                     │
│  • Raw data (any bytes)                                                     │
│  • Recipient public keys (ML-KEM)                                           │
│  • Access policy (optional)                                                 │
│  • Metadata (optional)                                                      │
│                                                                             │
│                              ┌─────────────────┐                            │
│                              │  1. KEY LAYER   │                            │
│                              │  ─────────────  │                            │
│                              │  ML-KEM-1024    │                            │
│                              │  (FIPS 203)     │                            │
│                              │  Key Encaps     │                            │
│                              └────────┬────────┘                            │
│                                       │                                     │
│                                       ▼                                     │
│                              ┌─────────────────┐                            │
│                              │ 2. ENCRYPT LAYER│                            │
│                              │ ─────────────── │                            │
│                              │ AES-256-GCM-SIV │                            │
│                              │ (RFC 8452)      │                            │
│                              │ AEAD Encryption │                            │
│                              └────────┬────────┘                            │
│                                       │                                     │
│                         ┌─────────────┴─────────────┐                       │
│                         ▼                           ▼                       │
│              ┌─────────────────┐         ┌─────────────────┐                │
│              │ 3. ZK PROOF     │         │ 4. SIGNATURE    │                │
│              │ ─────────────   │         │ ─────────────   │                │
│              │ Groth16/PLONK   │         │ ML-DSA-87       │                │
│              │ Circom Circuit  │         │ (FIPS 204)      │                │
│              │ Validity Proof  │         │ Data Signature  │                │
│              └────────┬────────┘         └────────┬────────┘                │
│                       │                           │                         │
│                       └─────────────┬─────────────┘                         │
│                                     ▼                                       │
│                          ┌─────────────────────┐                            │
│                          │  5. PACKAGE LAYER   │                            │
│                          │  ─────────────────  │                            │
│                          │  CBOR Serialization │                            │
│                          │  Blockchain-Ready   │                            │
│                          └──────────┬──────────┘                            │
│                                     │                                       │
│  OUTPUT                             ▼                                       │
│  ──────                                                                     │
│  • CTWrap Package (bytes)                                                   │
│  • ZK Proof (can verify without decryption)                                 │
│  • Verification Key (public)                                                │
│  • Decryption possible with recipient private key                           │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 1.2 Core Capabilities

| Capability | Description | Standard/Specification |
|------------|-------------|----------------------|
| Post-Quantum Key Exchange | ML-KEM-1024 key encapsulation | NIST FIPS 203 |
| Post-Quantum Signatures | ML-DSA-87 digital signatures | NIST FIPS 204 |
| Authenticated Encryption | AES-256-GCM-SIV | RFC 8452 |
| Zero-Knowledge Proofs | Groth16 or PLONK SNARKs | circom/snarkjs |
| Serialization | CBOR binary format | RFC 8949 |
| Blockchain Verification | Solidity/EVM verifier contracts | EIP-197 (BN254) |

### 1.3 Key Security Properties

1. **Post-Quantum Security**: Key exchange and signatures resist quantum attacks
2. **Forward Secrecy**: Each wrap uses fresh ephemeral keys
3. **Nonce Misuse Resistance**: AES-GCM-SIV tolerates accidental nonce reuse
4. **Zero-Knowledge**: Prove data properties without revealing content
5. **Integrity**: AEAD authentication + ML-DSA signatures
6. **Auditability**: All operations produce verifiable proofs

---

## 2. Technology Stack

### 2.1 Backend Service (Rust)

**Primary Language:** Rust (for performance and memory safety)

```toml
# Cargo.toml dependencies
[dependencies]
# Post-Quantum Cryptography
oqs = "0.9"                          # liboqs Rust bindings (ML-KEM, ML-DSA)
pqcrypto-kyber = "0.8"               # Alternative: pqcrypto ML-KEM
pqcrypto-dilithium = "0.5"           # Alternative: pqcrypto ML-DSA

# Classical Cryptography
aes-gcm-siv = "0.11"                 # AES-256-GCM-SIV AEAD
rand = "0.8"                         # Secure random generation
sha3 = "0.10"                        # SHA3/SHAKE for KDF

# Serialization
serde = { version = "1.0", features = ["derive"] }
serde_cbor = "0.11"                  # CBOR encoding
hex = "0.4"
base64 = "0.21"

# ZK Proofs (via FFI to snarkjs or native)
ark-groth16 = "0.4"                  # Native Groth16
ark-bn254 = "0.4"                    # BN254 curve
ark-serialize = "0.4"

# Web Framework
axum = "0.7"                         # HTTP API
tokio = { version = "1", features = ["full"] }
tower-http = { version = "0.5", features = ["cors"] }

# Database (optional, for key management)
sqlx = { version = "0.7", features = ["postgres", "runtime-tokio"] }
```

### 2.2 ZK Circuit Layer (Circom + snarkjs)

**Circuit Language:** Circom 2.x
**Proof Generation:** snarkjs (JavaScript/WASM)

```bash
# Install circom compiler
curl -L https://github.com/iden3/circom/releases/download/v2.1.8/circom-linux-amd64 -o /usr/local/bin/circom
chmod +x /usr/local/bin/circom

# Install snarkjs
npm install -g snarkjs

# Install circomlib (standard circuit library)
npm install circomlib
```

### 2.3 Smart Contracts (Solidity)

**Target Chain:** EVM-compatible (Ethereum, Base, Polygon, etc.)
**ZK Verifier:** BN254 pairing (EIP-197)

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;
```

### 2.4 Client SDKs

| Language | Primary Use Case |
|----------|-----------------|
| TypeScript/JavaScript | Web, Node.js, browser |
| Python | Data science, scripting, AI agents |
| Rust | High-performance, embedded |

---

## 3. Phase 1: Core Cryptographic Layer

### 3.1 ML-KEM Key Encapsulation (FIPS 203)

**Specification Reference:** https://csrc.nist.gov/pubs/fips/203/final

ML-KEM (Module-Lattice-Based Key-Encapsulation Mechanism) provides post-quantum secure key establishment.

#### 3.1.1 Parameter Set Selection

| Parameter Set | Security Level | Public Key Size | Ciphertext Size | Shared Secret |
|---------------|----------------|-----------------|-----------------|---------------|
| ML-KEM-512 | NIST Level 1 | 800 bytes | 768 bytes | 32 bytes |
| ML-KEM-768 | NIST Level 3 | 1184 bytes | 1088 bytes | 32 bytes |
| ML-KEM-1024 | NIST Level 5 | 1568 bytes | 1568 bytes | 32 bytes |

**Recommendation:** Use ML-KEM-1024 for maximum security.

#### 3.1.2 Implementation (Rust with liboqs)

```rust
use oqs::kem::{Kem, Algorithm as KemAlgorithm};
use oqs::Error as OqsError;

/// ML-KEM key pair for a recipient
pub struct MlKemKeyPair {
    pub public_key: Vec<u8>,
    secret_key: Vec<u8>,
}

/// Encapsulated key for transmission
pub struct MlKemEncapsulation {
    pub ciphertext: Vec<u8>,      // Send to recipient
    pub shared_secret: Vec<u8>,   // Use for AES key derivation
}

impl MlKemKeyPair {
    /// Generate a new ML-KEM-1024 key pair
    pub fn generate() -> Result<Self, OqsError> {
        oqs::init(); // Initialize liboqs (call once at startup)
        
        let kem = Kem::new(KemAlgorithm::MlKem1024)?;
        let (pk, sk) = kem.keypair()?;
        
        Ok(Self {
            public_key: pk.into_vec(),
            secret_key: sk.into_vec(),
        })
    }
    
    /// Decapsulate to recover shared secret
    pub fn decapsulate(&self, ciphertext: &[u8]) -> Result<Vec<u8>, OqsError> {
        let kem = Kem::new(KemAlgorithm::MlKem1024)?;
        let sk = kem.secret_key_from_bytes(&self.secret_key)?;
        let ct = kem.ciphertext_from_bytes(ciphertext)?;
        
        let shared_secret = kem.decapsulate(&sk, &ct)?;
        Ok(shared_secret.into_vec())
    }
    
    /// Serialize public key for distribution
    pub fn public_key_bytes(&self) -> &[u8] {
        &self.public_key
    }
}

/// Encapsulate a shared secret to a recipient's public key
pub fn encapsulate(recipient_public_key: &[u8]) -> Result<MlKemEncapsulation, OqsError> {
    let kem = Kem::new(KemAlgorithm::MlKem1024)?;
    let pk = kem.public_key_from_bytes(recipient_public_key)?;
    
    let (ct, ss) = kem.encapsulate(&pk)?;
    
    Ok(MlKemEncapsulation {
        ciphertext: ct.into_vec(),
        shared_secret: ss.into_vec(),
    })
}
```

#### 3.1.3 Key Derivation Function

Derive the AES-256 key from the ML-KEM shared secret using SHAKE256:

```rust
use sha3::{Shake256, digest::{ExtendableOutput, Update, XofReader}};

/// Derive encryption key from ML-KEM shared secret
/// 
/// # Arguments
/// * `shared_secret` - 32-byte ML-KEM shared secret
/// * `context` - Application-specific context string
/// * `key_length` - Desired key length in bytes (32 for AES-256)
pub fn derive_key(
    shared_secret: &[u8],
    context: &[u8],
    key_length: usize,
) -> Vec<u8> {
    let mut hasher = Shake256::default();
    
    // Domain separation
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
```

### 3.2 AES-256-GCM-SIV Encryption (RFC 8452)

**Specification Reference:** https://www.rfc-editor.org/rfc/rfc8452.html

AES-GCM-SIV provides nonce misuse-resistant authenticated encryption.

#### 3.2.1 Parameters

| Parameter | Value |
|-----------|-------|
| Key size | 256 bits (32 bytes) |
| Nonce size | 96 bits (12 bytes) |
| Tag size | 128 bits (16 bytes) |
| Max plaintext | 2^36 bytes per key/nonce |

#### 3.2.2 Implementation

```rust
use aes_gcm_siv::{
    Aes256GcmSiv, Nonce, 
    aead::{Aead, KeyInit, OsRng, rand_core::RngCore},
};

/// Encryption result containing all components
pub struct EncryptionResult {
    pub nonce: [u8; 12],
    pub ciphertext: Vec<u8>,  // Includes 16-byte auth tag
    pub aad_hash: [u8; 32],   // SHA3-256 of AAD for verification
}

/// Encrypt data using AES-256-GCM-SIV
/// 
/// # Arguments
/// * `key` - 32-byte encryption key (from KDF)
/// * `plaintext` - Data to encrypt
/// * `aad` - Additional authenticated data (metadata, not encrypted)
pub fn encrypt_aes_gcm_siv(
    key: &[u8; 32],
    plaintext: &[u8],
    aad: &[u8],
) -> Result<EncryptionResult, aes_gcm_siv::Error> {
    // Generate random 96-bit nonce
    let mut nonce_bytes = [0u8; 12];
    OsRng.fill_bytes(&mut nonce_bytes);
    let nonce = Nonce::from_slice(&nonce_bytes);
    
    // Initialize cipher
    let cipher = Aes256GcmSiv::new_from_slice(key)
        .expect("Invalid key length");
    
    // Encrypt with AAD
    let ciphertext = cipher.encrypt(nonce, aes_gcm_siv::aead::Payload {
        msg: plaintext,
        aad,
    })?;
    
    // Hash AAD for later verification
    use sha3::{Sha3_256, Digest};
    let aad_hash: [u8; 32] = Sha3_256::digest(aad).into();
    
    Ok(EncryptionResult {
        nonce: nonce_bytes,
        ciphertext,
        aad_hash,
    })
}

/// Decrypt data using AES-256-GCM-SIV
pub fn decrypt_aes_gcm_siv(
    key: &[u8; 32],
    nonce: &[u8; 12],
    ciphertext: &[u8],
    aad: &[u8],
) -> Result<Vec<u8>, aes_gcm_siv::Error> {
    let cipher = Aes256GcmSiv::new_from_slice(key)
        .expect("Invalid key length");
    let nonce = Nonce::from_slice(nonce);
    
    cipher.decrypt(nonce, aes_gcm_siv::aead::Payload {
        msg: ciphertext,
        aad,
    })
}
```

### 3.3 ML-DSA Signatures (FIPS 204)

**Specification Reference:** https://csrc.nist.gov/pubs/fips/204/final

ML-DSA (Module-Lattice-Based Digital Signature Algorithm) provides post-quantum signatures.

#### 3.3.1 Parameter Sets

| Parameter Set | Security Level | Public Key | Signature Size |
|---------------|----------------|------------|----------------|
| ML-DSA-44 | NIST Level 2 | 1312 bytes | 2420 bytes |
| ML-DSA-65 | NIST Level 3 | 1952 bytes | 3293 bytes |
| ML-DSA-87 | NIST Level 5 | 2592 bytes | 4595 bytes |

**Recommendation:** Use ML-DSA-87 for consistency with ML-KEM-1024.

#### 3.3.2 Implementation

```rust
use oqs::sig::{Sig, Algorithm as SigAlgorithm};

/// ML-DSA signing key pair
pub struct MlDsaKeyPair {
    pub public_key: Vec<u8>,
    secret_key: Vec<u8>,
}

impl MlDsaKeyPair {
    /// Generate new ML-DSA-87 key pair
    pub fn generate() -> Result<Self, oqs::Error> {
        let sig = Sig::new(SigAlgorithm::MlDsa87)?;
        let (pk, sk) = sig.keypair()?;
        
        Ok(Self {
            public_key: pk.into_vec(),
            secret_key: sk.into_vec(),
        })
    }
    
    /// Sign a message
    pub fn sign(&self, message: &[u8]) -> Result<Vec<u8>, oqs::Error> {
        let sig = Sig::new(SigAlgorithm::MlDsa87)?;
        let sk = sig.secret_key_from_bytes(&self.secret_key)?;
        
        let signature = sig.sign(message, &sk)?;
        Ok(signature.into_vec())
    }
}

/// Verify an ML-DSA signature
pub fn verify_signature(
    public_key: &[u8],
    message: &[u8],
    signature: &[u8],
) -> Result<bool, oqs::Error> {
    let sig = Sig::new(SigAlgorithm::MlDsa87)?;
    let pk = sig.public_key_from_bytes(public_key)?;
    let sig_obj = sig.signature_from_bytes(signature)?;
    
    Ok(sig.verify(message, &sig_obj, &pk).is_ok())
}
```

### 3.4 Hybrid Key Exchange (Optional Enhancement)

For defense-in-depth, combine ML-KEM with X25519:

```rust
use x25519_dalek::{EphemeralSecret, PublicKey, SharedSecret};

/// Hybrid key exchange: ML-KEM-1024 + X25519
pub struct HybridEncapsulation {
    pub ml_kem_ciphertext: Vec<u8>,
    pub x25519_public: [u8; 32],
    combined_secret: Vec<u8>,
}

pub fn hybrid_encapsulate(
    ml_kem_public: &[u8],
    x25519_public: &PublicKey,
) -> Result<HybridEncapsulation, oqs::Error> {
    // ML-KEM encapsulation
    let ml_kem = encapsulate(ml_kem_public)?;
    
    // X25519 key exchange
    let ephemeral = EphemeralSecret::random();
    let x25519_pk = PublicKey::from(&ephemeral);
    let x25519_shared = ephemeral.diffie_hellman(x25519_public);
    
    // Combine secrets with domain separation
    let combined = derive_hybrid_secret(
        &ml_kem.shared_secret,
        x25519_shared.as_bytes(),
    );
    
    Ok(HybridEncapsulation {
        ml_kem_ciphertext: ml_kem.ciphertext,
        x25519_public: *x25519_pk.as_bytes(),
        combined_secret: combined,
    })
}

fn derive_hybrid_secret(ml_kem_ss: &[u8], x25519_ss: &[u8]) -> Vec<u8> {
    use sha3::{Shake256, digest::{ExtendableOutput, Update, XofReader}};
    
    let mut hasher = Shake256::default();
    hasher.update(b"CT-WRAP-HYBRID-v1");
    hasher.update(ml_kem_ss);
    hasher.update(x25519_ss);
    
    let mut reader = hasher.finalize_xof();
    let mut key = vec![0u8; 32];
    reader.read(&mut key);
    key
}
```

---

## 4. Phase 2: ZK Proof System

### 4.1 Circuit Design Philosophy

The ZK system allows proving properties about encrypted data WITHOUT decryption:

1. **Data Commitment**: Prove the encrypted data matches a commitment
2. **Range Proofs**: Prove a value is within a range (e.g., balance > 0)
3. **Membership Proofs**: Prove data belongs to a set (Merkle proof)
4. **Hash Preimage**: Prove knowledge of data that hashes to a public value
5. **Schema Compliance**: Prove data follows a structure

### 4.2 Circuit: Data Commitment Proof

This circuit proves: "I know data D such that Hash(D) = public_commitment"

#### 4.2.1 Circom Circuit

Create file: `circuits/data_commitment.circom`

```circom
pragma circom 2.1.0;

include "node_modules/circomlib/circuits/poseidon.circom";
include "node_modules/circomlib/circuits/bitify.circom";

/*
 * DataCommitment Circuit
 * 
 * Proves: I know preimage data such that Poseidon(data) = commitment
 * 
 * Inputs:
 *   - data[N]: Private data array (field elements)
 *   - commitment: Public hash output
 * 
 * The circuit verifies that Poseidon hash of private data equals
 * the public commitment, without revealing the data.
 */
template DataCommitment(N) {
    // Private inputs (witness)
    signal input data[N];
    
    // Public inputs
    signal input commitment;
    
    // Poseidon hash of data
    component hasher = Poseidon(N);
    for (var i = 0; i < N; i++) {
        hasher.inputs[i] <== data[i];
    }
    
    // Constraint: hash output must equal commitment
    hasher.out === commitment;
}

// Default instantiation for 4 field elements (~1KB of data)
component main {public [commitment]} = DataCommitment(4);
```

#### 4.2.2 Extended Circuit: Range + Commitment

Create file: `circuits/range_commitment.circom`

```circom
pragma circom 2.1.0;

include "node_modules/circomlib/circuits/poseidon.circom";
include "node_modules/circomlib/circuits/comparators.circom";
include "node_modules/circomlib/circuits/bitify.circom";

/*
 * RangeCommitment Circuit
 * 
 * Proves:
 *   1. I know data such that Poseidon(data) = commitment
 *   2. data[0] (interpreted as a value) is >= minValue
 *   3. data[0] is <= maxValue
 */
template RangeCommitment(N, BITS) {
    // Private inputs
    signal input data[N];
    
    // Public inputs
    signal input commitment;
    signal input minValue;
    signal input maxValue;
    
    // 1. Verify commitment
    component hasher = Poseidon(N);
    for (var i = 0; i < N; i++) {
        hasher.inputs[i] <== data[i];
    }
    hasher.out === commitment;
    
    // 2. Range check: data[0] >= minValue
    component geq = GreaterEqThan(BITS);
    geq.in[0] <== data[0];
    geq.in[1] <== minValue;
    geq.out === 1;
    
    // 3. Range check: data[0] <= maxValue
    component leq = LessEqThan(BITS);
    leq.in[0] <== data[0];
    leq.in[1] <== maxValue;
    leq.out === 1;
}

component main {public [commitment, minValue, maxValue]} = RangeCommitment(4, 64);
```

#### 4.2.3 Merkle Membership Circuit

Create file: `circuits/merkle_membership.circom`

```circom
pragma circom 2.1.0;

include "node_modules/circomlib/circuits/poseidon.circom";

/*
 * MerkleMembership Circuit
 * 
 * Proves: A leaf is in a Merkle tree with given root
 */
template MerkleProof(LEVELS) {
    // Private inputs
    signal input leaf;
    signal input pathElements[LEVELS];
    signal input pathIndices[LEVELS];  // 0 = left, 1 = right
    
    // Public input
    signal input root;
    
    // Compute Merkle root from leaf and path
    signal hashes[LEVELS + 1];
    hashes[0] <== leaf;
    
    component hashers[LEVELS];
    component mux[LEVELS][2];
    
    for (var i = 0; i < LEVELS; i++) {
        hashers[i] = Poseidon(2);
        
        // Select left/right based on pathIndex
        // If pathIndex = 0: hash(current, sibling)
        // If pathIndex = 1: hash(sibling, current)
        
        var isRight = pathIndices[i];
        
        hashers[i].inputs[0] <== hashes[i] + isRight * (pathElements[i] - hashes[i]);
        hashers[i].inputs[1] <== pathElements[i] + isRight * (hashes[i] - pathElements[i]);
        
        hashes[i + 1] <== hashers[i].out;
    }
    
    // Constraint: computed root must match public root
    hashes[LEVELS] === root;
}

component main {public [root]} = MerkleProof(20);  // 2^20 = 1M leaves
```

### 4.3 Proof Generation Pipeline

#### 4.3.1 Setup Script

Create file: `scripts/setup_circuits.sh`

```bash
#!/bin/bash
set -e

CIRCUIT_DIR="circuits"
BUILD_DIR="build/circuits"
PTAU_FILE="powersOfTau28_hez_final_16.ptau"

# Download powers of tau (if not exists)
if [ ! -f "$PTAU_FILE" ]; then
    echo "Downloading Powers of Tau..."
    wget https://hermez.s3-eu-west-1.amazonaws.com/powersOfTau28_hez_final_16.ptau
fi

mkdir -p $BUILD_DIR

# Function to setup a circuit
setup_circuit() {
    local name=$1
    echo "Setting up circuit: $name"
    
    # Compile circuit
    circom "$CIRCUIT_DIR/$name.circom" \
        --r1cs "$BUILD_DIR/$name.r1cs" \
        --wasm "$BUILD_DIR/${name}_js/${name}.wasm" \
        --sym "$BUILD_DIR/$name.sym" \
        -l node_modules
    
    # Phase 2 setup (circuit-specific)
    snarkjs groth16 setup \
        "$BUILD_DIR/$name.r1cs" \
        "$PTAU_FILE" \
        "$BUILD_DIR/${name}_0000.zkey"
    
    # Contribute randomness
    echo "random-entropy-$(date +%s)" | snarkjs zkey contribute \
        "$BUILD_DIR/${name}_0000.zkey" \
        "$BUILD_DIR/${name}_final.zkey" \
        --name="CT-Wrap Setup"
    
    # Export verification key
    snarkjs zkey export verificationkey \
        "$BUILD_DIR/${name}_final.zkey" \
        "$BUILD_DIR/${name}_verification_key.json"
    
    # Export Solidity verifier
    snarkjs zkey export solidityverifier \
        "$BUILD_DIR/${name}_final.zkey" \
        "$BUILD_DIR/${name}_verifier.sol"
    
    echo "Circuit $name setup complete"
}

# Setup all circuits
setup_circuit "data_commitment"
setup_circuit "range_commitment"
setup_circuit "merkle_membership"

echo "All circuits setup complete!"
```

#### 4.3.2 Proof Generation (TypeScript)

Create file: `src/zk/prover.ts`

```typescript
import * as snarkjs from 'snarkjs';
import * as fs from 'fs';
import * as path from 'path';
import { buildPoseidon } from 'circomlibjs';

// Poseidon hash instance
let poseidon: any = null;

async function initPoseidon() {
    if (!poseidon) {
        poseidon = await buildPoseidon();
    }
    return poseidon;
}

/**
 * Convert data bytes to field elements for circuit input
 * Each field element can hold ~31 bytes safely (BN254 field is ~254 bits)
 */
export function bytesToFieldElements(data: Uint8Array, numElements: number): bigint[] {
    const BYTES_PER_ELEMENT = 31;
    const elements: bigint[] = [];
    
    for (let i = 0; i < numElements; i++) {
        const start = i * BYTES_PER_ELEMENT;
        const end = Math.min(start + BYTES_PER_ELEMENT, data.length);
        const chunk = data.slice(start, end);
        
        // Convert bytes to bigint (big-endian)
        let value = 0n;
        for (const byte of chunk) {
            value = (value << 8n) | BigInt(byte);
        }
        elements.push(value);
    }
    
    // Pad with zeros if needed
    while (elements.length < numElements) {
        elements.push(0n);
    }
    
    return elements;
}

/**
 * Compute Poseidon hash of field elements
 */
export async function computeCommitment(data: bigint[]): Promise<bigint> {
    const p = await initPoseidon();
    const hash = p(data);
    return p.F.toObject(hash);
}

/**
 * Generate a data commitment proof
 */
export async function generateDataCommitmentProof(
    data: Uint8Array,
    circuitWasmPath: string,
    zkeyPath: string
): Promise<{
    proof: any;
    publicSignals: string[];
    commitment: string;
}> {
    // Convert data to field elements
    const fieldElements = bytesToFieldElements(data, 4);
    
    // Compute commitment
    const commitment = await computeCommitment(fieldElements);
    
    // Prepare circuit inputs
    const input = {
        data: fieldElements.map(x => x.toString()),
        commitment: commitment.toString()
    };
    
    // Generate proof
    const { proof, publicSignals } = await snarkjs.groth16.fullProve(
        input,
        circuitWasmPath,
        zkeyPath
    );
    
    return {
        proof,
        publicSignals,
        commitment: commitment.toString()
    };
}

/**
 * Generate a range commitment proof
 */
export async function generateRangeProof(
    data: Uint8Array,
    minValue: bigint,
    maxValue: bigint,
    circuitWasmPath: string,
    zkeyPath: string
): Promise<{
    proof: any;
    publicSignals: string[];
}> {
    const fieldElements = bytesToFieldElements(data, 4);
    const commitment = await computeCommitment(fieldElements);
    
    const input = {
        data: fieldElements.map(x => x.toString()),
        commitment: commitment.toString(),
        minValue: minValue.toString(),
        maxValue: maxValue.toString()
    };
    
    const { proof, publicSignals } = await snarkjs.groth16.fullProve(
        input,
        circuitWasmPath,
        zkeyPath
    );
    
    return { proof, publicSignals };
}

/**
 * Verify a Groth16 proof
 */
export async function verifyProof(
    verificationKeyPath: string,
    publicSignals: string[],
    proof: any
): Promise<boolean> {
    const vkey = JSON.parse(fs.readFileSync(verificationKeyPath, 'utf-8'));
    return await snarkjs.groth16.verify(vkey, publicSignals, proof);
}

/**
 * Export proof for Solidity verifier
 * Returns calldata for the verifier contract
 */
export async function exportSolidityCalldata(
    publicSignals: string[],
    proof: any
): Promise<string> {
    return await snarkjs.groth16.exportSolidityCallData(proof, publicSignals);
}
```

### 4.4 Rust ZK Integration

Create file: `src/zk/mod.rs`

```rust
use std::process::Command;
use serde::{Deserialize, Serialize};
use std::path::Path;

#[derive(Debug, Serialize, Deserialize)]
pub struct Groth16Proof {
    pub pi_a: [String; 2],
    pub pi_b: [[String; 2]; 2],
    pub pi_c: [String; 2],
    pub protocol: String,
    pub curve: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ZkProofResult {
    pub proof: Groth16Proof,
    pub public_signals: Vec<String>,
    pub commitment: String,
}

/// Generate ZK proof by calling snarkjs via subprocess
/// 
/// In production, consider using ark-groth16 for native Rust proofs
pub fn generate_proof(
    data: &[u8],
    circuit_name: &str,
    build_dir: &Path,
) -> Result<ZkProofResult, Box<dyn std::error::Error>> {
    // Write data to temp file for Node.js script
    let data_hex = hex::encode(data);
    let temp_input = build_dir.join("temp_input.json");
    std::fs::write(&temp_input, format!(r#"{{"data_hex": "{}"}}"#, data_hex))?;
    
    // Call proof generation script
    let output = Command::new("node")
        .arg("scripts/generate_proof.js")
        .arg(circuit_name)
        .arg(&temp_input)
        .arg(build_dir)
        .output()?;
    
    if !output.status.success() {
        return Err(format!(
            "Proof generation failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ).into());
    }
    
    // Parse result
    let result: ZkProofResult = serde_json::from_slice(&output.stdout)?;
    
    // Clean up
    std::fs::remove_file(temp_input)?;
    
    Ok(result)
}

/// Native Groth16 proof verification using ark-groth16
pub fn verify_proof_native(
    vk_bytes: &[u8],
    proof_bytes: &[u8],
    public_inputs: &[Vec<u8>],
) -> Result<bool, Box<dyn std::error::Error>> {
    use ark_bn254::{Bn254, Fr};
    use ark_groth16::{Groth16, Proof, VerifyingKey};
    use ark_serialize::CanonicalDeserialize;
    use ark_snark::SNARK;
    
    // Deserialize verification key
    let vk = VerifyingKey::<Bn254>::deserialize_compressed(vk_bytes)?;
    
    // Deserialize proof
    let proof = Proof::<Bn254>::deserialize_compressed(proof_bytes)?;
    
    // Convert public inputs to field elements
    let inputs: Vec<Fr> = public_inputs
        .iter()
        .map(|bytes| Fr::from_be_bytes_mod_order(bytes))
        .collect();
    
    // Verify
    let pvk = ark_groth16::prepare_verifying_key(&vk);
    let valid = Groth16::<Bn254>::verify_with_processed_vk(&pvk, &inputs, &proof)?;
    
    Ok(valid)
}
```

---

## 5. Phase 3: Wrapper Serialization

### 5.1 CT-Wrap Package Format

The package format uses CBOR (RFC 8949) for compact binary serialization.

#### 5.1.1 Package Structure

```
CTWrapPackage {
    version: u8,                    // Format version (1)
    algorithm_suite: AlgorithmSuite,
    key_encapsulations: [KeyEncapsulation],  // One per recipient
    encrypted_data: EncryptedData,
    signature: Option<Signature>,
    zk_proof: Option<ZkProof>,
    metadata: Metadata,
}

AlgorithmSuite {
    kem: "ML-KEM-1024" | "HYBRID-ML-KEM-X25519",
    encryption: "AES-256-GCM-SIV",
    signature: "ML-DSA-87",
    hash: "SHAKE256",
}

KeyEncapsulation {
    recipient_id: [u8; 32],         // SHA3-256 of recipient public key
    kem_ciphertext: Vec<u8>,        // ML-KEM ciphertext
    x25519_ephemeral: Option<[u8; 32]>,  // For hybrid mode
}

EncryptedData {
    nonce: [u8; 12],
    ciphertext: Vec<u8>,            // Includes auth tag
    aad_hash: [u8; 32],             // Hash of AAD
}

Signature {
    algorithm: "ML-DSA-87",
    public_key: Vec<u8>,
    signature: Vec<u8>,
    signed_data_hash: [u8; 32],
}

ZkProof {
    circuit_id: String,             // "data_commitment", "range_commitment", etc.
    proof: Groth16Proof,
    public_signals: Vec<String>,
    verification_key_hash: [u8; 32],
}

Metadata {
    created_at: u64,                // Unix timestamp
    content_type: Option<String>,   // MIME type
    content_hash: [u8; 32],         // SHA3-256 of original data
    access_policy: Option<AccessPolicy>,
    custom: HashMap<String, Value>, // User-defined metadata
}
```

#### 5.1.2 Rust Serialization

Create file: `src/package/mod.rs`

```rust
use serde::{Deserialize, Serialize};
use serde_cbor;
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
    pub threshold: Option<u32>,     // N-of-M threshold
    pub expiry: Option<u64>,        // Unix timestamp
    pub allowed_verifiers: Option<Vec<[u8; 20]>>,  // Ethereum addresses
}

impl CTWrapPackage {
    /// Serialize package to CBOR bytes
    pub fn to_cbor(&self) -> Result<Vec<u8>, serde_cbor::Error> {
        serde_cbor::to_vec(self)
    }
    
    /// Deserialize package from CBOR bytes
    pub fn from_cbor(bytes: &[u8]) -> Result<Self, serde_cbor::Error> {
        serde_cbor::from_slice(bytes)
    }
    
    /// Get package size in bytes
    pub fn size(&self) -> usize {
        self.to_cbor().map(|v| v.len()).unwrap_or(0)
    }
    
    /// Compute package hash for on-chain storage reference
    pub fn hash(&self) -> [u8; 32] {
        use sha3::{Sha3_256, Digest};
        let cbor = self.to_cbor().expect("Serialization should not fail");
        Sha3_256::digest(&cbor).into()
    }
}
```

### 5.2 Complete Wrap Function

Create file: `src/wrap.rs`

```rust
use crate::crypto::{
    MlKemKeyPair, MlDsaKeyPair, 
    encapsulate, encrypt_aes_gcm_siv, derive_key,
};
use crate::package::*;
use crate::zk::generate_proof;
use sha3::{Sha3_256, Digest};
use std::time::{SystemTime, UNIX_EPOCH};

/// Configuration for wrapping data
pub struct WrapConfig {
    pub recipients: Vec<RecipientPublicKey>,
    pub signer: Option<MlDsaKeyPair>,
    pub generate_zk_proof: bool,
    pub zk_circuit: Option<String>,
    pub content_type: Option<String>,
    pub access_policy: Option<AccessPolicy>,
    pub custom_metadata: HashMap<String, serde_cbor::Value>,
}

pub struct RecipientPublicKey {
    pub ml_kem_pk: Vec<u8>,
    pub x25519_pk: Option<[u8; 32]>,  // For hybrid mode
}

impl RecipientPublicKey {
    pub fn id(&self) -> [u8; 32] {
        Sha3_256::digest(&self.ml_kem_pk).into()
    }
}

/// Wrap data with encryption, signatures, and ZK proofs
pub fn wrap(
    data: &[u8],
    config: WrapConfig,
) -> Result<CTWrapPackage, Box<dyn std::error::Error>> {
    // 1. Generate ephemeral key and shared secret
    let mut shared_secrets = Vec::new();
    let mut key_encapsulations = Vec::new();
    
    for recipient in &config.recipients {
        let encap = encapsulate(&recipient.ml_kem_pk)?;
        
        key_encapsulations.push(KeyEncapsulation {
            recipient_id: recipient.id(),
            kem_ciphertext: encap.ciphertext,
            x25519_ephemeral: None,  // TODO: Add hybrid support
        });
        
        shared_secrets.push(encap.shared_secret);
    }
    
    // 2. Derive encryption key (use first recipient's shared secret)
    // In production, consider encrypting to each recipient separately
    // or using a shared data encryption key (DEK) model
    let encryption_key = derive_key(
        &shared_secrets[0],
        b"CT-WRAP-ENCRYPTION",
        32,
    );
    let key_array: [u8; 32] = encryption_key.try_into()
        .map_err(|_| "Invalid key length")?;
    
    // 3. Prepare AAD (metadata that's authenticated but not encrypted)
    let content_hash: [u8; 32] = Sha3_256::digest(data).into();
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)?
        .as_secs();
    
    let aad = prepare_aad(&content_hash, timestamp, &config);
    
    // 4. Encrypt data
    let encrypted = encrypt_aes_gcm_siv(&key_array, data, &aad)?;
    
    // 5. Sign the package (optional)
    let signature = if let Some(signer) = &config.signer {
        let sign_data = prepare_sign_data(&encrypted, &content_hash);
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
    
    // 6. Generate ZK proof (optional)
    let zk_proof = if config.generate_zk_proof {
        let circuit = config.zk_circuit.as_deref().unwrap_or("data_commitment");
        let proof_result = generate_proof(
            data,
            circuit,
            std::path::Path::new("build/circuits"),
        )?;
        
        Some(ZkProof {
            circuit_id: circuit.to_string(),
            proof: Groth16ProofData {
                pi_a: vec![proof_result.proof.pi_a[0].clone(), proof_result.proof.pi_a[1].clone()],
                pi_b: vec![
                    vec![proof_result.proof.pi_b[0][0].clone(), proof_result.proof.pi_b[0][1].clone()],
                    vec![proof_result.proof.pi_b[1][0].clone(), proof_result.proof.pi_b[1][1].clone()],
                ],
                pi_c: vec![proof_result.proof.pi_c[0].clone(), proof_result.proof.pi_c[1].clone()],
            },
            public_signals: proof_result.public_signals,
            verification_key_hash: [0u8; 32],  // TODO: Hash actual vkey
        })
    } else {
        None
    };
    
    // 7. Assemble package
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

/// Unwrap (decrypt) a package
pub fn unwrap(
    package: &CTWrapPackage,
    recipient_keypair: &MlKemKeyPair,
) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    // 1. Find our key encapsulation
    let recipient_id: [u8; 32] = Sha3_256::digest(&recipient_keypair.public_key).into();
    
    let our_encap = package.key_encapsulations
        .iter()
        .find(|e| e.recipient_id == recipient_id)
        .ok_or("No key encapsulation for this recipient")?;
    
    // 2. Decapsulate to get shared secret
    let shared_secret = recipient_keypair.decapsulate(&our_encap.kem_ciphertext)?;
    
    // 3. Derive decryption key
    let decryption_key = derive_key(&shared_secret, b"CT-WRAP-ENCRYPTION", 32);
    let key_array: [u8; 32] = decryption_key.try_into()
        .map_err(|_| "Invalid key length")?;
    
    // 4. Reconstruct AAD
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
    
    // 5. Verify AAD hash
    let expected_hash: [u8; 32] = Sha3_256::digest(&aad).into();
    if expected_hash != package.encrypted_data.aad_hash {
        return Err("AAD hash mismatch".into());
    }
    
    // 6. Decrypt
    let plaintext = decrypt_aes_gcm_siv(
        &key_array,
        &package.encrypted_data.nonce,
        &package.encrypted_data.ciphertext,
        &aad,
    )?;
    
    // 7. Verify content hash
    let content_hash: [u8; 32] = Sha3_256::digest(&plaintext).into();
    if content_hash != package.metadata.content_hash {
        return Err("Content hash mismatch".into());
    }
    
    Ok(plaintext)
}

// Helper functions
fn prepare_aad(
    content_hash: &[u8; 32],
    timestamp: u64,
    config: &WrapConfig,
) -> Vec<u8> {
    let mut aad = Vec::new();
    aad.extend_from_slice(b"CT-WRAP-AAD-v1");
    aad.extend_from_slice(content_hash);
    aad.extend_from_slice(&timestamp.to_le_bytes());
    if let Some(ct) = &config.content_type {
        aad.extend_from_slice(ct.as_bytes());
    }
    aad
}

fn prepare_sign_data(encrypted: &EncryptionResult, content_hash: &[u8; 32]) -> Vec<u8> {
    let mut data = Vec::new();
    data.extend_from_slice(b"CT-WRAP-SIGN-v1");
    data.extend_from_slice(&encrypted.nonce);
    data.extend_from_slice(&encrypted.aad_hash);
    data.extend_from_slice(content_hash);
    data
}
```

---

## 6. Phase 4: API Service Layer

### 6.1 REST API Specification

Create file: `src/api/mod.rs`

```rust
use axum::{
    Router,
    routing::{get, post},
    extract::{Json, State, Path},
    http::StatusCode,
    response::IntoResponse,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

// API State
pub struct ApiState {
    pub circuit_dir: std::path::PathBuf,
    pub verification_keys: std::collections::HashMap<String, Vec<u8>>,
}

// Request/Response types
#[derive(Debug, Deserialize)]
pub struct WrapRequest {
    /// Base64-encoded data to wrap
    pub data: String,
    /// Recipient ML-KEM public keys (base64)
    pub recipients: Vec<String>,
    /// Content type (MIME)
    pub content_type: Option<String>,
    /// Generate ZK proof
    pub generate_proof: Option<bool>,
    /// ZK circuit to use
    pub circuit: Option<String>,
    /// Signer key (base64, optional)
    pub signer_secret_key: Option<String>,
}

#[derive(Debug, Serialize)]
pub struct WrapResponse {
    /// Base64-encoded CTWrap package
    pub package: String,
    /// Package hash (hex)
    pub package_hash: String,
    /// ZK proof details (if generated)
    pub proof: Option<ProofDetails>,
    /// Package size in bytes
    pub size_bytes: usize,
}

#[derive(Debug, Serialize)]
pub struct ProofDetails {
    pub circuit: String,
    pub commitment: String,
    pub public_signals: Vec<String>,
    /// Solidity verifier calldata
    pub solidity_calldata: String,
}

#[derive(Debug, Deserialize)]
pub struct UnwrapRequest {
    /// Base64-encoded CTWrap package
    pub package: String,
    /// Base64-encoded recipient secret key
    pub secret_key: String,
}

#[derive(Debug, Serialize)]
pub struct UnwrapResponse {
    /// Base64-encoded decrypted data
    pub data: String,
    /// Content type from metadata
    pub content_type: Option<String>,
    /// Original content hash (hex)
    pub content_hash: String,
    /// Package metadata
    pub metadata: serde_json::Value,
}

#[derive(Debug, Deserialize)]
pub struct VerifyProofRequest {
    /// Base64-encoded CTWrap package (or just proof section)
    pub package: String,
    /// Circuit ID
    pub circuit: String,
}

#[derive(Debug, Serialize)]
pub struct VerifyProofResponse {
    pub valid: bool,
    pub commitment: String,
    pub public_signals: Vec<String>,
}

#[derive(Debug, Serialize)]
pub struct KeyPairResponse {
    pub public_key: String,   // Base64
    pub secret_key: String,   // Base64 - ONLY for testing!
}

// Router setup
pub fn create_router(state: Arc<ApiState>) -> Router {
    Router::new()
        // Wrapping endpoints
        .route("/api/v1/wrap", post(wrap_handler))
        .route("/api/v1/unwrap", post(unwrap_handler))
        
        // Key management
        .route("/api/v1/keys/generate", post(generate_keys_handler))
        
        // ZK proof endpoints
        .route("/api/v1/proof/verify", post(verify_proof_handler))
        .route("/api/v1/proof/circuits", get(list_circuits_handler))
        .route("/api/v1/proof/circuits/:id/vkey", get(get_verification_key_handler))
        
        // Health & info
        .route("/api/v1/health", get(health_handler))
        .route("/api/v1/info", get(info_handler))
        
        .with_state(state)
}

// Handlers
async fn wrap_handler(
    State(state): State<Arc<ApiState>>,
    Json(req): Json<WrapRequest>,
) -> Result<Json<WrapResponse>, (StatusCode, String)> {
    use base64::{Engine, engine::general_purpose::STANDARD};
    
    // Decode input data
    let data = STANDARD.decode(&req.data)
        .map_err(|e| (StatusCode::BAD_REQUEST, format!("Invalid data: {}", e)))?;
    
    // Decode recipient keys
    let recipients: Result<Vec<_>, _> = req.recipients
        .iter()
        .map(|pk| {
            STANDARD.decode(pk).map(|bytes| RecipientPublicKey {
                ml_kem_pk: bytes,
                x25519_pk: None,
            })
        })
        .collect();
    let recipients = recipients
        .map_err(|e| (StatusCode::BAD_REQUEST, format!("Invalid recipient key: {}", e)))?;
    
    // Configure wrap
    let config = WrapConfig {
        recipients,
        signer: None,  // TODO: Handle signer
        generate_zk_proof: req.generate_proof.unwrap_or(false),
        zk_circuit: req.circuit,
        content_type: req.content_type,
        access_policy: None,
        custom_metadata: std::collections::HashMap::new(),
    };
    
    // Wrap data
    let package = wrap(&data, config)
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    // Serialize
    let package_bytes = package.to_cbor()
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    
    // Build response
    let mut response = WrapResponse {
        package: STANDARD.encode(&package_bytes),
        package_hash: hex::encode(package.hash()),
        proof: None,
        size_bytes: package_bytes.len(),
    };
    
    // Add proof details if present
    if let Some(zk_proof) = &package.zk_proof {
        response.proof = Some(ProofDetails {
            circuit: zk_proof.circuit_id.clone(),
            commitment: zk_proof.public_signals.get(0).cloned().unwrap_or_default(),
            public_signals: zk_proof.public_signals.clone(),
            solidity_calldata: "".to_string(),  // TODO: Generate calldata
        });
    }
    
    Ok(Json(response))
}

async fn unwrap_handler(
    State(_state): State<Arc<ApiState>>,
    Json(req): Json<UnwrapRequest>,
) -> Result<Json<UnwrapResponse>, (StatusCode, String)> {
    use base64::{Engine, engine::general_purpose::STANDARD};
    
    // Decode package
    let package_bytes = STANDARD.decode(&req.package)
        .map_err(|e| (StatusCode::BAD_REQUEST, format!("Invalid package: {}", e)))?;
    
    let package = CTWrapPackage::from_cbor(&package_bytes)
        .map_err(|e| (StatusCode::BAD_REQUEST, format!("Invalid package format: {}", e)))?;
    
    // Decode secret key
    let sk_bytes = STANDARD.decode(&req.secret_key)
        .map_err(|e| (StatusCode::BAD_REQUEST, format!("Invalid secret key: {}", e)))?;
    
    // Reconstruct keypair (would need public key too in real impl)
    // This is simplified - in production, use proper key storage
    let keypair = MlKemKeyPair {
        public_key: vec![],  // Not needed for decapsulation
        secret_key: sk_bytes,
    };
    
    // Unwrap
    let data = unwrap(&package, &keypair)
        .map_err(|e| (StatusCode::BAD_REQUEST, format!("Decryption failed: {}", e)))?;
    
    Ok(Json(UnwrapResponse {
        data: STANDARD.encode(&data),
        content_type: package.metadata.content_type,
        content_hash: hex::encode(package.metadata.content_hash),
        metadata: serde_json::to_value(&package.metadata).unwrap_or_default(),
    }))
}

async fn generate_keys_handler() -> Json<KeyPairResponse> {
    use base64::{Engine, engine::general_purpose::STANDARD};
    
    let keypair = MlKemKeyPair::generate().expect("Key generation failed");
    
    Json(KeyPairResponse {
        public_key: STANDARD.encode(&keypair.public_key),
        secret_key: STANDARD.encode(&keypair.secret_key),
    })
}

async fn verify_proof_handler(
    State(state): State<Arc<ApiState>>,
    Json(req): Json<VerifyProofRequest>,
) -> Result<Json<VerifyProofResponse>, (StatusCode, String)> {
    // TODO: Implement proof verification
    Ok(Json(VerifyProofResponse {
        valid: true,
        commitment: "".to_string(),
        public_signals: vec![],
    }))
}

async fn list_circuits_handler(
    State(state): State<Arc<ApiState>>,
) -> Json<Vec<String>> {
    Json(vec![
        "data_commitment".to_string(),
        "range_commitment".to_string(),
        "merkle_membership".to_string(),
    ])
}

async fn get_verification_key_handler(
    State(state): State<Arc<ApiState>>,
    Path(id): Path<String>,
) -> Result<Json<serde_json::Value>, (StatusCode, String)> {
    // Load verification key from file
    let vkey_path = state.circuit_dir.join(format!("{}_verification_key.json", id));
    let vkey_json = std::fs::read_to_string(&vkey_path)
        .map_err(|_| (StatusCode::NOT_FOUND, "Circuit not found".to_string()))?;
    let vkey: serde_json::Value = serde_json::from_str(&vkey_json)
        .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()))?;
    Ok(Json(vkey))
}

async fn health_handler() -> &'static str {
    "OK"
}

async fn info_handler() -> Json<serde_json::Value> {
    Json(serde_json::json!({
        "name": "CT-Wrap",
        "version": "1.0.0",
        "algorithms": {
            "kem": "ML-KEM-1024 (FIPS 203)",
            "signature": "ML-DSA-87 (FIPS 204)",
            "encryption": "AES-256-GCM-SIV (RFC 8452)",
            "hash": "SHAKE256"
        },
        "circuits": ["data_commitment", "range_commitment", "merkle_membership"]
    }))
}
```

### 6.2 Main Server Entry Point

Create file: `src/main.rs`

```rust
use axum::http::Method;
use std::sync::Arc;
use tower_http::cors::{Any, CorsLayer};

mod api;
mod crypto;
mod package;
mod wrap;
mod zk;

use api::{create_router, ApiState};

#[tokio::main]
async fn main() {
    // Initialize liboqs
    oqs::init();
    
    // Load verification keys
    let mut verification_keys = std::collections::HashMap::new();
    // TODO: Load from files
    
    // Create state
    let state = Arc::new(ApiState {
        circuit_dir: std::path::PathBuf::from("build/circuits"),
        verification_keys,
    });
    
    // CORS configuration
    let cors = CorsLayer::new()
        .allow_origin(Any)
        .allow_methods([Method::GET, Method::POST])
        .allow_headers(Any);
    
    // Build router
    let app = create_router(state).layer(cors);
    
    // Start server
    let addr = std::net::SocketAddr::from(([0, 0, 0, 0], 3000));
    println!("CT-Wrap API server listening on {}", addr);
    
    let listener = tokio::net::TcpListener::bind(addr).await.unwrap();
    axum::serve(listener, app).await.unwrap();
}
```

---

## 7. Phase 5: Smart Contract Verification

### 7.1 Groth16 Verifier Contract

The snarkjs-generated verifier handles BN254 pairing checks. Customize it for CT-Wrap:

Create file: `contracts/CTWrapVerifier.sol`

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./Groth16Verifier.sol";  // Generated by snarkjs

/**
 * @title CTWrapVerifier
 * @notice On-chain verification of CT-Wrap ZK proofs
 * @dev Wraps the snarkjs-generated Groth16 verifier with CT-Wrap specific logic
 */
contract CTWrapVerifier {
    // Generated verifier for data_commitment circuit
    Groth16Verifier public immutable dataCommitmentVerifier;
    
    // Registry of verified commitments
    mapping(bytes32 => bool) public verifiedCommitments;
    
    // Events
    event CommitmentVerified(
        bytes32 indexed commitment,
        address indexed verifier,
        uint256 timestamp
    );
    
    event PackageRegistered(
        bytes32 indexed packageHash,
        bytes32 indexed commitment,
        address indexed registrant
    );
    
    // Package metadata stored on-chain
    struct PackageRecord {
        bytes32 commitment;
        address registrant;
        uint256 timestamp;
        string contentType;
        bytes32 contentHash;
    }
    
    mapping(bytes32 => PackageRecord) public packages;
    
    constructor(address _dataCommitmentVerifier) {
        dataCommitmentVerifier = Groth16Verifier(_dataCommitmentVerifier);
    }
    
    /**
     * @notice Verify a data commitment proof
     * @param proof The Groth16 proof components
     * @param commitment The public commitment being proven
     * @return valid Whether the proof is valid
     */
    function verifyDataCommitment(
        uint256[2] calldata pA,
        uint256[2][2] calldata pB,
        uint256[2] calldata pC,
        uint256 commitment
    ) external view returns (bool valid) {
        uint256[1] memory publicInputs;
        publicInputs[0] = commitment;
        
        return dataCommitmentVerifier.verifyProof(pA, pB, pC, publicInputs);
    }
    
    /**
     * @notice Verify and register a commitment on-chain
     * @dev Stores the commitment as verified if proof is valid
     */
    function verifyAndRegister(
        uint256[2] calldata pA,
        uint256[2][2] calldata pB,
        uint256[2] calldata pC,
        uint256 commitment
    ) external returns (bool) {
        uint256[1] memory publicInputs;
        publicInputs[0] = commitment;
        
        require(
            dataCommitmentVerifier.verifyProof(pA, pB, pC, publicInputs),
            "Invalid proof"
        );
        
        bytes32 commitmentHash = bytes32(commitment);
        verifiedCommitments[commitmentHash] = true;
        
        emit CommitmentVerified(commitmentHash, msg.sender, block.timestamp);
        
        return true;
    }
    
    /**
     * @notice Register a CT-Wrap package with its proof
     * @param packageHash Hash of the full CTWrap package
     * @param pA Proof component A
     * @param pB Proof component B  
     * @param pC Proof component C
     * @param commitment The data commitment
     * @param contentType MIME type of the content
     * @param contentHash Hash of the original plaintext
     */
    function registerPackage(
        bytes32 packageHash,
        uint256[2] calldata pA,
        uint256[2][2] calldata pB,
        uint256[2] calldata pC,
        uint256 commitment,
        string calldata contentType,
        bytes32 contentHash
    ) external returns (bool) {
        // Verify the proof
        uint256[1] memory publicInputs;
        publicInputs[0] = commitment;
        
        require(
            dataCommitmentVerifier.verifyProof(pA, pB, pC, publicInputs),
            "Invalid proof"
        );
        
        // Store package record
        packages[packageHash] = PackageRecord({
            commitment: bytes32(commitment),
            registrant: msg.sender,
            timestamp: block.timestamp,
            contentType: contentType,
            contentHash: contentHash
        });
        
        verifiedCommitments[bytes32(commitment)] = true;
        
        emit PackageRegistered(packageHash, bytes32(commitment), msg.sender);
        
        return true;
    }
    
    /**
     * @notice Check if a commitment has been verified
     */
    function isCommitmentVerified(bytes32 commitment) external view returns (bool) {
        return verifiedCommitments[commitment];
    }
    
    /**
     * @notice Get package record
     */
    function getPackage(bytes32 packageHash) external view returns (
        bytes32 commitment,
        address registrant,
        uint256 timestamp,
        string memory contentType,
        bytes32 contentHash
    ) {
        PackageRecord storage record = packages[packageHash];
        return (
            record.commitment,
            record.registrant,
            record.timestamp,
            record.contentType,
            record.contentHash
        );
    }
}
```

### 7.2 Deployment Script

Create file: `scripts/deploy.ts`

```typescript
import { ethers } from "hardhat";
import * as fs from "fs";

async function main() {
    const [deployer] = await ethers.getSigners();
    console.log("Deploying contracts with:", deployer.address);
    
    // Deploy the Groth16 verifier (generated by snarkjs)
    const Groth16Verifier = await ethers.getContractFactory("Groth16Verifier");
    const groth16Verifier = await Groth16Verifier.deploy();
    await groth16Verifier.waitForDeployment();
    console.log("Groth16Verifier deployed to:", await groth16Verifier.getAddress());
    
    // Deploy CTWrapVerifier
    const CTWrapVerifier = await ethers.getContractFactory("CTWrapVerifier");
    const ctWrapVerifier = await CTWrapVerifier.deploy(
        await groth16Verifier.getAddress()
    );
    await ctWrapVerifier.waitForDeployment();
    console.log("CTWrapVerifier deployed to:", await ctWrapVerifier.getAddress());
    
    // Save deployment addresses
    const addresses = {
        groth16Verifier: await groth16Verifier.getAddress(),
        ctWrapVerifier: await ctWrapVerifier.getAddress(),
        deployer: deployer.address,
        network: (await ethers.provider.getNetwork()).name,
        timestamp: new Date().toISOString(),
    };
    
    fs.writeFileSync(
        "deployments/addresses.json",
        JSON.stringify(addresses, null, 2)
    );
    
    console.log("\nDeployment complete!");
    console.log(JSON.stringify(addresses, null, 2));
}

main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
});
```

---

## 8. Phase 6: SDK and Client Libraries

### 8.1 TypeScript/JavaScript SDK

Create file: `sdk/typescript/src/index.ts`

```typescript
import axios, { AxiosInstance } from 'axios';

export interface WrapOptions {
    contentType?: string;
    generateProof?: boolean;
    circuit?: string;
}

export interface WrapResult {
    package: Uint8Array;
    packageHash: string;
    proof?: {
        circuit: string;
        commitment: string;
        publicSignals: string[];
        solidityCalldata: string;
    };
    sizeBytes: number;
}

export interface UnwrapResult {
    data: Uint8Array;
    contentType?: string;
    contentHash: string;
    metadata: Record<string, unknown>;
}

export interface KeyPair {
    publicKey: Uint8Array;
    secretKey: Uint8Array;
}

/**
 * CT-Wrap Client SDK
 * 
 * @example
 * ```typescript
 * const client = new CTWrapClient('https://api.agentpmt.com/ctwrap');
 * 
 * // Generate keys
 * const keys = await client.generateKeys();
 * 
 * // Wrap data
 * const data = new TextEncoder().encode('Hello, World!');
 * const result = await client.wrap(data, [keys.publicKey], {
 *     generateProof: true,
 *     contentType: 'text/plain'
 * });
 * 
 * // Unwrap data
 * const decrypted = await client.unwrap(result.package, keys.secretKey);
 * console.log(new TextDecoder().decode(decrypted.data));
 * ```
 */
export class CTWrapClient {
    private client: AxiosInstance;
    
    constructor(baseUrl: string = 'http://localhost:3000') {
        this.client = axios.create({
            baseURL: baseUrl,
            headers: {
                'Content-Type': 'application/json',
            },
        });
    }
    
    /**
     * Generate a new ML-KEM key pair
     */
    async generateKeys(): Promise<KeyPair> {
        const response = await this.client.post('/api/v1/keys/generate');
        return {
            publicKey: this.base64ToBytes(response.data.public_key),
            secretKey: this.base64ToBytes(response.data.secret_key),
        };
    }
    
    /**
     * Wrap data with encryption and optional ZK proof
     * 
     * @param data - Data to encrypt
     * @param recipientPublicKeys - Array of recipient ML-KEM public keys
     * @param options - Wrap configuration options
     */
    async wrap(
        data: Uint8Array,
        recipientPublicKeys: Uint8Array[],
        options: WrapOptions = {}
    ): Promise<WrapResult> {
        const response = await this.client.post('/api/v1/wrap', {
            data: this.bytesToBase64(data),
            recipients: recipientPublicKeys.map(pk => this.bytesToBase64(pk)),
            content_type: options.contentType,
            generate_proof: options.generateProof,
            circuit: options.circuit,
        });
        
        return {
            package: this.base64ToBytes(response.data.package),
            packageHash: response.data.package_hash,
            proof: response.data.proof,
            sizeBytes: response.data.size_bytes,
        };
    }
    
    /**
     * Unwrap (decrypt) a CT-Wrap package
     * 
     * @param packageData - The encrypted package bytes
     * @param secretKey - Recipient's ML-KEM secret key
     */
    async unwrap(
        packageData: Uint8Array,
        secretKey: Uint8Array
    ): Promise<UnwrapResult> {
        const response = await this.client.post('/api/v1/unwrap', {
            package: this.bytesToBase64(packageData),
            secret_key: this.bytesToBase64(secretKey),
        });
        
        return {
            data: this.base64ToBytes(response.data.data),
            contentType: response.data.content_type,
            contentHash: response.data.content_hash,
            metadata: response.data.metadata,
        };
    }
    
    /**
     * Verify a ZK proof
     * 
     * @param packageData - The CT-Wrap package containing the proof
     * @param circuit - Circuit ID to verify against
     */
    async verifyProof(
        packageData: Uint8Array,
        circuit: string
    ): Promise<{ valid: boolean; commitment: string; publicSignals: string[] }> {
        const response = await this.client.post('/api/v1/proof/verify', {
            package: this.bytesToBase64(packageData),
            circuit,
        });
        return response.data;
    }
    
    /**
     * Get available ZK circuits
     */
    async getCircuits(): Promise<string[]> {
        const response = await this.client.get('/api/v1/proof/circuits');
        return response.data;
    }
    
    /**
     * Get verification key for a circuit
     */
    async getVerificationKey(circuitId: string): Promise<unknown> {
        const response = await this.client.get(`/api/v1/proof/circuits/${circuitId}/vkey`);
        return response.data;
    }
    
    // Helper methods
    private bytesToBase64(bytes: Uint8Array): string {
        return Buffer.from(bytes).toString('base64');
    }
    
    private base64ToBytes(base64: string): Uint8Array {
        return new Uint8Array(Buffer.from(base64, 'base64'));
    }
}

// Browser-compatible export
export default CTWrapClient;
```

### 8.2 Python SDK

Create file: `sdk/python/ctwrap/client.py`

```python
"""
CT-Wrap Python SDK

Example usage:
    from ctwrap import CTWrapClient
    
    client = CTWrapClient("https://api.agentpmt.com/ctwrap")
    
    # Generate keys
    keys = client.generate_keys()
    
    # Wrap data
    result = client.wrap(
        data=b"Hello, World!",
        recipients=[keys.public_key],
        generate_proof=True,
        content_type="text/plain"
    )
    
    # Unwrap data
    decrypted = client.unwrap(result.package, keys.secret_key)
    print(decrypted.data.decode())
"""

import base64
from dataclasses import dataclass
from typing import List, Optional, Dict, Any
import requests


@dataclass
class KeyPair:
    """ML-KEM key pair"""
    public_key: bytes
    secret_key: bytes


@dataclass
class ProofDetails:
    """ZK proof details"""
    circuit: str
    commitment: str
    public_signals: List[str]
    solidity_calldata: str


@dataclass
class WrapResult:
    """Result of wrapping data"""
    package: bytes
    package_hash: str
    proof: Optional[ProofDetails]
    size_bytes: int


@dataclass
class UnwrapResult:
    """Result of unwrapping data"""
    data: bytes
    content_type: Optional[str]
    content_hash: str
    metadata: Dict[str, Any]


class CTWrapClient:
    """
    CT-Wrap API Client
    
    Provides post-quantum encryption with ZK proof generation
    for secure data storage and verification.
    """
    
    def __init__(self, base_url: str = "http://localhost:3000"):
        self.base_url = base_url.rstrip("/")
        self.session = requests.Session()
        self.session.headers.update({"Content-Type": "application/json"})
    
    def generate_keys(self) -> KeyPair:
        """Generate a new ML-KEM-1024 key pair"""
        response = self.session.post(f"{self.base_url}/api/v1/keys/generate")
        response.raise_for_status()
        data = response.json()
        return KeyPair(
            public_key=base64.b64decode(data["public_key"]),
            secret_key=base64.b64decode(data["secret_key"]),
        )
    
    def wrap(
        self,
        data: bytes,
        recipients: List[bytes],
        content_type: Optional[str] = None,
        generate_proof: bool = False,
        circuit: Optional[str] = None,
    ) -> WrapResult:
        """
        Wrap data with encryption and optional ZK proof.
        
        Args:
            data: Raw bytes to encrypt
            recipients: List of ML-KEM public keys
            content_type: MIME type of the data
            generate_proof: Whether to generate a ZK proof
            circuit: ZK circuit to use (default: data_commitment)
        
        Returns:
            WrapResult containing the encrypted package and proof details
        """
        payload = {
            "data": base64.b64encode(data).decode(),
            "recipients": [base64.b64encode(pk).decode() for pk in recipients],
            "content_type": content_type,
            "generate_proof": generate_proof,
            "circuit": circuit,
        }
        
        response = self.session.post(f"{self.base_url}/api/v1/wrap", json=payload)
        response.raise_for_status()
        result = response.json()
        
        proof = None
        if result.get("proof"):
            proof = ProofDetails(
                circuit=result["proof"]["circuit"],
                commitment=result["proof"]["commitment"],
                public_signals=result["proof"]["public_signals"],
                solidity_calldata=result["proof"]["solidity_calldata"],
            )
        
        return WrapResult(
            package=base64.b64decode(result["package"]),
            package_hash=result["package_hash"],
            proof=proof,
            size_bytes=result["size_bytes"],
        )
    
    def unwrap(self, package: bytes, secret_key: bytes) -> UnwrapResult:
        """
        Unwrap (decrypt) a CT-Wrap package.
        
        Args:
            package: The encrypted CT-Wrap package
            secret_key: Recipient's ML-KEM secret key
        
        Returns:
            UnwrapResult containing the decrypted data and metadata
        """
        payload = {
            "package": base64.b64encode(package).decode(),
            "secret_key": base64.b64encode(secret_key).decode(),
        }
        
        response = self.session.post(f"{self.base_url}/api/v1/unwrap", json=payload)
        response.raise_for_status()
        result = response.json()
        
        return UnwrapResult(
            data=base64.b64decode(result["data"]),
            content_type=result.get("content_type"),
            content_hash=result["content_hash"],
            metadata=result.get("metadata", {}),
        )
    
    def verify_proof(
        self,
        package: bytes,
        circuit: str,
    ) -> Dict[str, Any]:
        """
        Verify a ZK proof from a CT-Wrap package.
        
        Args:
            package: The CT-Wrap package containing the proof
            circuit: Circuit ID to verify against
        
        Returns:
            Verification result with validity and public signals
        """
        payload = {
            "package": base64.b64encode(package).decode(),
            "circuit": circuit,
        }
        
        response = self.session.post(
            f"{self.base_url}/api/v1/proof/verify",
            json=payload
        )
        response.raise_for_status()
        return response.json()
    
    def get_circuits(self) -> List[str]:
        """Get list of available ZK circuits"""
        response = self.session.get(f"{self.base_url}/api/v1/proof/circuits")
        response.raise_for_status()
        return response.json()
    
    def get_verification_key(self, circuit_id: str) -> Dict[str, Any]:
        """Get verification key for a circuit"""
        response = self.session.get(
            f"{self.base_url}/api/v1/proof/circuits/{circuit_id}/vkey"
        )
        response.raise_for_status()
        return response.json()
    
    def health_check(self) -> bool:
        """Check if the API is healthy"""
        try:
            response = self.session.get(f"{self.base_url}/api/v1/health")
            return response.status_code == 200
        except requests.RequestException:
            return False
```

---

## 9. Testing Requirements

### 9.1 Unit Tests

Create comprehensive tests for each component:

```rust
// tests/crypto_tests.rs
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_ml_kem_roundtrip() {
        oqs::init();
        
        // Generate key pair
        let keypair = MlKemKeyPair::generate().unwrap();
        
        // Encapsulate
        let encap = encapsulate(&keypair.public_key).unwrap();
        
        // Decapsulate
        let recovered = keypair.decapsulate(&encap.ciphertext).unwrap();
        
        assert_eq!(encap.shared_secret, recovered);
    }
    
    #[test]
    fn test_aes_gcm_siv_roundtrip() {
        let key = [0u8; 32];
        let plaintext = b"Hello, CT-Wrap!";
        let aad = b"metadata";
        
        let encrypted = encrypt_aes_gcm_siv(&key, plaintext, aad).unwrap();
        let decrypted = decrypt_aes_gcm_siv(
            &key,
            &encrypted.nonce,
            &encrypted.ciphertext,
            aad
        ).unwrap();
        
        assert_eq!(plaintext.to_vec(), decrypted);
    }
    
    #[test]
    fn test_ml_dsa_signature() {
        oqs::init();
        
        let keypair = MlDsaKeyPair::generate().unwrap();
        let message = b"Sign this message";
        
        let signature = keypair.sign(message).unwrap();
        let valid = verify_signature(&keypair.public_key, message, &signature).unwrap();
        
        assert!(valid);
    }
    
    #[test]
    fn test_wrap_unwrap_roundtrip() {
        oqs::init();
        
        // Generate recipient keys
        let recipient = MlKemKeyPair::generate().unwrap();
        
        // Original data
        let data = b"Secret message for testing";
        
        // Wrap
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
        
        let package = wrap(data, config).unwrap();
        
        // Unwrap
        let recovered = unwrap(&package, &recipient).unwrap();
        
        assert_eq!(data.to_vec(), recovered);
    }
}
```

### 9.2 Integration Tests

```typescript
// tests/integration.test.ts
import { CTWrapClient } from '../src';

describe('CT-Wrap Integration Tests', () => {
    let client: CTWrapClient;
    
    beforeAll(() => {
        client = new CTWrapClient('http://localhost:3000');
    });
    
    test('full wrap/unwrap cycle with proof', async () => {
        // Generate keys
        const keys = await client.generateKeys();
        expect(keys.publicKey.length).toBe(1568); // ML-KEM-1024
        
        // Wrap data
        const data = new TextEncoder().encode('Test message');
        const result = await client.wrap(data, [keys.publicKey], {
            generateProof: true,
            contentType: 'text/plain',
        });
        
        expect(result.package.length).toBeGreaterThan(0);
        expect(result.proof).toBeDefined();
        expect(result.proof?.commitment).toBeTruthy();
        
        // Unwrap data
        const decrypted = await client.unwrap(result.package, keys.secretKey);
        
        expect(new TextDecoder().decode(decrypted.data)).toBe('Test message');
        expect(decrypted.contentType).toBe('text/plain');
    });
    
    test('proof verification', async () => {
        const keys = await client.generateKeys();
        const data = new TextEncoder().encode('Provable data');
        
        const result = await client.wrap(data, [keys.publicKey], {
            generateProof: true,
            circuit: 'data_commitment',
        });
        
        const verification = await client.verifyProof(
            result.package,
            'data_commitment'
        );
        
        expect(verification.valid).toBe(true);
    });
});
```

### 9.3 ZK Circuit Tests

```javascript
// tests/circuits.test.js
const { buildPoseidon } = require('circomlibjs');
const snarkjs = require('snarkjs');
const fs = require('fs');
const path = require('path');

describe('ZK Circuits', () => {
    let poseidon;
    
    beforeAll(async () => {
        poseidon = await buildPoseidon();
    });
    
    test('data_commitment circuit', async () => {
        // Test data
        const data = [1n, 2n, 3n, 4n];
        const commitment = poseidon.F.toObject(poseidon(data));
        
        const input = {
            data: data.map(x => x.toString()),
            commitment: commitment.toString(),
        };
        
        const { proof, publicSignals } = await snarkjs.groth16.fullProve(
            input,
            path.join(__dirname, '../build/circuits/data_commitment_js/data_commitment.wasm'),
            path.join(__dirname, '../build/circuits/data_commitment_final.zkey')
        );
        
        const vkey = JSON.parse(fs.readFileSync(
            path.join(__dirname, '../build/circuits/data_commitment_verification_key.json')
        ));
        
        const valid = await snarkjs.groth16.verify(vkey, publicSignals, proof);
        expect(valid).toBe(true);
    });
});
```

---

## 10. Security Considerations

### 10.1 Critical Security Requirements

| Requirement | Implementation |
|-------------|----------------|
| Key Generation | Use system CSPRNG via `rand::rngs::OsRng` |
| Nonce Generation | Random 96-bit nonce per encryption |
| Key Derivation | SHAKE256 with domain separation |
| Memory Handling | Zeroize sensitive data after use |
| Side Channels | Use constant-time operations where possible |
| Error Messages | Don't leak sensitive information |

### 10.2 Zeroization

```rust
use zeroize::Zeroize;

impl Drop for MlKemKeyPair {
    fn drop(&mut self) {
        self.secret_key.zeroize();
    }
}

impl Drop for MlDsaKeyPair {
    fn drop(&mut self) {
        self.secret_key.zeroize();
    }
}
```

### 10.3 Input Validation

```rust
pub fn validate_wrap_input(
    data: &[u8],
    recipients: &[RecipientPublicKey],
) -> Result<(), ValidationError> {
    // Check data size
    if data.len() > MAX_DATA_SIZE {
        return Err(ValidationError::DataTooLarge);
    }
    
    // Check recipient count
    if recipients.is_empty() {
        return Err(ValidationError::NoRecipients);
    }
    if recipients.len() > MAX_RECIPIENTS {
        return Err(ValidationError::TooManyRecipients);
    }
    
    // Validate public key sizes
    for recipient in recipients {
        if recipient.ml_kem_pk.len() != ML_KEM_1024_PUBLIC_KEY_SIZE {
            return Err(ValidationError::InvalidPublicKeySize);
        }
    }
    
    Ok(())
}
```

### 10.4 Rate Limiting

Implement rate limiting on the API to prevent abuse:

```rust
use tower_governor::{GovernorConfig, GovernorLayer};

let governor_conf = GovernorConfig::default();
let governor_layer = GovernorLayer {
    config: governor_conf,
};

let app = Router::new()
    .route("/api/v1/wrap", post(wrap_handler))
    .layer(governor_layer);
```

---

## Summary: Build Order

1. **Phase 1**: Implement crypto primitives (ML-KEM, AES-GCM-SIV, ML-DSA)
2. **Phase 2**: Create and test ZK circuits (circom + snarkjs)
3. **Phase 3**: Build serialization layer (CBOR package format)
4. **Phase 4**: Implement API service (Rust + Axum)
5. **Phase 5**: Deploy smart contracts (Solidity verifier)
6. **Phase 6**: Build SDKs (TypeScript, Python)
7. **Testing**: Comprehensive unit, integration, and E2E tests
8. **Security**: Audit, penetration testing, formal verification

---

## File Structure

```
ct-wrap/
├── Cargo.toml
├── src/
│   ├── main.rs
│   ├── lib.rs
│   ├── crypto/
│   │   ├── mod.rs
│   │   ├── ml_kem.rs
│   │   ├── ml_dsa.rs
│   │   ├── aes_gcm_siv.rs
│   │   └── kdf.rs
│   ├── zk/
│   │   ├── mod.rs
│   │   └── prover.rs
│   ├── package/
│   │   └── mod.rs
│   ├── wrap.rs
│   └── api/
│       └── mod.rs
├── circuits/
│   ├── data_commitment.circom
│   ├── range_commitment.circom
│   └── merkle_membership.circom
├── contracts/
│   ├── CTWrapVerifier.sol
│   └── Groth16Verifier.sol (generated)
├── sdk/
│   ├── typescript/
│   │   └── src/index.ts
│   └── python/
│       └── ctwrap/client.py
├── scripts/
│   ├── setup_circuits.sh
│   ├── generate_proof.js
│   └── deploy.ts
├── tests/
│   ├── crypto_tests.rs
│   ├── integration.test.ts
│   └── circuits.test.js
└── build/
    └── circuits/ (generated)
```

---

**END OF INSTRUCTIONS**

This document provides complete specifications for an LLM coding agent to build the CT-Wrap system. Each phase can be implemented independently and tested before proceeding to the next.
