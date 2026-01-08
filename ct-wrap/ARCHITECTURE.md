# CT-Wrap Architecture

## Overview

CT-Wrap is a post-quantum hybrid cryptographic package format and service:
- ML-KEM-1024 (Kyber1024) per-recipient encapsulation
- AES-256-GCM-SIV payload encryption under a random CEK
- Optional ML-DSA-87 (Dilithium5) signatures
- Optional Groth16 proofs (Circom/snarkjs), with verification-key hash binding

## Flow Diagrams

### Wrap Flow

1. plaintext
2. SHA3-256(plaintext) → `content_hash`
3. random(32) → `CEK`
4. For each recipient:
   - ML-KEM.Encaps(pk) → (ss, ct)
   - SHAKE256(ss, "CT-WRAP-CEK-MASK-v1") → mask
   - `wrapped_cek = CEK ⊕ mask`
5. AES-GCM-SIV(CEK, plaintext, AAD) → ciphertext
6. [optional] ML-DSA.Sign(sk, sign_data) → signature
7. [optional] Groth16.Prove(circuit, plaintext) → zk_proof
8. Output: `CTWrapPackage` (CBOR)

### Unwrap Flow

1. CTWrapPackage
2. Find `KeyEncapsulation` by `recipient_id`
3. ML-KEM.Decaps(sk, ct) → ss
4. SHAKE256(ss, "CT-WRAP-CEK-MASK-v1") → mask
5. `CEK = wrapped_cek ⊕ mask`
6. Check `aad_hash` matches recomputed AAD
7. [if signature] ML-DSA.Verify(pk, sign_data, sig) → assert valid
8. AES-GCM-SIV.Decrypt(CEK, ciphertext, AAD) → plaintext
9. SHA3-256(plaintext) == `content_hash` → assert match
10. [if zk_proof && verify_zk] snarkjs.verify(vk, public, proof) → assert valid
11. Output: plaintext

## Security Properties

| Property | Mechanism |
|----------|-----------|
| PQ-resistant KEX | ML-KEM-1024 (NIST Level 5) |
| PQ-resistant signatures | ML-DSA-87 (NIST Level 5) |
| Authenticated encryption | AES-256-GCM-SIV |
| Integrity | SHA3-256 content hash + AAD binding |
| Forward secrecy | Fresh KEM per wrap |
| ZK binding | `verification_key_hash` prevents VK substitution |

