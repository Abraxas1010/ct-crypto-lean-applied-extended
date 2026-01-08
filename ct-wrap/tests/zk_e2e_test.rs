//! End-to-end ZK smoke test.
//! Only runs when ZK toolchain is available (circom, ptau, npm deps).

use std::path::Path;
use std::process::Command;

fn zk_toolchain_available() -> bool {
    // Check circom
    if !Command::new("circom").arg("--version").output().is_ok() {
        return false;
    }
    // Check snarkjs (via npx or PATH)
    if !Command::new("npx")
        .args(["--no-install", "snarkjs", "--help"])
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
    {
        if !Command::new("snarkjs").arg("--help").output().is_ok() {
            return false;
        }
    }
    // Check ptau file exists
    if !Path::new("powersOfTau28_hez_final_16.ptau").exists() {
        return false;
    }
    // Check circuits are built
    if !Path::new("build/circuits/data_commitment_final.zkey").exists() {
        return false;
    }
    true
}

#[test]
#[ignore] // Run with: cargo test -- --ignored zk_e2e
fn zk_e2e_happy_path() {
    if !zk_toolchain_available() {
        eprintln!("Skipping ZK e2e test: toolchain not available");
        return;
    }

    use ct_wrap::crypto::MlKemKeyPair;
    use ct_wrap::wrap::{unwrap, wrap, RecipientPublicKey, WrapConfig};
    use std::collections::HashMap;

    let recipient = MlKemKeyPair::generate().unwrap();
    let data = b"ZK test payload for data_commitment circuit";

    let config = WrapConfig {
        recipients: vec![RecipientPublicKey {
            ml_kem_pk: recipient.public_key.clone(),
            x25519_pk: None,
        }],
        signer: None,
        generate_zk_proof: true,
        zk_circuit: Some("data_commitment".to_string()),
        content_type: Some("application/octet-stream".to_string()),
        access_policy: None,
        custom_metadata: HashMap::new(),
    };

    let package = wrap(data, config).expect("wrap with ZK proof failed");

    // Verify ZK proof is present and has non-zero vk hash
    let zk = package.zk_proof.as_ref().expect("ZK proof missing");
    assert_eq!(zk.circuit_id, "data_commitment");
    assert_ne!(
        zk.verification_key_hash, [0u8; 32],
        "VK hash should not be zero"
    );
    assert!(!zk.public_signals.is_empty(), "public signals should exist");

    // Verify unwrap succeeds
    let recovered = unwrap(&package, &recipient).expect("unwrap failed");
    assert_eq!(data.to_vec(), recovered);

    eprintln!("ZK e2e test passed: proof generated and verified");
}

#[test]
#[ignore] // Run with: cargo test -- --ignored zk_e2e
fn zk_e2e_verify_proof() {
    if !zk_toolchain_available() {
        eprintln!("Skipping ZK e2e test: toolchain not available");
        return;
    }

    use ct_wrap::crypto::MlKemKeyPair;
    use ct_wrap::wrap::{unwrap_with_config, wrap, RecipientPublicKey, UnwrapConfig, WrapConfig};
    use ct_wrap::zk::verify_proof;
    use std::collections::HashMap;
    use std::path::PathBuf;

    let recipient = MlKemKeyPair::generate().unwrap();
    let data = b"ZK test payload for data_commitment circuit";

    let config = WrapConfig {
        recipients: vec![RecipientPublicKey {
            ml_kem_pk: recipient.public_key.clone(),
            x25519_pk: None,
        }],
        signer: None,
        generate_zk_proof: true,
        zk_circuit: Some("data_commitment".to_string()),
        content_type: Some("application/octet-stream".to_string()),
        access_policy: None,
        custom_metadata: HashMap::new(),
    };

    let package = wrap(data, config).unwrap();

    // Verify proof standalone
    let result = verify_proof(
        package.zk_proof.as_ref().unwrap(),
        Path::new("build/circuits"),
    )
    .unwrap();
    assert!(result.valid);

    // Verify during unwrap
    let config = UnwrapConfig {
        verify_zk_proof: true,
        build_dir: Some(PathBuf::from("build/circuits")),
    };
    let recovered = unwrap_with_config(&package, &recipient, config).unwrap();
    assert_eq!(data.to_vec(), recovered);
}
