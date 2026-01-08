use std::path::Path;
use std::process::Command;

use serde::{Deserialize, Serialize};

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

/// Generate a ZK proof by calling the Node.js helper script.
///
/// This keeps the Rust binary lean and lets you swap Groth16/PLONK backends later.
pub fn generate_proof(
    data: &[u8],
    circuit_name: &str,
    build_dir: &Path,
) -> Result<ZkProofResult, Box<dyn std::error::Error>> {
    let data_hex = hex::encode(data);
    let script = Path::new("scripts").join("generate_proof.js");
    let output = Command::new("node")
        .arg(script)
        .arg("--circuit")
        .arg(circuit_name)
        .arg("--build-dir")
        .arg(build_dir)
        .arg("--data-hex")
        .arg(data_hex)
        .output()?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("zk proof generation failed: {stderr}").into());
    }

    let stdout = String::from_utf8(output.stdout)?;
    let parsed: ZkProofResult = serde_json::from_str(&stdout)?;
    Ok(parsed)
}
