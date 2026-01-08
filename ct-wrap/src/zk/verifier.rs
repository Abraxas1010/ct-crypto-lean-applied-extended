//! ZK proof verification via snarkjs.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use sha3::{Digest, Sha3_256};

use crate::package::ZkProof;

#[derive(Debug)]
pub struct VerifyResult {
    pub valid: bool,
    pub circuit_id: String,
}

fn snarkjs_command() -> Result<Vec<String>, Box<dyn std::error::Error>> {
    if Command::new("npx")
        .args(["--no-install", "snarkjs", "--help"])
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
    {
        return Ok(vec![
            "npx".to_string(),
            "--no-install".to_string(),
            "snarkjs".to_string(),
        ]);
    }

    if Command::new("snarkjs")
        .arg("--help")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
    {
        return Ok(vec!["snarkjs".to_string()]);
    }

    Err("snarkjs not found (install via npm or put in PATH)".into())
}

fn unique_tmp_dir(prefix: &str) -> Result<PathBuf, Box<dyn std::error::Error>> {
    let pid = std::process::id();
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("{prefix}_{pid}_{nanos}"));
    fs::create_dir_all(&dir)?;
    Ok(dir)
}

fn write_json<P: AsRef<Path>, T: serde::Serialize>(
    path: P,
    value: &T,
) -> Result<(), Box<dyn std::error::Error>> {
    let bytes = serde_json::to_vec_pretty(value)?;
    fs::write(path, bytes)?;
    Ok(())
}

/// Verify a Groth16 proof using snarkjs.
/// Returns Ok(VerifyResult) on success, Err on verification failure or missing toolchain.
pub fn verify_proof(
    proof: &ZkProof,
    build_dir: &Path,
) -> Result<VerifyResult, Box<dyn std::error::Error>> {
    let circuit = proof.circuit_id.as_str();
    let vk_path = build_dir.join(format!("{circuit}_verification_key.json"));
    let vk_bytes = fs::read(&vk_path).map_err(|_| {
        format!(
            "missing verification key for circuit '{circuit}' at {}",
            vk_path.display()
        )
    })?;

    let vk_hash: [u8; 32] = Sha3_256::digest(&vk_bytes).into();
    if vk_hash != proof.verification_key_hash {
        return Err("verification key hash mismatch".into());
    }

    let tmp_dir = unique_tmp_dir("ct_wrap_snarkjs_verify")?;
    let proof_path = tmp_dir.join("proof.json");
    let public_path = tmp_dir.join("public.json");

    // snarkjs expects the "full" proof json (at least pi_a/pi_b/pi_c plus protocol/curve).
    let proof_json = serde_json::json!({
        "pi_a": proof.proof.pi_a,
        "pi_b": proof.proof.pi_b,
        "pi_c": proof.proof.pi_c,
        "protocol": "groth16",
        "curve": "bn128"
    });
    write_json(&proof_path, &proof_json)?;
    write_json(&public_path, &proof.public_signals)?;

    let mut cmd_parts = snarkjs_command()?;
    let program = cmd_parts.remove(0);
    let mut cmd = Command::new(program);
    cmd.args(cmd_parts);
    cmd.arg("groth16")
        .arg("verify")
        .arg(&vk_path)
        .arg(&public_path)
        .arg(&proof_path);

    let out = cmd.output()?;
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();

    let _ = fs::remove_dir_all(&tmp_dir);

    if !out.status.success() {
        return Err(format!("snarkjs verify failed: {stderr}").into());
    }

    let upper = stdout.to_ascii_uppercase();
    let valid = upper.contains("OK") && !upper.contains("INVALID");

    Ok(VerifyResult {
        valid,
        circuit_id: proof.circuit_id.clone(),
    })
}
