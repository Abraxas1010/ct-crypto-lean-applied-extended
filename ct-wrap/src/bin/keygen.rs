//! Generate ML-KEM keypair and print base64 to stdout.

use base64::Engine;
use ct_wrap::crypto::MlKemKeyPair;

fn main() {
    let kp = MlKemKeyPair::generate().expect("keypair generation failed");
    let b64 = base64::engine::general_purpose::STANDARD;
    println!("PUBLIC_KEY={}", b64.encode(kp.public_key_bytes()));
    println!("SECRET_KEY={}", b64.encode(kp.secret_key_bytes()));
}
