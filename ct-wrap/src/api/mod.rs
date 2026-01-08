use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

use axum::{
    extract::{Json, State},
    http::StatusCode,
    response::IntoResponse,
    routing::{get, post},
    Router,
};
use base64::Engine;
use serde::{Deserialize, Serialize};
use tower_governor::{GovernorConfig, GovernorLayer};

use crate::crypto::{MlKemKeyPair};
use crate::package::CTWrapPackage;
use crate::wrap::{unwrap as unwrap_pkg, wrap as wrap_data, RecipientPublicKey, WrapConfig};

#[derive(Clone)]
pub struct ApiState {
    pub circuit_dir: PathBuf,
    pub verification_keys: HashMap<String, Vec<u8>>,
}

impl Default for ApiState {
    fn default() -> Self {
        Self {
            circuit_dir: PathBuf::from("build/circuits"),
            verification_keys: HashMap::new(),
        }
    }
}

pub fn router(state: ApiState) -> Router {
    let governor_conf = GovernorConfig::default();
    Router::new()
        .route("/health", get(|| async { "ok" }))
        .route("/api/v1/wrap", post(wrap_handler))
        .route("/api/v1/unwrap", post(unwrap_handler))
        .with_state(Arc::new(state))
        .layer(GovernorLayer { config: governor_conf })
}

#[derive(Debug, Deserialize)]
pub struct WrapRequest {
    pub data: String, // base64
    pub recipients: Vec<String>, // base64 ML-KEM pks
    pub content_type: Option<String>,
    pub generate_proof: Option<bool>,
    pub circuit: Option<String>,
}

#[derive(Debug, Serialize)]
pub struct WrapResponse {
    pub package: String, // base64 CBOR
    pub package_hash: String, // hex
}

async fn wrap_handler(
    State(state): State<Arc<ApiState>>,
    Json(req): Json<WrapRequest>,
) -> impl IntoResponse {
    let b64 = base64::engine::general_purpose::STANDARD;
    let data = match b64.decode(req.data.as_bytes()) {
        Ok(d) => d,
        Err(_) => return (StatusCode::BAD_REQUEST, "invalid base64 data").into_response(),
    };

    let mut recipients = Vec::with_capacity(req.recipients.len());
    for pk_b64 in &req.recipients {
        let pk = match b64.decode(pk_b64.as_bytes()) {
            Ok(d) => d,
            Err(_) => return (StatusCode::BAD_REQUEST, "invalid base64 public key").into_response(),
        };
        recipients.push(RecipientPublicKey { ml_kem_pk: pk, x25519_pk: None });
    }

    let config = WrapConfig {
        recipients,
        signer: None,
        generate_zk_proof: req.generate_proof.unwrap_or(false),
        zk_circuit: req.circuit,
        content_type: req.content_type,
        access_policy: None,
        custom_metadata: HashMap::new(),
    };

    let pkg = match wrap_data(&data, config) {
        Ok(p) => p,
        Err(e) => return (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()).into_response(),
    };

    let pkg_cbor = match pkg.to_cbor() {
        Ok(b) => b,
        Err(_) => return (StatusCode::INTERNAL_SERVER_ERROR, "serialization failed").into_response(),
    };

    let resp = WrapResponse {
        package: b64.encode(pkg_cbor),
        package_hash: hex::encode(pkg.hash()),
    };

    let _ = &state.circuit_dir;
    (StatusCode::OK, Json(resp)).into_response()
}

#[derive(Debug, Deserialize)]
pub struct UnwrapRequest {
    pub package: String, // base64 CBOR
    pub recipient_public_key: String, // base64
    pub recipient_secret_key: String, // base64
}

#[derive(Debug, Serialize)]
pub struct UnwrapResponse {
    pub data: String, // base64
    pub content_type: Option<String>,
}

async fn unwrap_handler(Json(req): Json<UnwrapRequest>) -> impl IntoResponse {
    let b64 = base64::engine::general_purpose::STANDARD;
    let pkg_bytes = match b64.decode(req.package.as_bytes()) {
        Ok(b) => b,
        Err(_) => return (StatusCode::BAD_REQUEST, "invalid base64 package").into_response(),
    };
    let pkg = match CTWrapPackage::from_cbor(&pkg_bytes) {
        Ok(p) => p,
        Err(_) => return (StatusCode::BAD_REQUEST, "invalid package").into_response(),
    };

    let pk = match b64.decode(req.recipient_public_key.as_bytes()) {
        Ok(b) => b,
        Err(_) => return (StatusCode::BAD_REQUEST, "invalid base64 public key").into_response(),
    };
    let sk = match b64.decode(req.recipient_secret_key.as_bytes()) {
        Ok(b) => b,
        Err(_) => return (StatusCode::BAD_REQUEST, "invalid base64 secret key").into_response(),
    };
    let kp = MlKemKeyPair::from_bytes(pk, sk);

    let plaintext = match unwrap_pkg(&pkg, &kp) {
        Ok(p) => p,
        Err(e) => return (StatusCode::FORBIDDEN, e.to_string()).into_response(),
    };

    let resp = UnwrapResponse {
        data: b64.encode(plaintext),
        content_type: pkg.metadata.content_type,
    };
    (StatusCode::OK, Json(resp)).into_response()
}
