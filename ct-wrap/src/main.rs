use std::net::SocketAddr;

use axum::Router;
use ct_wrap::api::{router as api_router, ApiState};

#[tokio::main]
async fn main() {
    let state = ApiState::default();
    let app: Router = api_router(state);

    let addr = SocketAddr::from(([127, 0, 0, 1], 3000));
    eprintln!("ct-wrap listening on http://{addr}");

    let listener = tokio::net::TcpListener::bind(addr)
        .await
        .expect("bind");
    axum::serve(listener, app).await.expect("serve");
}
