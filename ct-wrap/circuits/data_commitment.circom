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
