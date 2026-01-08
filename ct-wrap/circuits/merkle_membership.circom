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

    for (var i = 0; i < LEVELS; i++) {
        hashers[i] = Poseidon(2);

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

component main {public [root]} = MerkleProof(20);
