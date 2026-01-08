pragma circom 2.1.0;

include "node_modules/circomlib/circuits/poseidon.circom";
include "node_modules/circomlib/circuits/comparators.circom";
include "node_modules/circomlib/circuits/bitify.circom";

/*
 * RangeCommitment Circuit
 *
 * Proves:
 *   1. I know data such that Poseidon(data) = commitment
 *   2. data[0] >= minValue
 *   3. data[0] <= maxValue
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
