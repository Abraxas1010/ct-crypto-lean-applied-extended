#!/usr/bin/env node
/*
 * CT-Wrap: ZK proof helper
 *
 * This script is called by Rust to generate a Groth16 proof via snarkjs.
 * It reads raw data (hex), computes poseidon commitment, and runs fullProve.
 *
 * Output: JSON on stdout (ZkProofResult compatible).
 */

const fs = require("fs");
const path = require("path");

function parseArgs(argv) {
  const out = {};
  for (let i = 2; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--circuit") out.circuit = argv[++i];
    else if (a === "--build-dir") out.buildDir = argv[++i];
    else if (a === "--data-hex") out.dataHex = argv[++i];
    else if (a === "--input-json") out.inputJson = argv[++i];
  }
  return out;
}

function bytesToFieldElements(bytes, numElements) {
  const BYTES_PER_ELEMENT = 31;
  const elements = [];
  for (let i = 0; i < numElements; i++) {
    const start = i * BYTES_PER_ELEMENT;
    const end = Math.min(start + BYTES_PER_ELEMENT, bytes.length);
    const chunk = bytes.slice(start, end);
    let value = 0n;
    for (const b of chunk) value = (value << 8n) | BigInt(b);
    elements.push(value);
  }
  while (elements.length < numElements) elements.push(0n);
  return elements;
}

async function main() {
  const { circuit, buildDir, dataHex, inputJson } = parseArgs(process.argv);
  if (!circuit || !buildDir || (!dataHex && !inputJson)) {
    console.error(
      "Usage: generate_proof.js --circuit <name> --build-dir <dir> (--data-hex <hex> | --input-json <path>)"
    );
    process.exit(2);
  }

  const snarkjs = require("snarkjs");
  const { buildPoseidon } = require("circomlibjs");
  const poseidon = await buildPoseidon();

  let input;
  let commitment = "";

  if (inputJson) {
    input = JSON.parse(fs.readFileSync(inputJson, "utf8"));
    if (typeof input.commitment === "string") commitment = input.commitment;
  } else {
    if (circuit !== "data_commitment") {
      console.error(
        `Circuit '${circuit}' requires explicit inputs. Use --input-json for non-default circuits.`
      );
      process.exit(2);
    }
    const data = Buffer.from(dataHex, "hex");
    const elems = bytesToFieldElements(Uint8Array.from(data), 4);
    commitment = poseidon.F.toObject(poseidon(elems)).toString();
    input = {
      data: elems.map((x) => x.toString()),
      commitment,
    };
  }

  const wasmPath = path.join(buildDir, `${circuit}_js`, `${circuit}.wasm`);
  const zkeyPath = path.join(buildDir, `${circuit}_final.zkey`);

  const { proof, publicSignals } = await snarkjs.groth16.fullProve(input, wasmPath, zkeyPath);

  process.stdout.write(
    JSON.stringify({
      proof,
      public_signals: publicSignals,
      commitment,
    })
  );
}

main().catch((e) => {
  console.error(String(e && e.stack ? e.stack : e));
  process.exit(1);
});
