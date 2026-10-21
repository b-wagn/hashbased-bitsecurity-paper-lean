# XMSS bit security in Lean 4

Machine-checked correctness, security proofs, and attacks for the paper's target-sum and
checksum XMSS schemes, using [VCVio](https://github.com/Verified-zkEVM/VCVio).
Based on the XMSS development in [leanVM](https://github.com/leanEthereum/leanVM/tree/main/formal/xmss).

Both schemes use 128-bit hashes, `2^32` epochs, 16-position chains (`w = 4`), and 256-bit
messages and seeds. Key generation stores the chain values and Merkle tree.

- **Target sum:** 32 chains, digit sum 330, at most `2^32` signing attempts.
- **Checksum:** 32 message chains plus 3 checksum chains, one signing attempt.

## Results

Exact integer security levels for all 16 counting modes containing direct hash queries,
under strong (SUF-CMA) and standard (EUF-CMA) unforgeability: **64 combinations**.
An entry `b` means security at `b` bits and an attack ruling out `b + 1` bits.

`q_H` counts direct hash queries; `q_S` counts signing requests. `q_Gen`, `q_Sign`, and
`q_Verify` count hashes made by key generation, signing, and final verification.
For every budget `q ≥ 1`, security means `Pr[win] ≤ q / 2^b` whenever the sum of the
selected counts is at most `q` with probability one. Private sampling is free.

| Counted queries                                           | Target sum, SUF-CMA | Target sum, EUF-CMA | Checksum, both |
| --------------------------------------------------------- | ------------------- | ------------------- | -------------- |
| `q_H`                                                     | 122                 | 126                 | 122            |
| `q_H, q_S`                                                | 122                 | 127                 | 122            |
| `q_H, q_Sign`                                             | 127                 | 127                 | 123            |
| `q_H, q_S, q_Sign`                                        | 127                 | 127                 | 124            |
| Any mode including `q_H` and either `q_Gen` or `q_Verify` | 127                 | 127                 | 127            |

For checksum in mode `{q_H, q_S, q_Sign}`, the proof gives 124 bits and the attack is below
`log₂(3 · 2^128 / 32) ≈ 124.585` bits.
The paper's illustrative neighbor-attack budgets differ from the formal witnesses;
both establish the same security levels.

**Correctness:** error at most `2^-256` for target sum and `0` for checksum. The oracle
records and returns the first signing answer per epoch; repeated requests return `⊥`
without signing again and still count. With at most `q` requests, failure probability
is at most `δ · q`; hash queries are unlimited.

## Code

[Statement/](XmssSecurity/Statement/) contains the definitions and eight main theorems:
[strong unforgeability](XmssSecurity/Statement/StrongUnforgeabilityTheorems.lean),
[standard unforgeability](XmssSecurity/Statement/UnforgeabilityTheorems.lean), and
[correctness](XmssSecurity/Statement/CorrectnessTheorems.lean).
Only these theorem files import [Proof/](XmssSecurity/Proof/).

## Build

Lean `v4.31.0`; VCVio pinned to `cbd4144`.

```sh
lake exe cache get
lake build
scripts/check_statement_imports.sh
python3 scripts/generate_encoding_count.py --check
```

The build checks all proofs and guards the eight main theorems' axioms:
`propext`, `Classical.choice`, and `Quot.sound`.
