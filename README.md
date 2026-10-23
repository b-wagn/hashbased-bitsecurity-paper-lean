# XMSS and SLH-DSA bit security in Lean 4

Machine-checked security proofs for XMSS and SLH-DSA-SHAKE-128s in the random-oracle model,
using [VCVio](https://github.com/Verified-zkEVM/VCVio). Security at `b` bits means
`Pr[win] ≤ q / 2^b` for every adversary whose counted queries are at most `q ≥ 1` with
probability one.

*Disclaimer.* The proofs are about the schemes as defined in each `Statement/` folder, with the hash
function modelled as a random oracle. They say nothing about any implementation.

## XMSS

Target-sum and checksum XMSS with 128-bit hashes, `2^32` epochs and `w = 4`. Exact security levels
(an entry `b` is proved, and an attack rules out `b + 1`):

| Counted queries            | Target sum, SUF-CMA | Target sum, EUF-CMA | Checksum, both |
| -------------------------- | ------------------- | ------------------- | -------------- |
| `q_H`                      | 122                 | 126                 | 122            |
| `q_H, q_S`                 | 122                 | 127                 | 122            |
| `q_H, q_Sign`              | 127                 | 127                 | 123            |
| `q_H, q_S, q_Sign`         | 127                 | 127                 | 124            |
| plus `q_Gen` or `q_Verify` | 127                 | 127                 | 127            |

`q_H` counts the adversary's hash queries, `q_S` its signing requests, and `q_Gen`, `q_Sign`,
`q_Verify` the hashes of key generation, signing and final verification. Correctness error is at
most `2^-256` (target sum) and `0` (checksum).

## SLH-DSA-SHAKE-128s

Pure FIPS 205 SLH-DSA at the 128s parameters, with deterministic signing and the SHAKE
instantiation's formats.

**Theorem** (`slhDsa_sufCma_127`): 127 bits of strong unforgeability, counting the adversary's
signing requests, its hash queries and the verification of its forgery. Key generation's and the
signer's hashes are free, and the adversary makes at most `2^64` signing requests.

## Layout

Each library splits into `Statement/` (scheme, games and main theorems, readable on its own) and
`Proof/`. Only `Statement/Theorems/` imports `Proof/`.

- XMSS: [`Xmss/Statement/Theorems/`](Xmss/Statement/Theorems/)
- SLH-DSA: [`SLH-DSA-SHAKE-128s/Statement/Theorems/StrongUnforgeability.lean`](SLH-DSA-SHAKE-128s/Statement/Theorems/StrongUnforgeability.lean)

## Build

Lean `v4.31.0`, VCVio `cbd4144`.

```sh
lake exe cache get
lake build
scripts/check_statement_imports.sh
python3 scripts/generate_encoding_count.py --check
```

The build fails if a main theorem depends on an axiom other than `propext`, `Classical.choice` and
`Quot.sound`.
