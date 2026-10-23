# XMSS and SLH-DSA bit security in Lean 4

Machine-checked security proofs for XMSS and SLH-DSA-SHAKE-128s in the random-oracle model,
using [VCVio](https://github.com/Verified-zkEVM/VCVio).

## XMSS

Both schemes use 128-bit hashes, `2^32` epochs, 16-position chains (`w = 4`), and 256-bit messages and seeds. Key generation stores the chain values and Merkle tree.

- **Target sum:** 32 chains, digit sum 330, at most `2^32` signing attempts.
- **Checksum:** 32 message chains plus 3 checksum chains, one signing attempt.

## Results

Exact integer security levels for all 16 counting modes containing direct hash queries, under strong (SUF-CMA) and standard (EUF-CMA) unforgeability: **64 combinations**. An entry `b` means security at `b` bits and an attack ruling out `b + 1` bits.

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

FIPS 205 SLH-DSA at the 128s parameters, with deterministic signing and the SHAKE
instantiation's formats.

**Theorem** (`slhDsa_sufCma_127`): 127 bits of strong unforgeability, counting the adversary's
signing requests (`q_S`, at most `2^64`), its hash queries (`q_H`) and the verification of its forgery (`q_Verify`).

## Build

Lean `v4.31.0`, VCVio `cbd4144`.

```sh
lake exe cache get
lake build
scripts/check_statement_imports.sh
python3 scripts/generate_encoding_count.py --check
# SLH-DSA test vectors
git -C .lake/packages/VCVio submodule update --init   # VCVio's native libraries, needed to link
lake exe slh-dsa-kat                                  # signing takes minutes per vector
```

The build fails if a main theorem depends on an axiom other than `propext`, `Classical.choice` and
`Quot.sound`.
