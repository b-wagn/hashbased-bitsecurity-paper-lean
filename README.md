# XMSS and SLH-DSA bit security in Lean 4

Machine-checked correctness, security proofs, and attacks for target-sum and checksum XMSS, and
correctness and a 127-bit security proof for SLH-DSA-SHAKE-128s, using
[VCVio](https://github.com/Verified-zkEVM/VCVio).

## XMSS

Both schemes use 128-bit hashes, `2^32` epochs, 16-position chains (`w = 4`), and 256-bit messages and seeds. Key generation stores the chain values and Merkle tree.

- **Target sum:** 32 chains, digit sum 330, at most `2^32` signing attempts.
- **Checksum:** 32 message chains plus 3 checksum chains, one signing attempt.

### Results

Exact integer security levels for all 16 counting modes containing direct hash queries, under strong (SUF-CMA) and standard (EUF-CMA) unforgeability: **64 combinations**. An entry `b` means security at `b` bits and an attack ruling out `b + 1` bits.

| Counted queries            | Target sum, SUF-CMA | Target sum, EUF-CMA | Checksum, both |
| -------------------------- | ------------------- | ------------------- | -------------- |
| `q_H`                      | 122                 | 126                 | 122            |
| `q_H, q_S`                 | 122                 | 127                 | 122            |
| `q_H, q_Sign`              | 127                 | 127                 | 123            |
| `q_H, q_S, q_Sign`         | 127                 | 127                 | 124            |
| plus `q_Gen` or `q_Verify` | 127                 | 127                 | 127            |

`q_H` counts direct hash queries, `q_S` signing requests, and `q_Gen`/`q_Sign`/`q_Verify` the hashes of key generation, signing, and final verification. Security at `b` bits means `Pr[win] ≤ q / 2^b` for every budget `q ≥ 1` bounding the selected counts with probability one.

**Correctness:** error at most `2^-256` for target sum and `0` for checksum.

## SLH-DSA-SHAKE-128s

[`SlhDsaSecurity/`](SlhDsaSecurity/) formalizes FIPS 205 SLH-DSA at the 128s parameter set
(`n = 16`, `h = 63`, `d = 7`, `h' = 9`, `a = 12`, `k = 14`, `w = 16`) with deterministic signing,
byte-level addresses, the checksum, and the standard 7856-byte signature encoding, all sharing one
lazily sampled random oracle.

- **Strong unforgeability, 127 bits:** `Pr[win] ≤ q / 2^127` for every adversary whose work is
  at most `q ≥ 1` with probability one, where the game is an `Xmss.SecurityGame` counting hash
  calls by source (`sign`, `hash`, `keygen`, `signer`, `verifier`) and the counting mode is
  `Z = {sign, hash, keygen, verifier}`: signing requests, the adversary's own hash calls, key
  generation's and final verification's — every source but the signer's own hash calls
  ([`SecurityBySource.lean`](SlhDsaSecurity/Statement/SecurityBySource.lean),
  [`StrongUnforgeability.lean`](SlhDsaSecurity/Statement/Theorems/StrongUnforgeability.lean)).
  The framework has no signing limit and SLH-DSA's security fails without one (past `2^64`
  signatures the FORS leaves are all revealed), so `HasLimitedSecurityBits` adds FIPS 205's
  `2^64` as an almost-sure bound on the `sign` count.
- **Correctness:** error `0`; a request with an over-long context is always rejected
  ([`Correctness.lean`](SlhDsaSecurity/Statement/Theorems/Correctness.lean)).

The proof splits the forgery event into an *answer* half (a fresh hash answer hitting a target:
FORS coverage, structural collisions) and a *shared* half (a query guessing a secret the
adversary has not been given: an unrevealed cell of the key, or `SK.prf`). The answer half is
`AnswerFired`. The shared half caps the adversary at the budget left after key generation
(`ShareRealCap`), couples the real game with a lenient presentation of it (`ShareWhole`,
`ShareEvent`), moves to a blind game identical until a sticky flag (`ShareUntilBad`), and charges
the flag one `2^-128` per recorded guess by stalling and redrawing each unrevealed cell
(`BlindCharge`, `ShareBound`). `BySourceTarget` assembles the bound. With the signer's calls free,
the answer half charges structural faults per *fresh cache entry* rather than per
query (`FreshExpectation`): the signer's millions of canonical queries are cache hits, and its
only fresh entries are its `PRF_msg` and digest inputs, one digest per request.

## Code

For XMSS, [`Statement/`](Xmss/Statement/) holds the definitions and the six main theorems: the scheme in [`Scheme/`](Xmss/Statement/Scheme/), the games in `CorrectnessGame.lean` and `UnforgeabilityGame.lean`, the measure in `BitSecurity.lean`, and the results in [`Theorems/`](Xmss/Statement/Theorems/). Only those three theorem files import [`Proof/`](Xmss/Proof/). SLH-DSA follows the same layout under [`SlhDsaSecurity/Statement/`](SlhDsaSecurity/Statement/): the scheme, the games in `Security.lean`, `SecurityBySource.lean` and `CorrectnessGame.lean`, and the main theorems in [`Theorems/`](SlhDsaSecurity/Statement/Theorems/).

## Build

Lean `v4.31.0`; VCVio pinned to `cbd4144`.

```sh
lake exe cache get
lake build
scripts/check_statement_imports.sh
python3 scripts/generate_encoding_count.py --check
```

The build checks all proofs and guards the main theorems' axioms: `propext`, `Classical.choice`, and `Quot.sound`. For SLH-DSA every public theorem is guarded in [`Proof/Axioms.lean`](SlhDsaSecurity/Proof/Axioms.lean) and `Proof/AxiomWalk.lean` checks every declaration; `python3 scripts/guard_sweep.py .` reports any public theorem without a guard.
