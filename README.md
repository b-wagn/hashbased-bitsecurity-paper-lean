# Security of XMSS in the random-oracle model, in Lean 4

Machine-checked security statements and proofs for the XMSS instance of Ethereum's
post-quantum consensus, in Lean 4 using [VCVio](https://github.com/Verified-zkEVM/VCVio).
The development started from the 127-bit SUF-CMA proof in
[leanEthereum/leanVM](https://github.com/leanEthereum/leanVM/tree/main/formal/xmss) and
separates *what is claimed* from *why it holds*.

*Disclaimer.* The Lean code proves statements about the scheme as defined in `Statement/Scheme/`,
with the hash function modelled as a random oracle. It does not prove security of any
implementation and cannot replace an audit.

## Layout

The statement layer is meant to be read on its own; nothing in it depends on `Proof/`.

| Part | File(s) | Content |
|---|---|---|
| Signature schemes | `XmssSecurity/Statement/SynchronizedSignature.lean` | syntax of synchronized (epoch-based) signature schemes, eprint 2025/055 Def. 7 |
| Random-oracle model | `XmssSecurity/Statement/RandomOracleModel.lean` | the oracle world (private sampling + hash oracle), lazy random oracle, hash-query counting |
| Security notions | `XmssSecurity/Statement/Security/SUFCMA.lean` | strong unforgeability under chosen-message attacks (one file per notion) |
| Bit security | `XmssSecurity/Statement/BitSecurity.lean` | `SecurityNotion` and `HasClassicalSecurityBits`: `Pr[win] ≤ q / 2^bits` for every `q`-query adversary |
| The scheme | `XmssSecurity/Statement/Scheme/Parameters.lean` | the parameter table (`n`, `w`, `v`, `T`, `h`, `L`, `A_max`, …) |
| | `XmssSecurity/Statement/Scheme/Construction.lean` | tweaks, target-sum encoding, chains, Merkle tree, key generation, signing, verification |
| | `XmssSecurity/Statement/Scheme/Xmss.lean` | `xmss`, the scheme as a `SynchronizedSignature` |
| Claims | `XmssSecurity/Statement/Claims.lean` | the bit-security statements, one per notion |
| Proofs | `XmssSecurity/Proof/` | the proofs; only the number of bits in a claim may change during proof search |
| | `XmssSecurity/Proof/Direct/` | the direct-count proof: pruning a semantically bounded adversary to a syntactically bounded one (`Basic`, `Prune`, `Bridge`), the per-term bounds (`FirstLane`, `Structural`, `Prehit`, `SeedGuessing`, `VerifierBound`), and the assembly |
| Main theorems | `XmssSecurity.lean` | one theorem per claim, with an axiom guard |

## Claims and theorems

| Claim | Bits | Theorem |
|---|---|---|
| `XmssSufCmaTotalStatement`: SUF-CMA, counting every hash call of the experiment | 127 | `xmss_has_127_bits_of_classical_security` |
| `XmssSufCmaDirectStatement`: SUF-CMA, counting only the adversary's own hash calls | 119 | `xmss_has_119_bits_of_classical_direct_security` |

The direct-count level is what the current proof gives, not a known attack: the proof charges the
133 hash calls of verifying the forgery and 42 chain probes at full weight `2^-128`, which costs
`log2(312) ≈ 8` bits at query budgets of a few queries. Sharpening these terms is the natural next
step (see `XmssSecurity/Proof/Direct/Assemble.lean`).

The adversary is probabilistic, adaptive, and unbounded in time and memory; only hash queries are
counted. The probability is over the master seed, the random oracle, and the adversary's private
randomness.

## Building

```
lake exe cache get   # Mathlib cache
lake build           # everything, including the axiom check in XmssSecurity.lean
```

Toolchain: Lean `v4.31.0`; VCVio pinned to `cbd4144` in `lakefile.toml`.

The main theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`; the root module
checks this with `#guard_msgs`, so the build fails if a `sorry` or a nonstandard axiom enters.
