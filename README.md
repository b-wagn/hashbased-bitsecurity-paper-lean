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
| Proofs | `XmssSecurity/Proof/` | proofs of the unchanged statement layer, including stronger numerical bounds |
| | `XmssSecurity/Proof/Direct/` | the direct-count proof: pruning a semantically bounded adversary to a syntactically bounded one (`Basic`, `Prune`, `Bridge`), the per-term bounds (`FirstLane`, `Structural`, `Prehit`, `SeedGuessing`, `VerifierBound`), and the assembly |
| Main theorems | `XmssSecurity.lean` | one theorem per claim, with an axiom guard |

## Claims and theorems

| Claim | Bits | Theorem |
|---|---|---|
| `XmssSufCmaAllHashesStatement`: counting every hash call of the experiment | 127 | `xmss_sufCma_allHashes_127` |
| `XmssSufCmaDirectStatement`: the original direct-query milestone | 119 | `xmss_sufCma_direct_119` |
| Stronger direct-query security | 122 | `xmss_sufCma_direct_122` |
| Every counting mode | 122 | `xmss_sufCma_secure_122` |
| Direct queries and key generation | 127 | `xmss_sufCma_keygen_127` |
| Every mode charging key generation | 127 | `xmss_sufCma_secure_127_of_keygen` |
| Direct queries and verification | 127 | `xmss_sufCma_verifier_127` |
| Every mode charging verification | 127 | `xmss_sufCma_secure_127_of_verifier` |
| Every hash call and every signing request | 127 | `xmss_sufCma_everything_127` |

The direct proof now reaches the conjectured lower bound of 122 bits. It selects one deciding
chain, charges one probe in the first lane, and charges at most 40 verification queries on the
deciding path in the second lane. See `Proof/Direct/DecidingSecurity.lean` and
[`docs/plan-direct-122.md`](docs/plan-direct-122.md). The original 119-bit statement is unchanged.

The keygen-counted 127-bit proof shares the direct-query budget between encoding prehits and
structural collisions, and subtracts the exact key-generation cost from the charged budget.
See `Proof/Direct/SharedDecidingBudget.lean` and `Proof/Modes/Keygen.lean`.

The verifier-counted proof uses the exact 133-query cost of accepting verification. Pruning
preserves the contribution of successful executions after subtracting that cost, even when
unsuccessful executions exceed the reduced budget. See `Proof/Modes/Verifier.lean`.

Exact security for all sixteen modes remains open. `Proof/Modes/Exact.lean` reduces it to six
basis obligations, of which three remain: 127-bit security when only signer hashes are
additionally charged; an attack against 123 bits when direct
queries and signing requests are charged; and an attack against 128 bits when everything is
charged. No attack theorem is proved yet.

The encoding prerequisites now include a kernel-checked exact count of admissible digests:
`11539185377238682781344003244544752`. Thus a uniform digest is accepted with probability
strictly between `2^-15` and `2^-14`. `Proof/EncodingCardinality.lean` proves the counting
recurrence; `scripts/generate_encoding_count.py` generates finite certificates whose equations
Lean checks. `Proof/EncodingProbability.lean` derives the probability bounds and the average
number of collision opportunities when a uniformly chosen signature chain is changed.
`Proof/EncodingRejectionProbability.lean` accounts for repeated randomizers and proves that
a fresh signing request in the randomized reference scheme succeeds with probability greater
than `31/32` after every supported key-generation result.

The adversary is probabilistic, adaptive, and unbounded in time and memory. Each counting mode
specifies which hash queries and signing requests are charged. The probability is over the
master seed, the random oracle, and the adversary's private randomness.

## Building

```
lake exe cache get   # Mathlib cache
lake build           # everything, including the axiom check in XmssSecurity.lean
```

Toolchain: Lean `v4.31.0`; VCVio pinned to `cbd4144` in `lakefile.toml`.

The main theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`; the root module
checks this with `#guard_msgs`, so the build fails if a `sorry` or a nonstandard axiom enters.
