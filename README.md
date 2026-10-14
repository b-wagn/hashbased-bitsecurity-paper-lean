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
| Direct-query attack against 123 bits | upper bound 122 | `xmss_sufCma_direct_attack_122` |
| Direct queries plus signing requests: attack against 123 bits | upper bound 122 | `xmss_sufCma_requests_attack_122` |
| Direct-query security, both bounds | exactly 122 | `xmss_sufCma_direct_exact_122` |
| Direct queries plus signing requests, both bounds | exactly 122 | `xmss_sufCma_requests_exact_122` |
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
basis obligations, of which two remain: 127-bit security when only signer hashes are
additionally charged, and an attack against 128 bits when everything is charged.
The one-request chain-mutation attack now proves the unchanged direct-attack claim and the
stronger direct-plus-requests upper bound, completing exact 122-bit security for both modes.

The encoding prerequisites now include a kernel-checked exact count of admissible digests:
`11539185377238682781344003244544752`. Thus a uniform digest is accepted with probability
strictly between `2^-15` and `2^-14`. `Proof/EncodingCardinality.lean` proves the counting
recurrence; `scripts/generate_encoding_count.py` generates finite certificates whose equations
Lean checks. `Proof/EncodingProbability.lean` derives the probability bounds and the average
number of collision opportunities when a uniformly chosen signature chain is changed.
`Proof/EncodingRejectionProbability.lean` accounts for repeated randomizers and proves that
a fresh signing request in the randomized reference scheme succeeds with probability greater
than `31/32` after every supported key-generation result.
`Proof/FreshPathProbability.lean` proves the exact collision probability for a separately
addressed hash path, excluding an unchanged starting value. `Proof/Attack/PathBounds.lean`
proves that averaging these probabilities over a valid encoding's 42 chains, and allowing
signing failure, exceeds the 123-bit threshold.
`Proof/Attack/ChainMutation.lean` implements the concrete adversary and proves its
zero direct-query count, exact one-request count, transcript validity, and signature freshness
when the sampled replacement differs from the original chain value.
`Proof/Attack/ChainMutationAccounting.lean` connects this count to the statement's security
experiment: every supported execution charges exactly one in the direct-plus-requests mode.
It also identifies the counted advantage with the seeded game's success probability.
`Proof/Attack/MutationPath.lean` identifies the modified chain, leaf, and authentication-root
computation with the `40 - digit` hash path, and proves address separation and input injectivity
along that path.
`Proof/Attack/MutationPathCache.lean` proves that every path address has exactly its honest
input cached after key generation, with the honest path ending at the public-key root.
`Proof/Attack/MutationProbability.lean` obtains the exact probability that a distinct uniformly
sampled chain value reaches that root in the path experiment starting from the key-generation
cache. `Proof/Attack/MutationSigningCache.lean` proves that signing preserves every path cache
entry, identifies successful signatures with their key-generation replay, and carries the
exact root-collision probability through successful signing.
`Proof/Attack/MutationVerification.lean` removes the cached unchanged chains and encoding check
from full verification, proving the exact probability of acceptance with a changed chain value
after every successful reference signature. `Proof/Attack/MutationAverage.lean` averages over
the chosen chain and signing outcomes, proving success above `2^-123` for the reference
experiment that rejects failed signing requests. `Proof/Attack/MutationGame.lean` connects that
experiment to the adversary's logged game and proves that its full reference-scheme advantage
exceeds `2^-123`. `Proof/Direct/SeedGuessingZero.lean` proves exact seeded-to-table game
equivalence for adversaries making no direct hash queries. `Proof/Attack/ChainMutationSeeded.lean`
uses the attack's single request to eliminate memoization, transfers its advantage exactly to
the seeded scheme, and proves the attack claims with the already verified one-query budget.

For the remaining attack against 128 bits, `Proof/Attack/EncodingNeighbors.lean` proves that
every valid encoding has at least 392 distinct valid neighboring digests obtained by decreasing
one digit and increasing another. The encoding-search and predecessor-search attack still
needs its final verification and total-budget proofs. `Proof/Attack/HashSearch.lean` provides
a bounded search with exact fresh-input failure probability and guaranteed cached-hit success.
`Proof/Attack/NeighborSearch.lean` proves that, after signing, searching `2^121` distinct
randomizers for a different message finds a neighboring encoding with probability greater
than `3/4`, using at most `2^121` hash queries. `Proof/Attack/PreimageSearch.lean` chooses
a uniform four-bit prefix and searches its `2^124` candidate predecessors. When the cache
contains exactly the genuine predecessor at the chosen address, it proves an exact failure
probability of `(15/16) * (1 - 2^-128)^(2^124)` and success at least `2/17`.
`Proof/Attack/NeighborPreimageCache.lean` proves that signing and the encoding search preserve
every chain address, carrying this predecessor-success bound to every supported encoding-search
outcome after a successful reference signature. `Proof/Attack/NeighborVerification.lean`
proves that the single forward chain query returns the required increased-chain value and
that combining it with a successful cached predecessor gives a deterministically accepted
signature for the neighboring encoding. `Proof/Attack/NeighborExperiment.lean` combines
signing, both searches, signature construction, and full verification. After every supported
reference key generation, this experiment succeeds with probability at least
`(31/32) * (3/4) * (2/17)`, which is strictly greater than `5/64`.
`Proof/Attack/NeighborAdversary.lean` implements the concrete one-request adversary and proves
its direct hash-query bound of `2^124 + 2^121 + 2`, as well as the absence of queries to
seed-derivation domains. `Proof/Attack/NeighborGame.lean` connects its logged execution to
the experiment, proves transcript freshness, and establishes reference-game advantage greater
than `5/64`. Transfer to the seeded security game and the total charged budget remain open.

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
