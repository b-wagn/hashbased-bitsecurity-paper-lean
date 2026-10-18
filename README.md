# Security of XMSS in the random-oracle model, in Lean 4

Machine-checked security statements and proofs for the XMSS instance of Ethereum's
post-quantum consensus, in Lean 4 using [VCVio](https://github.com/Verified-zkEVM/VCVio), with
two one-time signatures: WOTS with the target-sum encoding of the instance, and WOTS with a
checksum, as in SLH-DSA (FIPS 205). The development started from the 127-bit SUF-CMA proof in
[leanEthereum/leanVM](https://github.com/leanEthereum/leanVM/tree/main/formal/xmss) and
separates *what is claimed* from *why it holds*.

The library proves the exact classical bit security of both schemes for **all 16 counting modes
that charge the adversary's own hash queries**, under both strong (SUF-CMA) and standard
(EUF-CMA) unforgeability. Each classification is one theorem, in
`XmssSecurity/Statement/StrongUnforgeabilityTheorems.lean` and
`XmssSecurity/Statement/UnforgeabilityTheorems.lean`. As in the manuscript, the signing oracle
answers a request for an epoch it already signed by `⊥`, without running the signer. A standard
forgery must use an epoch/message pair never requested from the signer, including requests that
returned no signature. Private uniform sampling is free: only hash calls, and signing requests
where the mode says so, are charged.

As in the manuscript, each notion has a single experiment that outputs whether the adversary
wins together with five query counts: the adversary's signing queries `q_S` and direct hash
queries `q_H`, and the hash queries of key generation `q_Gen`, of the signer `q_Sig`, and of the
final verification `q_Ver`. A counting mode `Z` is a set of these kinds, and bit security in mode
`Z` measures the adversary's work as the sum of the counts in `Z`. In Lean the kinds are
`SUFCMA.QueryKind.sign`, `.hash`, `.keygen`, `.signer`, and `.verifier`. The theorems cover the
sixteen modes with `q_H ∈ Z`.

| Counting mode `Z` (with `q_H ∈ Z`) | SUF-CMA, target sum | EUF-CMA, target sum | SUF-CMA, checksum | EUF-CMA, checksum |
|---|---|---|---|---|
| `{q_H}` | 122 | 126 | 122 | 122 |
| `{q_H, q_S}` | 122 | 127 | 122 | 122 |
| `{q_H, q_Sig}` | 127 | 127 | 123 | 123 |
| `{q_H, q_S, q_Sig}` | 127 | 127 | 124 | 124 |
| `Z` contains `q_Gen` or `q_Ver` (12 modes) | 127 | 127 | 127 | 127 |

Every entry is an exact level: `b` bits hold and `b + 1` bits do not.

## The two schemes

The construction (`Statement/Scheme/Construction.lean`, `Xmss.lean`) is generic in the WOTS
encoding (`WotsEncoding`: the number of chains, the partial decoder from 128-bit digests to
codewords, and the number of randomizer trials of the signer). The two encodings are:

* `xmssTargetSum` (`Statement/Scheme/TargetSum.lean`): a digest is read as `v = 42` digits of
  `w = 3` bits and decodes when its two padding bits are clear and the digits sum to `T = 195`.
  The signer tries up to `2^32` randomizers, each costing two hash calls, until a digest decodes.
* `xmssChecksum` (`Statement/Scheme/Checksum.lean`): a digest is read as `len_1 = 43` digits of
  `w = 3` bits, followed by the `len_2 = 3` base-8 digits of the checksum `Σ (7 - x_i)`, for
  `v = 46` chains. Every digest encodes, so the signer makes a single attempt and costs two hash
  calls (the randomizer and the encoding).

The levels differ in two places. With the checksum, the signer is cheap, so charging it does not
make the 122-bit attack (replace one chain value of a signature by a random value) expensive:
the attack costs `2` or `3` and the levels are 123 and 124. With the target sum, a standard
forgery needs a fresh digest that decodes, which costs the adversary a hash query or a lucky
verification, hence 126 and 127; with the checksum, a signature for one message already answers
half of a forgery for any other message, and the standard levels equal the strong ones.

Randomizers have 128 bits. With the target sum, the signer may accept a randomizer whose
encoding hash the adversary queried before the signing request. Such a signature helps a forgery
only together with a second input of the same epoch whose digest is the same, so the loss is at
most `(q + 2^86) / 2^256` per expected direct encoding query of an adversary making at most
`q < 2^127` of them (`Proof/TargetSum/Direct/CollisionLoss.lean`).

Small budgets in the signer modes of the checksum scheme, where the adversary can afford at most
one signature, use a separate argument (`Proof/Checksum/NoSign/`): an adversary that does not
sign must forge the honest top sibling of the Merkle tree, which it never sees, or make a fresh
top query collide with the root, so it wins with probability at most
`(2q + 2) / 2^128 + q / 2^256` (the last term covers guessing the master seed). With the signer
and the requests charged and `q = 3`, the adversary signs once without hashing or hashes without
signing; the two cases are weighted by the probability of signing, for at most
`45 / 2^128 + 3 / 2^256`.

## Correctness

`Statement/Security/Correctness.lean` defines the correctness experiment of the manuscript: the
adversary adaptively requests signatures, a repeated epoch is answered by `⊥`, and the experiment
outputs `1` if a request is answered by `⊥` or by a signature that does not verify. The
correctness error is at most `δ` if every adversary making at most `q` signing requests outputs
`1` with probability at most `δ · q`; its hash queries are not limited.

`xmssChecksum_correct` (`Statement/CorrectnessTheorems.lean`) proves that the checksum scheme has
correctness error `0`. `xmssTargetSum_correct` proves that the target-sum scheme has correctness
error at most `2^-64864`. With the target sum, a signature that the signer returns verifies, and
signing fails when all `2^32` randomizers give digests that do not decode. The adversary's hash
queries are unlimited, so it may learn the master seed and search for a bad message. The proof
therefore fixes a public parameter, master seed, epoch, and message, and bounds the probability
that the final oracle answers show all trials of that request failing by
`(1 - p + 2^32 / 2^128)^(2^32) ≤ 2^-(2^16)`, where `p > 2^-15` is the probability that a uniform
digest decodes (`Proof/TargetSum/SigningFailure.lean`). A union bound over the `2^672` such
tuples gives the bound (`Proof/TargetSum/CorrectnessError.lean`).

## Layout

* `Statement/`: the definitions (security games, bit security, the scheme) and the four theorem
  statements. Only the theorem files import the proof layer.
* `Proof/Common/`: proofs that do not depend on the scheme (counting modes, query counting). The
  proofs were written for a variant of the games in which a repeated epoch makes the forgery lose
  (`LossyGames.lean`); `RepeatedEpochs.lean` transfers them to the statement's games: an
  adversary that answers its own repeated requests by `⊥` wins the variant with the same
  probability and is charged no more, and every attack makes a single signing request.
* `Proof/Generic/`: the proofs that hold for any WOTS code with the properties of the class
  `Code` (`Proof/Generic/Code.lean`): a decoder that is injective where it decodes, codewords that
  do not dominate one another, and bounds on the chain counts and signer trials. They work with a
  copy of the construction for the code (`Scheme/`), and `Scheme/Bridge.lean` proves that the copy
  is the statement's construction for the encoding of the code.
* `Proof/TargetSum/` and `Proof/Checksum/`: the instance of `Code` for each encoding (`Code.lean`),
  and what depends on the encoding: the encoding's counting and probability facts, the attacks,
  the numerical bounds, and the assembly of the classifications (`Main/`).

*Disclaimer.* The Lean code proves statements about the scheme as defined in `Statement/Scheme/`,
with the hash function modelled as a random oracle. It does not prove security of any
implementation and cannot replace an audit.

## Theorems

| Theorem | File |
|---|---|
| `xmssTargetSum_sufCma_exact`, `xmssChecksum_sufCma_exact` | `Statement/StrongUnforgeabilityTheorems.lean` |
| `xmssTargetSum_eufCma_exact`, `xmssChecksum_eufCma_exact` | `Statement/UnforgeabilityTheorems.lean` |
| `xmssTargetSum_correct`, `xmssChecksum_correct` | `Statement/CorrectnessTheorems.lean` |

The adversary is probabilistic, adaptive, and unbounded in time and memory. Each counting mode
specifies which hash queries and signing queries count as the adversary's work. The probability is over the
master seed, the random oracle, and the adversary's private randomness.

## Building

```
lake exe cache get   # Mathlib cache
lake build          # strong and standard security proofs, attacks, and axiom guards
```

Toolchain: Lean `v4.31.0`; VCVio pinned to `cbd4144` in `lakefile.toml`.

`lake build` builds the single `XmssSecurity` library. Its root module imports the three theorem
files, so the four classifications, including the matching attacks, and the correctness theorems
are checked in the same build.
To check that the statement layer imports the proof layer only through the theorem files, run
`scripts/check_statement_imports.sh`.

The main theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The theorem files check this with `#guard_msgs`, so the build fails if a `sorry`
or a nonstandard axiom enters.
