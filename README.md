# Security of XMSS in the random-oracle model, in Lean 4

Machine-checked security statements and proofs for a concrete XMSS family with 128-bit hashes,
32 Merkle levels, and four-bit Winternitz digits, in Lean 4 using [VCVio](https://github.com/Verified-zkEVM/VCVio), with
two one-time signatures: WOTS with a target-sum encoding, and WOTS with a
checksum, as in SLH-DSA (FIPS 205). The development started from the 127-bit SUF-CMA proof in
[leanEthereum/leanVM](https://github.com/leanEthereum/leanVM/tree/main/formal/xmss) and
separates *what is claimed* from *why it holds*.

The library gives security proofs and attacks less than one bit apart for both schemes in
**all 16 counting modes that charge the adversary's own hash queries**, under both strong
(SUF-CMA) and standard (EUF-CMA) unforgeability. All 64 combinations have exact integer
classifications. The public theorems are in
`XmssSecurity/Statement/StrongUnforgeabilityTheorems.lean` and
`XmssSecurity/Statement/UnforgeabilityTheorems.lean`. As in the manuscript, the signing oracle
records the first request and answer at each epoch, even if signing fails; later requests at that
epoch return `⊥` without running the signer or changing the record. A standard forgery must use
an epoch/message pair absent from that record. Private uniform sampling is free: only hash calls,
and signing requests where the mode says so, are charged.

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

Every entry is an exact integer level: `b` bits hold and `b + 1` bits do not. In the checksum
mode charging both signer hashes and signing requests, the tighter bounds are 124 bits of
security and an attack below `log₂(3 · 2^128 / 32) ≈ 124.5850` bits: a gap below 0.585 bits.
The checksum `_exact` theorems cover every mode; `_signerRequests_bounds` records this tighter gap.

## The two schemes

Every scheme hash input starts with the 9-byte tweak `enc(t, p, j) = t ∥ LE32(p) ∥ LE32(j)`,
where `t` is a one-byte type tag and `p`, `j` are 32-bit little-endian integers. The public
parameter is derived as `P = H(enc(5, 0, 0) ∥ seed)`. All other scheme hash inputs place the
16-byte public parameter between the tweak and the payload. No padding is used.

The construction (`Statement/Scheme/Construction.lean`, `Xmss.lean`) is generic in the WOTS
encoding (`WotsEncoding`: the number of chains, the partial decoder from 128-bit digests to
codewords, and the number of randomizer trials of the signer). The two encodings are:

* `xmssTargetSum` (`Statement/Scheme/TargetSum.lean`): a digest is read as `v = 32` digits of
  `w = 4` bits and decodes when the digits sum to `T = 330`. All 128 bits are used.
  The signer tries up to `2^32` randomizers, each costing two hash calls, until a digest decodes.
* `xmssChecksum` (`Statement/Scheme/Checksum.lean`): a digest is read as `len_1 = 32` digits of
  `w = 4` bits, followed by the `len_2 = 3` base-16 digits of the checksum `Σ (15 - x_i)`, for
  `v = 35` chains. Every digest encodes, so the signer makes a single attempt and costs two hash
  calls (the randomizer and the encoding).

The secret key contains the seed, public parameter, chain starts, and finite vectors of all
chain values and Merkle nodes. Key generation fills these vectors from its recorded hash answers
before returning. Signing reads the stored digests by index; it does not replay chains or trees.
Materializing the vectors makes no additional oracle queries.

The levels differ in two places. With the checksum, the signer is cheap, so charging it does not
make the 122-bit attack (replace one chain value of a signature by a random value) expensive:
the attack costs `2` or `3`. The two modes have exact integer levels 123 and 124. With the target sum, a standard
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
signing. Keeping these branch probabilities in the bound gives exactly `48 / 2^128`, including
the seed-reduction loss (`Proof/Checksum/NoSign/ExactThreeBudget.lean`). On signed executions,
reusing the encoding costs at most the 48-query deciding path; a fresh encoding uses the first
differing four-bit message digit and a bound on the average remaining path. Unsigned executions
leave enough slack to absorb seed guessing.

## Correctness

`Statement/Security/Correctness.lean` defines the correctness experiment of the manuscript: the
adversary adaptively requests signatures, and the experiment outputs `1` if a first request at an
epoch fails or returns a signature that does not verify. Repeated epochs return `⊥` without
setting the failure flag. The correctness error is at most `δ` if every adversary making at most
`q` signing requests outputs
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

* `Statement/`: definitions and eight main theorems. To review the claims, start with
  `BitSecurity.lean`, then `Security/` for the games, `Scheme/` for the construction, and
  `*Theorems.lean` for the results. Only the theorem files import the proof layer.
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
| `xmssChecksum_sufCma_signerRequests_bounds`, `xmssChecksum_eufCma_signerRequests_bounds` | The two unforgeability theorem files |
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
files, so the classifications, the sub-bit bounds, their matching attacks, and the correctness theorems
are checked in the same build.
To check that the statement layer imports the proof layer only through the theorem files, run
`scripts/check_statement_imports.sh`.

The main theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The theorem files check this with `#guard_msgs`, so the build fails if a `sorry`
or a nonstandard axiom enters.
