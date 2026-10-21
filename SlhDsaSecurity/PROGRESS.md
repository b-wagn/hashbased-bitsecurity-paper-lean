# SLH-DSA-128s: proof status

**Concrete construction and experiment. The 127-bit security theorem is not established.**

The experiment is deterministic, pure SLH-DSA-128s with at most
2^64 signing requests. Work counts direct adversary hash calls and every hash
call in final verification, including repeated inputs. Honest key generation
and signing share the same oracle but contribute no work. The target is
SUF-CMA advantage at most q/2^127 for every almost-sure work budget q ≥ 1;
`Proof/Security.lean` proves that any SUF-CMA bound implies the same EUF-CMA bound.

## Source audit

- [FIPS 205](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.205.pdf),
  Table 2: n=16, h=63, d=7, h'=9, a=12, k=14, lg(w)=4, m=30.
  Algorithms 7–8 use 32 message digits and three checksum digits, most
  significant first. Algorithm 18 computes only the top XMSS tree.
- [leanVM at 3a37fb6](https://github.com/leanEthereum/leanVM/tree/3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45/formal/lean_sphincs):
  `Sphincs/StatementDet.lean` uses `Statement.countedOracle`, which charges
  **all** hashes. `Scheme.lean` fixes one height-26 tree, 256-bit seeds,
  target-sum WOTS, and a custom forest. `Lifetimes.requestedSecurity` is not
  a theorem about standard SLH-DSA. `BridgeHeavyCert.det_bitsFH` explicitly
  subtracts `keygenCost` from q; its certificates include that credit.
- The existing XMSS `Proof/Checksum/Modes/Verifier.lean` supplies a useful
  accounting pattern: reserve the final verifier's work and prune the
  adversary's direct-query budget. Its cryptographic bound does not cover
  FORS, a hypertree, or the standard 128-bit seeds.

## Model decisions and outstanding obligations

Start with the SHAKE byte formats in FIPS 205 Section 11.1, idealizing SHAKE
as one consistent random oracle. A 30-byte output suffices for all scheme
calls; 16-byte outputs must be prefixes of that same answer. One oracle
call is one unit, independent of input length. This is an ideal-hash claim,
not a concrete SHAKE or SHA2 security proof.

Preserve the 32-byte addresses, both independent 16-byte secret seeds,
public seed, message processing, and all nine unused bits in the 30-byte
message-digest layout. The PRF address types distinguish WOTS and FORS
derivation. Message randomization and message hashing use their specified
byte concatenations; they cannot be replaced by independently tagged oracles
without a proof that accounts for overlaps.

The security argument still needs a joint adaptive bound for seed guesses,
FORS disclosures and reuse, digest prequeries selected by subsequent signing,
WOTS/hypertree modifications, and the final verification. A fixed, independent
FORS target calculation cannot discharge these obligations. No component
security hypothesis or numerical security certificate has been assumed.

`Proof/Parameters.lean` checks the standard dimensions and signature length.
`Proof/Checksum.lean` proves the WOTS chain-step range 45–510, including both
endpoints. `Proof/VerificationQueries.lean` connects this arithmetic to every
verifier trace: WOTS verification uses 46–511 calls, FORS uses exactly 183,
and a parsed signature with a valid message frame uses 569–3824 calls.
These bounds survive any stateful oracle implementation and initial cache;
repeated inputs are charged. `Proof/{VerifierNaturality,VerificationBudget}.lean`
connects them to the experiment's actual `Outcome.counts`: every accepted outcome
has work at least 569, and either forgery advantage is zero for q < 569.
`Proof/ChecksumAntichain.lean` proves that every different WOTS message requires
an earlier value on at least one chain; advancing all chains cannot change the
message.
All existing XMSS definitions and proofs are unchanged.

`Statement/{Types,Address,Hashing}.lean` now defines the standard key fields,
32-byte addresses, SHAKE input concatenations, shared 30-byte oracle, short-output
truncation, and pure-message framing. `Proof/Hashing.lean` proves injectivity of
the byte serialization, addresses, each hash-input format, and successful framing.
Different structural address types give different inputs. The exact overlap
between message hashing and message randomization is also proved; it is not an
attack or a claim that the security target is impossible.

`Statement/{Wots,Merkle,Fors,Hypertree,Scheme}.lean` defines the complete
deterministic algorithms, including on-demand secret derivation and key generation
of only the top tree. `Statement/Signature.lean` supplies the standard byte layout
and decoder. `Statement/Security.lean` defines the adaptive experiment and the
exact target proposition `HasSecurityBits .strong 127`. Every request counts,
including repetitions and rejected contexts; honest hashes are uncharged and
every direct or final-verifier hash call is charged. The lifetime and work bounds
hold jointly with probability one. `Proof/{Signature,SignatureCanonical}.lean`
proves both codec roundtrips, including that every accepted byte string is the
canonical encoding of its parsed value. `Proof/Correctness/` proves correctness
of WOTS, each FORS tree, XMSS authentication paths, all seven hypertree layers,
and the complete byte-facing scheme for every fixed hash function and all seeds.
`Proof/Correctness/SharedROM.lean` then proves the honest keygen/sign/verify roundtrip
with actual private seed sampling and one shared cache, from every starting cache.
Valid contexts accept with probability one; invalid contexts return `none`.
This is per-request correctness, not an adaptive security theorem.

`Proof/ROMPresampling.lean` proves that unobserved adaptive oracle work before
the actual security game preserves its entire outcome distribution, including
the instrumented counters. The original almost-sure budget therefore holds
from every cache supported by that preparation. It does not transfer that budget
to arbitrary hybrid caches.

`Proof/CanonicalGraph/` represents the standard structural computations by a
finite graph with strictly decreasing child ranks and injective addresses.
Its evaluated cells are the actual WOTS, FORS and Merkle values. A parser using
only public inputs identifies the parent and proposed child values, and all
graph addresses satisfy the proved separation bounds.
`Proof/GraphFreshSampling.lean` and `CanonicalGraph/Programming.lean` prove the
exact law of computing this graph in the shared oracle: independent uniform
128-bit cells, including the secret seed, and independent 112-bit suffixes,
with the corresponding byte-input cache. This preserves full 240-bit answers.

`Proof/Extraction/` proves deterministic collision extraction from WOTS and
XMSS verification. Recovering the genuine public key with changed signature
values gives a collision at a specific chain, compression, or authentication
path call. `Proof/Extraction/Fors.lean` adds the FORS half: recovering a single
FORS tree root gives either the canonical secret leaf and twelve siblings or a
path collision, and recovering the FORS public key gives either every canonical
tree root or a root-compression collision. `Proof/Extraction/Hypertree.lean`
composes the Merkle and WOTS extractions into one layer step: a forged XMSS
layer recovering the canonical subtree root either equals, for its incoming
message, the canonical WOTS signature and all nine authentication siblings, or
collides at a layer hash call. Chaining the seven layers top-down threads each
recovered root as the next layer's WOTS message; the canonical branch only forces
`xsig.wots = Wots.sign message`, so propagating canonicity to the layer below
additionally requires the checksum-antichain WOTS preimage argument
(`Proof/ChecksumAntichain.lean`) and its ROM probability charge. These witnesses
still need the joint adaptive probability argument.

`Proof/Extraction/WotsPreimage.lean` supplies that transition witness: `chain_le`
composes two chain segments, and `exists_preimage_witness` shows that when a
layer's canonical branch forces `sig.wots = Wots.sign forged` for a message
differing from the honestly signed one, the checksum antichain produces a chain
on which the forged value is a strict chain-ancestor (preimage) of the honestly
revealed value. Its probability is charged separately in the ROM; no one-wayness
is assumed.

Seven-layer chaining (the structural capstone, not yet in Lean) is a reverse
induction on `Hypertree.rootFromSignature`'s `remaining` argument. The recursion
peels the bottom layer first and threads each recovered root up as the next
layer's WOTS message, but a layer's recovered root is message-dependent, so only
the top layer's output is pinned (to `pk.root`). The induction therefore carries
an explicit honest-input parameter `expectedInput`: the recursive (upper) call is
given `expectedInput := Merkle.node secretSeed publicSeed (address layer tree)
subtreeHeight 0`, the honest output of the layer just processed. The induction
hypothesis, applied to the upper segment with output `pk.root`, yields either a
fault in the upper layers or `root₀ = expectedInput = honestNode(layer)`; the
latter lets `Extraction.Hypertree.layer_canonical_or_collision` fire at the bottom
layer, giving a collision or `sig₀.wots = Wots.sign message`. Comparing `message`
to `expectedInput` then gives either `message = expectedInput` or, via
`WotsPreimage.exists_preimage_witness`, a WOTS preimage discrepancy at this layer.
The base case `remaining = 0` returns the threaded message and closes against the
hypothesis `pk.root = Merkle.node secretSeed publicSeed (address (layers - 1) 0)
subtreeHeight 0` (honest keygen root). Threaded to the bottom, the fault-free
branch forces the layer-0 message — the recovered FORS public key — to equal the
honest FORS public key at the digest's `(tree, leaf)`, handing the FORS coverage
argument its input. Each fault is a concrete, position-tagged collision or
preimage witness whose ROM probability is charged in the adaptive assembly.

## FORS components

`Proof/ForsCoverage.lean` proves the exact coverage probability of an independent
uniform target. If `s_i` bounds the number of disclosures at instance i, the
probability is at most `sum_i s_i^14 / 2^231`. In particular, the deterministic
condition `sum_i s_i^14 <= 2^103` suffices for a bound of 2^-128. This result
does not assert that an adaptive signing transcript satisfies the condition.

`Statement/MessageDigest.lean` implements the standard 21/7/2-byte split.
`Proof/MessageDigest.lean` proves joint uniformity of its 63-bit instance and
fourteen 12-bit FORS indices when the full 240-bit answer is fresh and uniform.
The proof retains the nine ignored bits to obtain a bijection; they have not
been removed from the hash output. `fresh_digest_coverage` connects this parser
to the exact coverage count. Freshness of an adaptively selected input remains
a separate obligation.

`Proof/ForsMoments.lean` checks Touchard-polynomial values through degree 84.
`Proof/ForsConcentrationPoisson.lean` identifies them with moments of the actual
Poisson measure and proves integrability and centered moments. Using the exact
sixth moment of a sum of independent variables, `Proof/ForsConcentration.lean`
proves that 2^63 independent Poisson(3) loads satisfy
`Pr[sum_i load_i^14 >= 2^103] <= 2^-142`.

`Proof/ForsConcentrationOccupancy.lean` proves the exact multinomial occupancy
law and its Poisson mixture, preserving the dependencies between bins. Monotonicity
and a second-moment bound transfer the Poisson result to every fixed N ≤ 2^64
independent uniform instance selections:
`Pr[sum_i load_i^14 > 2^103] <= 2^-141`.
`Proof/ForsConcentrationExtended.lean` proves the same tail up to 5·2^62 draws,
allowing room for additional independent digest queries in a future reduction.
The adaptive signing transcript remains a separate argument.

`Proof/ForsAdaptiveTargets.lean` proves a bound for adaptive selection from an
independent target tape. Decisions may depend on earlier targets and an arbitrary
fixed full disclosure tape, including future disclosures. The bound charges the
expected number of selected targets, plus one bad-load probability. This handles
random allocation among query roles within that experiment; coupling the actual
shared-oracle game to these independent tapes is still unproved.

`Proof/ForsDisclosureTape.lean` defines actual disclosure sets from an independent
tape of full parsed digest views and connects their multiplicities to the proved
occupancy distribution. Its VCVio bad-load probability is at most 2^-141 for
at most 5·2^62 entries. It also supplies removal of one target coordinate without
depending on that coordinate's value.

`Proof/ForsLeaveOneOut.lean` charges adaptive target selection from that same
tape while using all other entries as disclosures, including future entries.
The bound is 2^-141 plus the expected number of selected targets divided by
2^128; independent auxiliary randomness may determine the causal policy.
`Proof/ForsConcentrationSharper.lean` additionally proves a smaller load cap:
2^102 except with probability 2^-126. It yields the alternative bound 2^-126
plus the expected number of selected targets divided by 2^129. These are
independent-tape theorems; connecting them to the actual shared ROM remains open.

`Proof/BlindKey.lean` bounds guesses against independent hidden keys and combines
their expected cost with other costs under one common transcript budget. Applying
it requires a capped simulation whose transcript is independent of those keys;
it does not identify a randomizer-key hit with a successful forgery.

Even after that step, the ROM proof must handle signing whose digest was
queried in advance, future disclosures, and overlaps between the specified
SHAKE inputs. For example, at the internal-message level, H_msg with R=SK.prf
has the same input as PRF_msg on PK.root concatenated with that message.
The pure-message encoding also matters when analyzing such overlaps.
A hybrid that simply declares these roles independent is insufficient.
`Proof/FramingOverlap.lean` proves that an overlap with an actual pure-message
randomizer call requires the public root's first byte to be zero. That restriction
has probability exactly 1/256 under actual key generation; it is only a necessary
condition for the overlap, not an attack probability or security bound.

`Proof/HashSeparation.lean` proves a separation criterion for H_msg versus
structural hashing: an overlap requires PK.seed concatenated with PK.root to
encode the structural address. A loose rectangle enclosing the standard
128s address ranges has at most 2^91 candidates, so an independently uniform
pair of 16-byte values satisfies this condition with probability at most
2^-165. `Proof/{KeygenFresh,KeygenUniform}.lean` proves that the actual top-tree
root is a fresh uniform output, and that actual key generation yields independent
uniform public seed and root. Thus the 2^-165 bound now applies directly to
key generation. The address ranges still need to be connected to all algorithm
traces. PRF_msg versus structural hashing is also proved disjoint whenever
SK.prf differs from PK.seed. These results do not resolve the remaining
H_msg/PRF_msg overlap.

`Proof/PartialDigest.lean` proves that fixing the first 128 output bits leaves
the instance and final three FORS indices jointly uniform in the remaining
112 bits. For fixed disclosures with at most L leaves per tree and a fixed set
of instances, coverage is at most `|instances| * L^3 / 2^99`; at L=256 this is
`|instances| / 2^75`. Applying it to adaptive disclosures requires a freshness
and independence argument that is not yet proved.

`Proof/ForsPrefixCapacity.lean` bounds all 120-bit FORS prefixes simultaneously.
For fixed instance assignments satisfying the load cap and iid leaf samples,
the probability that any prefix is covered at sixteen or more instances is at
most 2^-152. This controls selection of a signature body after a partially
revealed digest; its distributional hypotheses still need an adaptive-game bridge.
`Proof/ForsDisclosurePrefix.lean` proves the corresponding result for the full
uniform digest-view tape by conditioning on its instance assignments and
reindexing its leaf coordinates. For at most 5·2^62 entries, the exceptional
probability is at most 2^-141 + 2^-152.
