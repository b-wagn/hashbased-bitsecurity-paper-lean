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

`Proof/Extraction/HypertreeChain.lean` now carries out the seven-layer chaining.
`rootFromSignature_fault_or_canonical` is the reverse induction below;
`verify_fault_or_fors_canonical` specialises it to the actual honest-key verifier:
a forged hypertree signature accepted against an honestly generated key either
contains a concrete structural fault at some layer (a `LayerCollision`, or a WOTS
signature on a message differing from the honest threaded input, which yields a
chain preimage witness) or its recovered FORS public key equals the honest FORS
public key fed into the hypertree. `honestFold_eq` discharges the honest fold to
the keygen root. Only the ROM probability charge for each concrete fault remains.

The reverse induction on `Hypertree.rootFromSignature`'s `remaining` argument. The recursion
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

## Tightness budget for the 127-bit target

Write the target as `q / 2 ^ 127 = 4q / 2 ^ 129`. The two unavoidable attack avenues are
additive, and their sum decides whether the target is provable at all.

* Structural faults. `Proof/FreshHitBound.lean` charges every extracted collision or
  preimage witness at `q / 2 ^ 128 = 2q / 2 ^ 129`, and that charge is *tight*: a fresh
  tweakable call hits a value fixed before it with probability exactly `2 ^ -128`
  (`CollisionCharge.fresh_tweakable_prob_hit`).
* FORS coverage. The plain bound `Proof/ForsCoverage.lean` gives `2 ^ -128` per fresh
  digest, i.e. `2q / 2 ^ 129`. Added to the structural charge this is `4q / 2 ^ 129`,
  exactly the target, leaving **no** room for any further term. The target is therefore
  **not provable through the plain FORS bound**.
* `Proof/ForsConcentrationSharper.lean` is what creates the slack: the smaller load cap
  `2 ^ 102` gives `q / 2 ^ 129` plus an additive `2 ^ -126 = 8 / 2 ^ 129`. The provable sum
  becomes `3q / 2 ^ 129 + 8 / 2 ^ 129`, leaving slack `(q - 8) / 2 ^ 129`.

So the proof **must** route FORS through the sharper cap, and the remaining slack
`(q - 8) / 2 ^ 129` must absorb every other term:

| `q` | slack `(q - 8) / 2 ^ 129` |
| --- | --- |
| 569 | `2 ^ -119.9` |
| `2 ^ 20` | `2 ^ -109` |
| `2 ^ 57` | `2 ^ -72` |
| `2 ^ 64` | `2 ^ -65` |
| `2 ^ 81` | `2 ^ -48` |

The additive constant `2 ^ -126` is harmless only because `Proof/VerificationBudget.lean`
forces the advantage to zero for `q < 569`, so `q ≥ 569 > 8` always. The other recorded
constants (`2 ^ -141` occupancy, `2 ^ -152` prefix, `2 ^ -165` hash separation) sit far
below the slack at every `q ≥ 569`.

The one term that is *not* obviously below the slack is the shared-oracle framing leak now
proved in `Proof/FramingLeak.lean`. Its success is driven by **free** signing queries
rather than by `q`: with probability `1/256` the public root starts with a zero byte, the
`chainFrame` family becomes legal, and up to `2 ^ 64` uncharged signing requests each
publish a randomizer that is a truncated message digest for the next message down. The
calculation modelled in `Proof/SharedOracleArithmetic.lean` adds roughly `2 ^ -72` on top
of the generic baseline. Because the slack reaches `2 ^ -72` only at `q = 2 ^ 57`, the
target survives this path **only if** mounting it genuinely costs that many charged
queries. It appears to: recovering `SK.prf` requires recognising which of the roughly
`2 ^ 64` published randomizers equals it, and each candidate test is at least one charged
hash call, so about `2 ^ 64` charged queries are needed, where the slack is `2 ^ -65` —
roughly seven bits of margin. Closing this rigorously means proving a *charged-work lower
bound* for the recovery step, not just its success probability. That is the remaining
quantitative obligation, and `proposed_bound_exceeds_target` is a certificate about the
proposed calculation, not a proof that any adversary achieves it.

Summary: 127 bits is not refuted and appears attainable, but only via the sharper FORS cap,
the 569-query verification floor, and a charged-work lower bound on the framing-leak
recovery. Routing FORS through the plain `2 ^ -128` bound cannot work.

## Remaining obligations for `HasSecurityBits .strong 127`

The structural half is complete and the per-query charge is proved and bridged to it.
Four obligations remain, in increasing order of difficulty.

1. **Counter-based charge — done.** `Proof/GrowthCharge.lean` proves `prob_hitWithin_le`:

       Pr[Hit targetOf ∧ GrowthAtMost initialCache finalCache limit] ≤ limit / 2 ^ 128

   with the budget enforced by the *event* instead of by a syntactic query bound, so the
   mismatch with `Security.HasBudget` is gone and no new instrumentation was needed. Only a
   cache miss draws fresh randomness, so only a miss can newly hit; the miss count is
   exactly the cache growth, a function of the observable final state. `cache_mono` shows
   entries are never removed or overwritten; `GrowthAtMost` states growth without a
   cardinality on the infinite input type, as a bound on duplicate-free lists of newly
   present inputs. Replays are uncharged here, which is sound for an upper bound because a
   replay cannot create a new hit, and the experiment charges them, so its budget dominates
   the growth.

   Note for whoever continues: VCVio's cost-to-query-bound bridge does **not** help here
   and should not be retried. `WorstCaseCostBound.toIsPerIndexQueryBound_unit` is stated
   only for `CostModel.unit`, which charges every query one unit, while
   `RandomOracleModel.hashCost` charges `.inl _ => 0`. An adversary may make unboundedly
   many free uniform-coin queries while keeping its hash count under `q`, so no unit-cost
   worst-case bound and no finite per-index bound for the `unifSpec` indices exist.

2. **Assembling the structural term — done.** `Proof/StructuralTerm.lean` proves
   `prob_deviatingCollision_le`: started from a cache holding only honest canonical
   queries, a charged phase produces a deviating structural collision — precisely the shape
   of every witness `Extraction.*` yields — while growing the cache by at most `limit`,
   with probability at most `limit / 2 ^ 128`. It composes
   `CanonicalTarget.clean_of_canonical_cache`,
   `CanonicalTarget.hit_of_deviating_collision` and `GrowthCharge.prob_hitWithin_le`. The
   charge is linear in the budget and independent of how many honest node values exist.

   What is still needed to use it inside the experiment: instantiate `initialCache` with
   the actual post-key-generation, post-signing cache, which means showing the honest phase
   queries only canonical inputs. `ROMPresampling` provides the phase decomposition and
   `CanonicalGraph.Correspondence` identifies the honest queries as canonical cells, so this
   is bookkeeping rather than a new idea, but it is not done.

3. **FORS coverage in the real game.** Couple the shared oracle to the independent-tape
   bounds. By the tightness budget above this *must* go through
   `ForsConcentrationSharper` (`q / 2 ^ 129 + 2 ^ -126`); the plain `2 ^ -128` coverage
   bound leaves no room and cannot close. `ROMPresampling`, `GraphFreshSampling` and
   `CanonicalGraph.Programming` are the intended machinery.
4. **Charged-work lower bound for the framing leak.** `Proof/FramingLeak.lean` shows the
   leak is real and driven by free signing queries. Since the slack `(q - 8) / 2 ^ 129`
   only reaches `2 ^ -72` at `q = 2 ^ 57`, the target survives this path only given a lower
   bound on the *charged* work needed to recover `SK.prf` from the roughly `2 ^ 64`
   published randomizers. This is a lower-bound argument about an adversary's cost, a
   different shape from every other obligation here, and it has no counterpart in the XMSS
   development.

## All-queries-counted accounting (current target)

The accounting changed: every hash call made anywhere in the game is charged — key
generation, signing, the adversary's direct calls and final verification — matching the
leanVM `lean_sphincs` statement. Signing requests are still capped separately at `2 ^ 64`,
including repetitions and failures. `Statement/Security.lean` adds `countAllHashes`,
`runAll`, `HasTotalBudget`, `totalAdvantage` and the target `HasTotalSecurityBits .strong
127`; `Proof/Security.lean` proves `totalAdvantage_eq` (the counter is bookkeeping, so
every result about `advantage` transfers) and `total_strong_implies_standard`.

**Why this accounting closes the budget, where verifier-counted did not.** Write the target
as `4q / 2 ^ 129`. The structural charge is `2q / 2 ^ 129` and tight. Routing FORS through
`ForsConcentrationSharper` gives `q / 2 ^ 129 + 2 ^ -126`, so the sum is
`3q / 2 ^ 129 + 8 / 2 ^ 129` and the target is met as soon as `q ≥ 8`. Charging the honest
work makes that automatic — key generation alone costs about `2 ^ 18` hashes — and the small
`q` regime is covered anyway by the 569-call verification floor. It also removes the
framing-leak obstruction entirely: that attack needs `2 ^ 64` signing requests, which are
now charged, forcing `q` to about `2 ^ 80`, where the slack `q / 2 ^ 129 ≈ 2 ^ -49` dwarfs
the leak's `≈ 2 ^ -72`. Under verifier-counted accounting the signing queries were free and
that slack was zero, which is exactly what made the target unreachable there.

**Done.** `Proof/WholeGameStructural.lean` proves the structural term for the entire game:
`prob_deviatingCollision_whole_game_le` bounds the probability of any deviating structural
collision by `q / 2 ^ 128`. Charging the honest work is what makes this unconditional — the
game starts from the empty cache, which is vacuously a cache of honest canonical queries, so
the honest phase needs no separate analysis. `Proof/GrowthBudget.lean` supplies the bridge
`growth_le_count` (repeats are charged but do not grow the cache, so the count dominates the
growth).

**Remaining.**
* *Counter comparison.* `counts.work ≤ total count`, and more specifically that the total
  count dominates the final verifier's calls. With it, `VerificationBudget`'s 569-call floor
  gives `totalAdvantage = 0` for `q < 569` directly. Bounded plumbing: the total counter is
  additive over the experiment's binds while `counts.verification` accumulates only in the
  verification phase.
* *FORS coverage term and the forgery decomposition.* This is unchanged by the new
  accounting and is the remaining mathematical core: couple the shared oracle to the
  independent-tape concentration bounds for the adaptively selected digest, and decompose an
  accepted forgery into a structural collision or a coverage event using the `Extraction.*`
  chain. `Proof/FreshDigest.lean` supplies the freshness half (a fresh `H_msg` call has a
  uniform parsed FORS view, and the signer's randomizer is uniform when its `PRF_msg` input
  is uncached). The adaptive, prequeried and cross-request-correlated cases remain.

## The two remaining inputs, and how `hcap` avoids a freshness argument

`Proof/Assembly.lean`'s `le_target_of_terms` reduces the 127-bit bound to three inputs. The
structural term (`WholeGameStructural`, `2q / 2 ^ 129`) and the FORS term
(`ForsCoverageTerm.prob_coverage_within_le_of_family`, `q / 2 ^ 129`) are proved. Two remain.

**`hsplit`: an accepted forgery is a structural collision or a coverage event.** Laborious
but mechanical. The chain is already proved end to end — `Extraction.Hypertree`'s layer
extraction and `HypertreeChain.verify_fault_or_fors_canonical`, then `Extraction.Fors`'s
decomposition down to `recoveredLeaf_canonical_secret_or_collision` — and
`Proof/CollisionToDeviating.lean` now supplies the byte-level bridge: a two-child structural
node's `childBytes` encoding is literally `BinaryPath.pairBytes`, so the extraction's byte
inputs and the charge's canonical inputs agree on the nose. What remains is naming the
parent node and candidate cells for each of the collision shapes, via
`CanonicalGraph.Correspondence`.

**`hcap`: the actual disclosures satisfy the load cap except with probability `2 ^ -126`.**
This needs *no freshness argument*, which is worth stating because the obvious route is both
harder and too expensive.

The tempting route is to argue that each signing request's `H_msg` input is uncached, so its
digest is fresh. That requires the adversary not to have prequeried
`SK.prf ‖ PK.seed ‖ M'`, i.e. not to have guessed `SK.prf`, costing a `BlindKey`-style
`q / 2 ^ 128 = 2q / 2 ^ 129` term. The slack after the structural and FORS terms is only
`q / 2 ^ 129`, so that route **breaks the budget**.

It is also unnecessary. The load cap depends only on the *distribution of the FORS instances*
`MessageDigest.treeIndex ++ leafIndex` of the signed digests, and a digest is a uniform
oracle answer whichever party queries its input first — a prequery by the adversary does not
bias it. So the instances are uniform regardless of freshness. What is needed instead is only
that the signed messages' digest inputs are *pairwise distinct*, which is immediate from
injectivity of `Hashing.messageInput` in its message component (`Proof/Hashing.lean`), since
distinct requests give distinct framed messages. Distinct inputs in the shared random oracle
have independent uniform answers, so the instances of the at most `2 ^ 64` distinct signed
messages are iid uniform, and `ForsConcentrationSharper` bounds the probability that
`∑ i loads i ^ 14` exceeds `2 ^ 102` by `2 ^ -126`.

Repeated requests need no separate treatment: a repeat has the same digest input, hence the
same digest and the same fourteen disclosed leaves, so it does not enlarge the disclosure
sets even though it is charged.

The remaining work for `hcap` is therefore the iid-uniformity transfer — that the answers at
the distinct signed digest inputs are jointly uniform in the actual lazily-sampled oracle,
in the form `ForsConcentrationSharper` consumes — not a freshness or key-guessing argument.

## What `hcap` actually needs: a partial-random-function invariant

`Proof/DigestInputDistinct.lean` proves what the message layer owes: distinct signing
requests have distinct `H_msg` inputs (`messageInput_ne_of_request_ne`), and the digest-input
family is byte-input separated for *every* assignment of randomizers to requests and states
(`separated_messageInput`), so the oracle-determined randomizers never have to be pinned down.

That is necessary but **not** sufficient, and it is worth recording why, because three
plausible routes all fail:

1. *The table route.* `GraphFreshSampling.evalDist_evaluate_eq_uniform_program` samples a
   complete output table `$ᵗ (Index → HashOutput)` and so requires `[Fintype Index]`. Indexing
   by `Message` is what makes `Separated` true — distinct indices *are* distinct messages — but
   `Message` contains `Bytes` and is infinite, so there is no such table. Re-indexing by
   `Fin N` instead restores finiteness but destroys `Separated`, since the adaptive choice may
   put the same message at two positions.
2. *The lazy route.* `GraphFreshSampling.evaluate_eq_sample` needs no `Fintype`, but it
   requires `FreshFor`: the starting cache must hold no entry at any digest input, for any
   state. The adversary may prequery a digest input, so this fails in the experiment.
3. *The freshness route.* Recovering `FreshFor` by arguing the adversary cannot have
   prequeried a signer's input costs a `BlindKey`-style `SK.prf` guess, `q / 2 ^ 128 =
   2q / 2 ^ 129`, which exceeds the `q / 2 ^ 129` of slack left after the structural and FORS
   terms. Even if provable it would break the budget.

The reason the obstruction is structural: with an infinite input domain there is no "sample
the whole random function in advance" computation, so the usual lazy/eager equivalence is not
available off the shelf, while the lazy formulations all want freshness at the inputs of
interest — which adaptive prequeries deny.

What is actually needed is an invariant of the lazily-built cache: *along any run started
from the empty cache, the cache is a partial uniform random function* — so that for any set
of pairwise distinct inputs, the answers recorded at them are jointly uniform regardless of
**when** each was sampled or **which party** queried it. Given that invariant, applied to the
distinct signed digest inputs supplied by `messageInput_ne_of_request_ne`, the FORS instances
are iid uniform and `ForsConcentrationSharper` bounds the load-cap failure by `2 ^ -126`,
with no freshness and no key guessing.

This invariant is the remaining content of `hcap`. It is a genuine probabilistic lemma about
the shared oracle, not an instantiation of the existing fresh-sampling results, and it is
what `ROMPresampling` would have to be extended to provide.

## A regime limit in the FORS route, and why `pinned` cannot be the signed set

The oracle-to-tape chain is complete: `GrowthCharge.cache_value_persists` and
`prob_cache_values_le` give the partial-random-function invariant,
`prob_cache_values_mem_le'` sums it over a bad set with a `Fintype` index,
`FreshDigest.viewAssignment_uniform` pushes forward to parsed views, and
`prob_view_event_le` / `prob_tape_event_le` land on a uniform
`ForsDisclosureTape.Tape pinned.card`, which is the exact form of
`bad_load_probability_sharper` and `ForsLeaveOneOut.independent_tape_coverage_le_sharper`.

Instantiating it at the experiment is **not** mere bookkeeping, for two linked reasons.

*`pinned` is fixed in advance; the signed set is adaptive.* Worse than a technicality: the
adversary can deliberately break the load cap. Prequerying digests is charged but allowed, so
it may query many messages, observe their instances, and then sign only messages sharing an
instance. Violating the `2 ^ 102` cap needs a single instance of load `157`, which takes about
`157 · 2 ^ 63 ≈ 2 ^ 70.3` digest queries to collect. So for `q` beyond roughly `2 ^ 70` the
signed-digest tape is **not** iid uniform and `Pr[cap violated]` is not `2 ^ -126`; it tends to
one. The signed set therefore cannot be used as `pinned`.

*The leave-one-out machinery avoids this by capping the full tape, which bounds `q`.*
`ForsLeaveOneOut.independent_tape_coverage_le_sharper` puts the cap on the whole iid tape and
charges the adaptive *selection* separately through the policy, which is the right structure.
But its hypothesis is `trials ≤ 5 * 2 ^ 62 = 2 ^ 64.32`, and under all-queries counting the
tape must cover every digest query, so the route needs `q ≲ 2 ^ 64.32`. Note `2 ^ 64 ≤ 5 * 2 ^ 62`,
so the signing limit alone is fine; it is the *charged* digest queries that bind.

Beyond that the cap itself fails for a structural reason, not a proof gap: with `T` digest
queries the typical potential is about `2 ^ 63 · (T / 2 ^ 63) ^ 14`, which passes `2 ^ 102`
once `T ≳ 2 ^ 65.8`.

So the current FORS route proves the bound only for `q ≤ 5 * 2 ^ 62`. The target is a
statement for **every** `q ≥ 1`, so a second argument is needed for `q > 5 * 2 ^ 62`. That
regime is not hopeless — the target `q / 2 ^ 127` is correspondingly weaker there — but it
needs a `q`-dependent load cap with a coverage coefficient adjusted to match, replacing the
fixed `2 ^ 102` / `2 ^ -129` pair. `ForsConcentrationExtended` already reaches `5 * 2 ^ 62`,
which is the present ceiling.

This is a scope limit of the plan recorded in the tightness budget above, which assumed a
fixed additive `2 ^ -126` available at every `q`.

## Correction: the adversary cannot concentrate loads without `SK.prf`

The preceding section is **wrong** where it claims the adversary can break the load cap by
prequerying digests and then signing only messages that share an instance. Signing is
deterministic: the signer uses `R = PRF_msg(SK.prf, PK.seed, M')`, so the digest input
`R ‖ PK.seed ‖ PK.root ‖ M'` of an *unsigned* message is unpredictable without `SK.prf`.
Prequerying `H_msg` at randomizers of the adversary's own choosing says nothing about which
instance the signer will land on. And once a message is signed the signature is spent, so
there is no re-rolling. The signed instances are therefore iid uniform under adaptive
selection after all, and the regime limit `q ≤ 5 * 2 ^ 62` claimed above is not real: the
tape of signed digests has at most `2 ^ 64 ≤ 5 * 2 ^ 62` entries whatever `q` is.

The concentration attack is only available to an adversary that has **learned `SK.prf`**, and
that is where the real problem is.

**An unaccounted term.** Learning `SK.prf` is a `128`-bit secret guess, and it is cheaply
verifiable: query `PRF_msg` at a guess and compare the answer with the randomizer of any
signature already held. So with `q` charged queries the probability is about `q / 2 ^ 128 =
2q / 2 ^ 129`. Conditioned on success the attack is devastating — with `SK.prf` the adversary
can steer messages to one FORS instance, and about `4096 · 2 ^ 63 ≈ 2 ^ 75` charged queries
disclose every leaf of every tree there, after which any digest landing on that instance
forges.

The tightness budget recorded earlier never charged this. Adding it:

| term | cost |
| --- | --- |
| structural (proved, tight) | `2q / 2 ^ 129` |
| FORS coverage (sharper cap) | `q / 2 ^ 129` |
| `SK.prf` guess | `2q / 2 ^ 129` |
| **sum** | **`5q / 2 ^ 129`** |
| target | `4q / 2 ^ 129` |

So the three avenues as currently bounded *exceed* the target by a factor `5/4`. This does not
refute the target — these are upper bounds and the events need not be simultaneously
achievable, so the true advantage may be smaller — but it does mean the budget does **not**
close as recorded, and that one of the three has to be sharpened, or their overlap exploited,
before the assembly can be instantiated. The `SK.prf` guess is the term to attack first, since
it is the only one not yet proved and the only one whose `2q / 2 ^ 129` coefficient looks
loose: a guess is only useful if it is *verified*, and verification needs a signature whose
randomizer is known, which may permit a sharper accounting than one guess per query.

## The decisive question: the per-query union

The two preceding sections went back and forth; this settles what the obstacle actually is.

Every avenue is a *per-charged-query* event, so the right way to budget is by rate per query,
in units of `2 ^ -129`:

| avenue | rate | effect |
| --- | --- | --- |
| `SK.seed` guess — the query's input is the true secret seed | 2 | immediate forgery |
| `SK.prf` guess — the query's input is the true PRF seed | 2 | enables load concentration |
| structural hit — the query's answer truncates to an honest cell | 2 | collision / preimage |
| FORS coverage at the sharper cap | 1 | few-time break |
| naive union | **7** | |

The target `q / 2 ^ 127` is `4q / 2 ^ 129`, i.e. rate **4**. So the naive union overshoots by
`7/4`, which is what the previous section recorded as "the budget does not close".

Two observations fix the shape of the remaining problem.

*The overshoot is an artefact of the union bound, not of the scheme.* An adversary has `q`
queries **in total** and must apportion them; it cannot spend the same query pursuing every
avenue at full rate. Putting the whole budget on the single best avenue gives `2q / 2 ^ 129`,
comfortably inside the target. So there is no attack here, and the target is not refuted.

*But the slack is genuinely thin, because the secrets alone already cost the whole budget.*
Two independent `128`-bit secrets contribute `2 + 2 = 4`, exactly the target rate. Hence a
proof of 127 bits **cannot** charge the structural and FORS terms on top of the seed guesses:
it must charge all four against one shared per-query budget, via a case analysis showing a
single query cannot profitably pursue two avenues at once — e.g. a query whose input is a
guessed secret is not simultaneously a useful structural probe.

That joint per-query accounting is the real remaining content of the proof, and it is not
something the current machinery does. `GrowthCharge.prob_badWithin_le` already charges one
shared budget for an arbitrary bad predicate, so the structural and FORS events can be merged
into a single predicate with rate `2 + 1 = 3`. What is missing is folding the two
secret-guessing events — which are conditions on a query's *input* rather than its *answer* —
into that same predicate, so that the total rate is bounded by `4` rather than `3 + 4 = 7`.

Until that is done the assembly cannot be instantiated, regardless of how much of `hsplit` and
`hcap` is finished, because `Assembly.le_target_of_terms` is fed terms that do not sum to the
target.

## The first-principles architecture (supersedes the earlier budget sections)

Several sections above record budgets that turned out to be wrong; this one supersedes them.
With every query charged, the game is a sequence of at most `q` oracle calls and the target
`q / 2 ^ 127` is a *rate* of `4 / 2 ^ 129` per call. The whole proof is therefore: bound what
one call can buy, by `4`.

**The classification.** FIPS 205 fixes a byte format per hash call, and the format decides
which avenues are live (`Proof/PerQueryBudget.lean`):

| class | format | live avenues | rate |
| --- | --- | --- | --- |
| structural | `PK.seed ‖ ADRS ‖ payload` | `SK.seed` guess `2`, structural hit `2` | `4` |
| message | `R ‖ PK.seed ‖ PK.root ‖ M`, `SK.prf ‖ PK.seed ‖ M` | coverage `1`, `SK.prf` guess `2` | `3` |

`classRate_le_target` gives `max = 4`, the target rate, where the naive sum over avenues gives
`5`. The classes are disjoint by `Proof/HashSeparation.lean`: an `H_msg` input coincides with a
structural one only if `PK.seed ‖ PK.root` encodes a valid address, probability `2 ^ -165`.

**The two halves.** Splitting by *side* rather than by avenue:

*Answer-side — proved.* `Proof/CombinedCharge.lean` charges the structural and coverage
clauses as a single predicate. Because they are exclusive by format the per-call rate is their
maximum `2 ^ -128`, not their sum, and `prob_combinedBad_within_le` charges a whole run at
`limit / 2 ^ 128 = 2 · limit / 2 ^ 129`. That is exactly half the target. The chain beneath it
is complete: `cache_value_persists` → `prob_cache_values_le` (partial random function) →
`prob_badWithin_le` (linear charge) → `CanonicalTarget` (structural targets) and
`ForsCoverageTerm` / `FreshDigest.prob_tape_event_le` (coverage, transported to a uniform
disclosure tape).

*Input-side — not proved.* The remaining `2 / 2 ^ 129` is secret guessing: a call whose input
carries `SK.seed` or `SK.prf`. This is the one avenue that is **not** an event about an
answer, so none of the charge lemmas apply — they all bound the probability that a *fresh
uniform answer* is bad, whereas here the randomness is the key sampled at key generation. The
abstract form is already available as `BlindKey.hit_probability_le`
(`guesses.length / 2 ^ 128` against an independently sampled key table). What is missing is the
coupling: the game's transcript must be shown independent of the keys up to the first hit, so
that the adversary's inputs count as blind guesses. That is a deferred-sampling argument of
the same kind as `ROMPresampling` and `CanonicalGraph.Programming.warmup_seed_uniform`, and it
is the only genuinely new machinery the proof still needs.

**Then:** `hsplit` (forgery implies a combined answer-side event or a secret hit, via the
`Extraction` chain, whose structural half is complete) and the assembly
`2q / 2 ^ 129 + 2q / 2 ^ 129 = 4q / 2 ^ 129 = q / 2 ^ 127`.

The budget closes at `4` exactly, with the `2 ^ -165` separation defect and the `2 ^ -126`
load-cap defect both far below the slack at every `q ≥ 569` — and `q ≥ 569` is automatic,
since an accepted forgery forces that many charged verifier calls.

## State of the first-principles proof

Everything below is proved, unconditionally, with no `sorry` and axiom-guarded.

| piece | lemma |
| --- | --- |
| per-query-class rates sum to the target | `PerQueryBudget.classRate_le_target`, `total_le_target` |
| answer side, structural and FORS charged as one predicate at rate `max` | `CombinedCharge.prob_combinedBad_le`, `prob_combinedBad_within_le` |
| the charge with the growth budget split by class | `ClassCharge.prob_badWithinClasses_le` |
| input side, secret guessing | `SecretGuessCharge.prob_secret_guessed_le`, `prob_run_guesses_secret_le` |
| assembly, with the defects in the message-class slack | `Assembly.le_target_of_classes` |

Underneath them: the partial-random-function invariant
(`GrowthCharge.cache_value_persists`, `prob_cache_values_le`, `prob_cache_values_mem_le'`),
the linear charge (`prob_badWithin_le`), the structural targets (`CanonicalTarget`), the
whole-game structural term (`WholeGameStructural`), the FORS transport onto a uniform
disclosure tape (`FreshDigest.prob_tape_event_le`), the counter machinery (`GrowthBudget`),
and the complete structural extraction (`Extraction.*`, through the seven-layer
`HypertreeChain`).

**What is not done** is the instantiation at the experiment. Four items, of which only the
last is more than wiring.

1. `hsplit`: an accepted forgery implies a combined answer-side event or a secret hit. The
   structural half is the `Extraction` chain, which is complete; the FORS half and the secret
   half need connecting to it.
2. Discharge `hseparated` from `HashSeparation.prob_possible_le`, and the load cap by the
   dichotomy `qm ≥ 16` (slack `2 ^ -125` covers `2 ^ -126 + 2 ^ -165`) versus `qm < 16`
   (at most fifteen disclosures, so `∑ i loads i ^ 14 ≤ 15 ^ 14 < 2 ^ 55` and the cap is
   deterministic).
3. Identify the experiment's structural- and message-class query counts with the two budgets
   of `ClassCharge.prob_badWithinClasses_le`.
4. **The until-first-hit coupling.** `SecretGuessCharge.prob_run_guesses_secret_le` needs the
   secret sampled *after* the run; the experiment samples it first. In VCVio's vocabulary the
   obligation is a `DeferredSampling.Factorizes` statement: the experiment factorizes through
   a tape in which the seed is drawn last. It is true for the usual reason — before the first
   canonical query every answer the adversary sees is a fresh uniform value, so its view is
   independent of the cells, and `CanonicalGraph.Programming.warmup_seed_uniform` already
   exhibits the seed as one coordinate of a uniform cell table — and the commuting step is
   `DeferredSampling.evalDist_bind_comm`. What is missing is the induction carrying "no hit
   yet implies the view is independent of the cells" along the adversary's execution.
   `BlindKey.hit_probability_le` is the abstract target. This is the one piece of the argument
   with no machinery behind it, and it was flagged as open in this file before any of the
   present work began.

## The coupling: machinery exists, and what it demands

The claim above that the until-first-hit coupling has "no machinery behind it" is wrong.
VCVio has `VCVio/StateSeparating/IdenticalUntilBad.lean`, whose
`QueryImpl.Stateful.advantage_le_expectedQuerySlack_plus_probEvent_bad` is exactly the
game-hop: two stateful handlers over a state `σ × Bool`, the Boolean being the bad flag,
with

    advantage ≤ expectedQuerySlack + Pr[bad fired]

under a per-step total-variation hypothesis and a query bound `IsQueryBoundP`. Taking the
blind handler for `h₁`, a `querySlack` of `2 ^ -128` and a bad flag that never fires gives
`q / 2 ^ 128` — the input-side half, exactly.

**The structural requirement is the real finding.** The per-step hypothesis is

    ∀ t s, tvDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false)) ≤ querySlack s

and it is quantified over *every* state `s`. If the secret seed lives in `s`, this is false
pointwise: for the one `t` that is the seed-derived input of that particular `s`, the real
handler returns the honest value and the blind handler returns a fresh one, so the distance
is `1`, not `2 ^ -128`. Averaging over the seed is what makes the bound true, and this
hypothesis does not average.

So the theorem applies only to handlers whose state does **not** contain the seed — the seed
must be sampled *lazily, inside the step*, at which point the step's own sampling supplies
the `2 ^ -128` honestly and the hypothesis holds as stated. The chain is therefore three
steps, not one:

1. the real experiment (seed sampled eagerly at key generation) equals the same experiment
   with the seed sampled lazily at first use — a deferred-sampling equality in the style of
   `CanonicalGraph.Programming.warmup_seed_uniform`, which already performs exactly this move
   for the warmup;
2. the lazy-seed handler and the blind handler satisfy the per-step bound at `2 ^ -128`, so
   `advantage_le_expectedQuerySlack_plus_probEvent_bad` separates them by `q / 2 ^ 128`;
3. in the blind game the seed is independent of the transcript by construction, so
   `BlindKey.mixture_hit_le_expected` with `expectedGuesses_le_of_cap` closes it.

Step 3 is done, twice. Step 2 is an application of an existing theorem once the handlers are
written. Step 1 is the one that still needs proving, and it is a narrower obligation than
"the coupling": not an induction over the adversary's execution carrying an independence
invariant, but a single commutation of one uniform sample past a computation that consumes it
only as query-input bytes.

## The input side: why the identical-until-bad route only gets halfway

`Proof/InputCoupling.lean` carries out the hop over VCVio's
`QueryImpl.Stateful.advantage_le_expectedQuerySlack_plus_probEvent_bad`, with all three of its
hypotheses proved and the bad-flag mass bounded, giving `2 q / 2 ^ 128` between a lazily-seeded
handler and a blind one. It does not finish the input side, and the reason is structural rather
than a gap in the execution.

That theorem's per-step hypothesis is quantified over *every* handler state:

    ∀ t s, tvDist ((h₀ t).run (s, false)) ((h₁ t).run (s, false)) ≤ querySlack s

A seed remembered across steps is a seed in the state, and with the seed in the state the
hypothesis is false pointwise — at the one input that is seed-derived for that `s` the two
handlers differ with distance `1`. So the only handler shape satisfying it draws a *fresh*
seed at every step. That handler is not the experiment, and the two are not identical-until-bad:
conditioned on no bad event their output laws agree, but the mass of the no-bad path does not.
With one input queried twice the eager handler misses with probability `1 - p` and the
resampling one with `(1 - p) ^ 2`.

### The route that does close it

The bound wanted is `Pr[the adversary queries a seed-derived input] ≤ q / 2 ^ 128` in the eager
game. Approximating the eager game by the resampling one is the wrong move; the right one is an
*exact* comparison against a blind game, because the event is prefix-determined.

1. **Blind game.** Answer the adversary from a cache that does not carry the honest entries at
   seed-derived keys. There the adversary's view is literally seed-independent — the honest
   results it sees are seed-independent as *computations*, which is
   `SeedDeferral.honest_result_indep_of_seed`, and its own answers are fresh — so
   `SecretGuessCharge.prob_run_guesses_secret_le` applies directly and gives `q / 2 ^ 128`.

2. **Exactness, not slack.** The real and blind games produce identical transcripts until the
   first seed-derived query. "Some query is seed-derived" is determined by the transcript up to
   that first occurrence, on which the two games agree, so the two assign it the *same*
   probability. No `ε` is lost, which is what makes this fit a budget that is met with equality.

The work this needs is an induction showing the two handlers agree on the has-a-hit-occurred bit:
at a query that is seed-derived both games register the hit whatever the answer, and at any other
query they answer identically and recurse. That is the next concrete step, and unlike the
identical-until-bad hop it does not require a per-step bound quantified over states the eager
seed makes unreachable.

## Presampling: proved for the verifier's world, blocked for the game's

`Proof/Presample.lean` establishes, over `OracleComp HashSpec`:

* `evalDist_prepend_fresh` — filling one empty cache entry with a uniform value does not change
  the law of what follows;
* `evalDist_prefill` — the same for a duplicate-free list of empty inputs;
* `evalDist_prepend_evaluate` — the same for an adaptive traversal, whose next input is chosen
  using the value just drawn. This is the form the honest parties' queries actually take, since
  a node's byte input is built from its children's cells.

With `GraphFreshSampling.evalDist_evaluate_eq_uniform_program` these fix the honest cells ahead
of the adversary, which is what every charge is parameterised by.

**They are now available in the game's oracle world too**, as
`evalDist_prepend_fresh_world`: the experiment runs in `OracleComp OracleWorld`, which is
`unifSpec + HashSpec`, and a coin flip does not touch the hash cache, so it commutes with the
prepended draw exactly as a hash query at a different input does.

Getting there cost two sessions' turns to a misdiagnosis, which is worth recording accurately
rather than as first written. The failures all mentioned a mismatch between
`OracleWorld.Range (Sum.inr t)` and `HashSpec.Range t`, and this note previously recorded that
as the obstruction — a `simp` normalisation problem between two `rfl`-equal types, to be fixed
by coercing once at a boundary. That was wrong, and type ascriptions and requantifying at each
type in turn all failed because they addressed a symptom.

The actual cause: the prepended draw puts the right-hand side under a binder, and `rw` does not
rewrite under binders. Unfolding the query step with `rw` therefore rewrote only the left-hand
side, and every later step failed on a `Range` mismatch that was really just the side that had
never been unfolded. Replacing that single `rw` with `simp only`, which does go under binders,
removed the entire difficulty; the final branch then closed by `rfl`.

The transferable lesson is not about `Range` at all: when several independent-looking failures
share a symptom, look for one upstream cause instead of fixing each occurrence.

## The coverage half of `hanswer` goes through the tape, not through `CombinedCharge`

`CombinedCharge.prob_combinedBad_within_le` charges the structural and coverage clauses as one
predicate, so their per-call rate is the maximum `2 ^ -128` rather than the sum. That was built
to keep the answer side inside half the target, and the arithmetic is right. But its
`revealed : ForsCoverage.Disclosures` is a *parameter*, fixed before the run — and in the
experiment the disclosures are not fixed. They are whatever the signing oracle reveals, on
messages the adversary chooses adaptively.

Fixing `revealed` to the run's final disclosures is sound as an over-approximation — a query
covered at the time is covered at the end — but it cannot be *applied*, because the charge
needs the parameter before the run and the final disclosures are only known after it.

The machinery for exactly this already exists and is what the coverage half should use:
`ForsLeaveOneOut.independent_tape_coverage_le_sharper` samples the whole digest tape up front,
which fixes the disclosures as a function of the tape, and lets an adaptive `Policy` select
which trial to attack. Its bound, `1 / 2 ^ 126 + expectedUses / 2 ^ 129`, is already in the
shape the budget wants: the first term is the load-cap defect that
`Assembly.cap_defect_within_slack` pays out of the message-class slack, and the second is one
unit per message-class query.

So the answer side should be assembled per class rather than as one predicate:

* structural clause, rate `2`, on structural-class queries — `ClassCharge` / `ClassBudget` with
  `WholeGameStructural.prob_deviatingCollision_whole_game_le`;
* coverage clause, rate `1`, on message-class queries — the tape.

The two clauses live on disjoint query classes, so no query pays both, which is what made the
maximum-rather-than-sum argument work in the first place. `CombinedCharge` reaches the same
rate by a different route; it is not wrong, it is just not instantiable at an adaptive
disclosure set.

## One weighted counter, not two class counters

`ClassCharge.prob_badWithinClasses_le` bounds the bad event by
`insideLimit * insideRate + outsideLimit * outsideRate`, with both limits *fixed numbers*.
Supplying them from the game does not work, and the reason is worth stating because it is not
a plumbing problem.

The class counts are run-dependent. Fixing both at `q` gives `2q + q = 3q` units, over the
answer side's allowance of `2q`. Taking the actual counts is not allowed, since the limits must
be chosen before the run. Splitting the probability over the possible message count `m` and
using limits `(m, q - m)` does not help either: the charge bounds the *whole* probability at
each `m`, not the probability conditioned on it, so the sum over `m` diverges.

What the game can offer is a single number. Give each charged miss its own weight — `2` for a
structural-class input, `1` for a message-class input — and charge a single weighted budget at
the uniform rate `2 ^ -129`. Then the answer side is `weighted / 2 ^ 129`, and with
`qs + qm ≤ q` the weighted count is `2 qs + qm ≤ 2q - qm`.

The useful part is that the load-cap dichotomy then falls out of *that one counter*, with no
second instrumentation. Writing `total` for the plain hash count,

    2 · total − weighted = qm      exactly,

so `qm ≤ 2q − weighted` whenever `total ≤ q`. Hence:

* `weighted > 2q − 16` forces `qm < 16`, and below sixteen disclosures the load cap holds
  deterministically (`ForsCoverageTerm.moment_le_of_few_digests`) — no defect to pay;
* `weighted ≤ 2q − 16` leaves `16 / 2 ^ 129 = 2 ^ -125` of room, which covers the `2 ^ -126`
  defect with a factor of two to spare.

Either way the answer side, defect included, stays within `q / 2 ^ 128`.

So what to build is a *weighted* growth charge — `prob_badWithin_le` with a per-input weight
and one budget, generalising both it and `prob_badWithinClasses_le` — together with the
corresponding weighted instrumentation of the game. That is one induction, not two counters.

## What `hinput` still needs: one instrumentation carrying the queried set

Both halves of the input side are proved, and so is the hypothesis joining them:

* `BlindComparison.prob_touched_eq` — two caches agreeing off `S` touch `S` with exactly the
  same probability;
* `BlindComparison.agreeOff_seedInputs` — the programmed cache and the blind one (programming
  every node but the seed-bearing `wotsPrf` and `forsPrf`) agree off the seed-bearing inputs;
* `SeedDeferral.prob_run_meets_honest_key_le` — a seed-independent run meets a seed-derived key
  at most once per query.

They do not yet compose, and the obstacle is an instrumentation mismatch rather than a missing
argument. `prob_touched_eq` is stated over `BlindComparison.tagged`, which carries a Boolean
flag; `prob_run_meets_honest_key_le` consumes a `Finset Bytes` of queried inputs. The flag is a
function of that set — it is set exactly when the set meets `S` — but the set is not available
from the flag.

What closes it is an oracle carrying the queried set instead of the flag, with two facts about
it:

* the set is *secret-independent* on the blind side, since the blind cache carries no
  seed-bearing entry and the oracle's answers therefore do not involve the seed — which is what
  lets the secret be drawn after the run, as `prob_run_meets_honest_key_le` requires;
* the set's cardinality is at most the charged query count. Note this does **not** follow from
  cache growth: the blind cache starts with an entry at every non-PRF canonical input, so a
  query answered from it enlarges the set without enlarging the cache. It is bounded by the
  *counter*, every query being charged under all-queries accounting — so the instrumentation
  has to carry the set and the count together, as `WeightedCharge.countJoint` does for the two
  budgets.

`prob_touched_eq` then needs restating over that oracle. Its proof carries across unchanged:
the two cases are a query inside `S`, where both runs add the same input and the event is
already decided, and a query outside it, where the caches agree at that input so the answer
distribution is the same.


## Warming the game, and the defeq trap in `afterSeeds`

Every charge bounds an event against a *fixed* cell table, and has to: the alternative — a cell
drawn after the query that collides with it — needs a union bound over the whole graph, some
`2 ^ 26` cells, which no budget here can pay for. In the bare experiment the cells are a random
variable, so no charge applied to the run's own key. That gap was not an oversight in the
charges; it is why `Presample` exists.

`WarmedGame.warmedRun` closes it. `experiment_eq` puts `Security.experiment` into the
`liftM seeds >>= rest` shape (`liftM_bind` does the work; the three seed draws are coin
queries), `Presample.evalDist_counted_warmed` inserts the graph walk after the seeds, and
`probEvent_warmed` transfers the winning event — which looks only at the outcome, so the walk's
effect on the cache is invisible to it. `warmedRun_eq` then splits the run into `graphWalk` and
`tail`, and `probEvent_le_of_tail` reduces each half to a bound on the tail with the cells
fixed, averaged by `Averaging.probEvent_bind_pair_le`.

Three things the walk supplies, each now proved:

* `WarmedGame.mem_support_graphWalk` — the walk's result is always `cellsOfOutputs` of some
  output table together with the canonical cache of that table (read off
  `Programming.warmup_uniform` as a statement about the support, since the charges are uniform
  over the walk and never look at its distribution);
* `WarmedCharges.walk_cache_canonical` — that cache carries canonical entries and nothing else,
  which is the cleanliness hypothesis every charge takes
  (`Programming.cacheFrom_empty_canonical`);
* `WarmedCharges.count_le_of_budget_tail` — the budget, which speaks about `Security.runAll`,
  bounds the tail's count, imported through `evalDist_outcome`.

`prob_deviatingCollision_tail_le` is the first charge in this form: the structural term at this
run's own honest key.

**The trap.** `WarmedGame.afterSeeds` must be made `irreducible` wherever it is treated as an
opaque computation. Left reducible, a defeq check as trivial as closing a goal with a
hypothesis of *syntactically identical* type — verified identical under `pp.all` — unfolds it
and runs out of heartbeats. Two hours went into diagnosing this as a mismatch between `tail`
and its own definition; it is neither, and the one-line `attribute [local irreducible]` at the
top of a file that uses the game abstractly is the whole fix. Expect the same of any later file
that mentions the game without taking it apart.

## `SomeWotsWitness` is a tautology, and what that costs

`HypertreeDispatch.SomeWotsWitness secretSeed publicSeed` existentially quantifies the
signature it is about:

    ∃ message expected layer tree leaf (signature : XmssSignature),
      signature.wots = Wots.sign (m := Id) message secretSeed publicSeed (wotsAddress …) ∧
        message ≠ expected

Nothing ties `signature` to the forgery, so it can simply be built: take `signature.wots` to
*be* `Wots.sign 0 secretSeed publicSeed (wotsAddress 0 0 0)`, `message := 0`, `expected := 1`.
This was checked, not argued — the one-line proof compiles with no hypotheses. So that
disjunct of `cases_of_hypertreeFault`, and therefore of `HypertreeDispatch.cases_of_accepted`
and `GameBridge.cases_of_replayed_accept`, carries no information, and any charge stated
against it would have to bound a probability of one.

`Extraction.HypertreeChain.HypertreeFault` itself is sound: there the signature is
`signatures 0`, a component of the array the forgery supplied. The loss happens in the
*flattening*, which drops that binding. `SomeLayerCollision` drops it too, and is suspect for
a second reason: at the `Id` level the oracle is `CacheReplay.replayQuery cache`, which returns
`default` at every uncached input, so "collisions" among uncached inputs are free. What saves
the collision branch in practice is that the charge compositions
(`WotsCharge.deviatingCollision_of_chainCollision*`, `MerkleCharge.*`) each take the colliding
query's *cache entry* as an explicit hypothesis — and a predicate that has forgotten the
forgery cannot supply one.

So the flattened predicates have to carry the forgery's signature, and the WOTS branch has to
be pushed one step further than it currently is: holding `Wots.sign message` for an unsigned
`message` means holding a chain value below what any signature revealed, which is either a
chain collision (structural, already charged) or a WOTS secret, which is
`PRF(PK.seed ‖ ADRS ‖ SK.seed)` and so a seed-bearing query (the input half).
`Extraction.Wots.chain_eq_or_collision` is the step that splits those.

## Where the slack actually comes from

An earlier worry, now resolved: the two halves meet the target `q / 2 ^ 127` exactly, which
seemed to leave no room for the `2 ^ -165` input-format coincidence, the `2 ^ -126` load-cap
defect, or the `≈ 2 ^ -120` union over the chain positions at which a forgery could hold an
unrevealed honest value. The slack is not in the arithmetic; it is in the *query count*.

`Security.HasTotalBudget` charges `q` for **every** hash call in the game, key generation and
signing included. Key generation alone makes a fixed number `H` of calls — the whole top
subtree, on the order of `2 ^ 18` — and not one of them can produce a bad event: each is a
canonical query, so the structural clause is dead by `CanonicalTarget.clean_of_canonical_cache`
and the coverage clause by format, and the input half counts only the adversary's queries. So
both halves are really bounded by `(q - H) / 2 ^ 128`, leaving `H / 2 ^ 128 ≈ 2 ^ -110` of
slack — orders of magnitude more than every defect combined.

This is the robust source of slack, and it replaces the earlier plan of taking it from the
message-class weight (`Assembly.cap_defect_within_slack`), which supplies nothing on a run
with no message-class queries. What it needs proved is a *lower* bound on the honest hash
count, which is a deterministic count of a fixed computation, plus the fact that canonical
queries are never bad — which is already `cleanBad_walk_cache` in another guise.

## What the WOTS residue actually costs

`FaultCharge.WotsResidue` is what is left of a hypertree fault once the collisions are charged:
at some layer the forgery's WOTS signature is the *honest* signature of a message differing
from the honest input threaded into that layer. Turning that into something the budget pays
for has one easy half and one hard half, and the hard half is the deepest remaining question.

**The easy half, and a simplification worth naming.** Each WOTS key in the hypertree signs
exactly one message, and that message is a deterministic function of the key: the honest node
value one layer down. So unlike FORS, where the signed digests follow the adversary's chosen
messages, the hypertree's disclosures are not adaptive at all — `expectedInput` *is* what was
revealed. `Checksum.exists_decreased_digit` then gives a chain index whose forged digit is
strictly below the revealed one, so the forgery holds `chain(c, 0, j, secret_c)` for some
`j < k`, a value no signature ever disclosed. `Extraction.Wots.chain_eq_or_collision` is what
rules out the alternative that the forged value merely hashes to the right endpoint.

**The hard half.** Holding that value means one of three things, and only the first is already
charged:

* the adversary queried a seed-bearing input — the input half, as designed;
* it queried the canonical input of chain position `j'` for some `1 ≤ j' ≤ j`, whose payload is
  the chain value at `j' - 1`, so it already held *that*; by induction this bottoms out at
  `secret_c`, whose canonical input carries `SK.seed`;
* or at some step it supplied, as a query payload or in its output, a cell it had not obtained
  — a guess at a uniform 128-bit value.

The third is the one with no machinery behind it. Charging it per *cell* is hopeless: there are
about `2 ^ 26` cells, and `2 ^ 26 · q / 2 ^ 128` is far over budget. It has to be charged per
*query*, and then it unifies with the seed guess rather than adding to it: a canonical input's
payload is the concatenation of its children's cells, so a query at a canonical input whose
address names a node with an unobtained child matches that child's cell with probability
`2 ^ -128`, the address having fixed which cell is at stake. The seed guess is exactly this
event at a PRF node, where the only child is `SK.seed`. One event, rate `2 ^ -128`, two units —
which is what the input half already claims.

What that costs is an invariant carried along the adversary's execution — which cells it has
obtained — and the proof that an unobtained cell stays uniform given its view. That is the
"until-first-hit coupling" this file has called open from the beginning, in its sharpest form.
The blind comparison does not subsume it: stripping is a fixed set of entries chosen before the
run, and the obtained set is not.

Whether `q / 2 ^ 127` exactly survives this turns on it, so it is the next thing to settle.

## The obtained-cells invariant is not needed: fix the secret region instead

The section above left the input half needing an invariant along the adversary's execution —
which cells it has obtained — and called that the sharpest form of the coupling this file has
had open from the start. It is not needed. The region can be fixed before the adversary runs,
and then the existing blind comparison charges all of it at once.

**The secret region.** Call a structural node *secret* when its canonical input carries
something the adversary must not be able to form:

* `wotsPrf` and `forsPrf` — the only child is `SK.seed`;
* `forsLeaf` — the only child is a FORS secret cell;
* `wotsHash` at a chain position strictly below the digit the honest message encodes on that
  chain — the only child is the chain value one step back, which no signature discloses.

The last clause is the one that looked adaptive and is not. **Each WOTS key in the hypertree
signs exactly one message, and that message is a deterministic function of the key** — the
honest node value one layer down. So the revealed digit on each chain is fixed by the walk,
whether or not that leaf is ever signed, and the whole region is a function of the seeds and
the output table. Nothing about it waits on the adversary. (FORS is the opposite — its signed
digests follow the adversary's messages — which is why the FORS *coverage* event goes to the
tape instead, and why `forsLeaf` is stripped wholesale rather than by disclosure.)

**Why stripping that region is enough.** The blind cache is the walk's cache with every secret
node's entry dropped. Its remaining keys mention only non-secret cells, and its remaining
values are the output table's other coordinates, so the blind cache is independent of the
secret cells and of `SK.seed`. The honest phase, stripped by `StripCached`, asks nothing the
walk's cache answers, so it never touches the region — the single reason the earlier,
PRF-only, version of this comparison said nothing. And the signatures still hand the adversary
exactly what they should: chain values at or above the revealed digit, and FORS secrets at the
disclosed positions, all read from the table rather than queried.

**The rate is exactly right.** A secret node's canonical input is
`PK.seed ‖ ADRS ‖ (its children's cells)`, and the address determines the node, hence *which*
cell is at stake. Every node in the region has exactly **one** secret child — `wotsPk` and
`forsRoots` collect endpoints and roots, which sit at or above the revealed positions; tree
nodes collect tree cells — so a query matches a stripped input with probability `2 ^ -128`,
two units, and the union is over queries rather than over the `2 ^ 26`-odd cells. Charging per
cell was what made this look impossible; charging per query makes the chain-value guess and
the seed guess *the same event* rather than two, which is what the budget was always assuming.

So the input half is `q / 2 ^ 128` exactly, and the ingredients are the ones already proved:
`StripCached` to keep the honest phase out of the region, `TrackedQueries.prob_meets_real_eq_blind`
for the exact comparison, and `SeedDeferral.prob_any_honest_key_le` generalised from one secret
to a family — each query still putting only one coordinate at stake.

## The adaptive digest tape, and what it did not need

The coverage half's missing step — exhibiting the game's `H_msg` answers as a uniform tape when
the inputs are adaptively chosen — is proved. `DigestTape.prob_romEvent_le` bounds any event
witnessed by recorded digests at `1 / 2 ^ 141 + limit / 2 ^ 128`, where `limit` is growth at
*message-class inputs only*, so instantiating at the `H_msg` format gives `qm / 2 ^ 128` rather
than `q / 2 ^ 128`. That is the budget's allowance exactly.

The move that unlocks it: `GrowthCharge.prob_cache_values_le` pins coordinates by naming their
*inputs*, which cannot be done when the signer's inputs follow the adversary's messages. The
recording pins them by **position in query order** instead — `prob_prefix_le`, a lazy-sampling
invariant saying that any word fixed in advance is a prefix of the recording with probability
at most `|HashOutput| ^ -length`. Nothing has to be named in advance, and the instrumentation
is invisible (`recorder_eq_rom`).

Two corrections to what this file said before:

* The `DeferredSampling.Factorizes` obligation recorded under "What is not done" is about the
  *input* side — the until-first-hit seed deferral — not about coverage. For coverage it would
  have been strictly stronger than needed: `ForsLeaveOneOut.independent_tape_coverage_le` is
  already an inequality about a uniform tape, so the one-sided "no event is likelier on the
  recording than on a uniform tape" is the whole requirement, and the prefix invariant gives it
  directly.
* The mixture form `independent_tape_mixture_coverage_le` is not needed either. At the constant
  policy every coordinate is selected, `expectedUses = trials`, and the bound is already what
  the budget allows; the mixture would only be needed to get *below* `trials`.

A run may record fewer than `trials` answers, so the tape is completed with an independent
uniform pad drawn afterwards. That is sound upward because coverage is monotone in the
disclosures — `tapeCovered_of_prefix`.

What is left on this half is wiring, none of it probabilistic: instantiate `keep` at the
`H_msg` format (`DigestInputDistinct` separates it from the structural format), witness the
coverage event by recorded rather than pre-existing answers (the warm cache is purely
canonical, so no `H_msg` entry predates the tail), and feed the message-class growth from the
budget.

## Correction: `forsLeaf` cannot be stripped wholesale

The section above claims the secret region includes every `forsTree key ⟨0⟩ index` node — the
FORS leaf hashes, whose only child is a FORS secret cell — and that stripping them wholesale
makes the blind cache independent of those cells. The second half is right; the first half
breaks the bound, and the error matters because it is the difference between the WOTS and FORS
sides.

A FORS secret that *was* disclosed is in the adversary's hands legitimately: it came in a
signature. It may then query that leaf's canonical input — `PK.seed ‖ ADRS ‖ the secret` — and
be perfectly entitled to the answer. If that entry is stripped, the blind run diverges there,
so the comparison reports "bad" on an event the adversary reaches honestly, as often as it
likes. The bound `q / 2 ^ 128` is then simply false; nothing is wrong with the proof technique,
the region is wrong.

So the region may contain only the *undisclosed* FORS secrets, and which those are follows the
adversary's chosen messages. **The WOTS clause survives** — each hypertree WOTS key signs one
deterministic message, so its revealed digit is fixed by the walk — but the FORS clause does
not, and the claim that the whole region is fixed before the run was too strong.

What the FORS case needs is a per-step argument: the first query at an undisclosed leaf's
canonical input matches that leaf's cell with probability `2 ^ -128`, conditioned on a
"not yet disclosed" predicate that the run so far determines. That is the same shape as
`DigestTape.prob_prefix_le` — a lazy-sampling invariant indexed by query order rather than by
inputs named in advance — which is now proved, so the pattern is available even though this
instance is not written.

The `wotsPrf` and `forsPrf` clauses are unaffected either way: their canonical inputs carry
`SK.seed`, which no signature ever discloses, so they are secret unconditionally.
