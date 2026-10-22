# SLH-DSA-128s: proof status

**Concrete construction and experiment. The 127-bit security theorem is not established.**

The experiment is deterministic, pure SLH-DSA-128s with at most
2^64 signing requests. Work counts direct adversary hash calls and every hash
call in final verification, including repeated inputs. Honest key generation
and signing share the same oracle but contribute no work. The target is
SUF-CMA advantage at most q/2^127 for every almost-sure work budget q ≥ 1;
`Proof/Security.lean` proves that any SUF-CMA bound implies the same EUF-CMA bound.

## Where the proof stands

*About to change a parameter, a draw or a recorder? Read `REVIEW.md` first — it is one page of
checks that are cheap to run and expensive to rediscover, and it points back here for the
reasoning.*

*Read this first, and read the rest knowing what it is.* The sections below are in the order
they were written, so several of them record designs that were later replaced. Those are marked
**Superseded** at the top, with one line saying what replaced them. Nothing is deleted: why a
design was rejected is the part of this file that stops it being proposed again, and twice in
one day a note of that kind has done exactly that.

`Obligations.target_of_charges` reduces `HasTotalSecurityBits .strong 127` to **two** statements
about the warmed tail. That is the whole of what is outstanding.

### The answer half

`Obligations.AnswerCharged`, at a fixed walk, bounded by
`q / 2 ^ 128 + (1 / 2 ^ 126 + 1 / 2 ^ 141)`.
`AnswerSide.prob_answerBad_good_le_of_caps` proves it from four hypotheses, and each is a named
piece of work rather than a design question:

* **`hlate`** — the ordering defect, as a support hypothesis on the recorded run.
* **`hleftBound`** — the disclosing recording is no longer than a `leftLength ≤ 5 * 2 ^ 62`.
  Settled: `ServedAgreement.record_length_le_cap` gives it at `signingLimit`, which is
  `4 * 2 ^ 62`. The headroom is a quarter and no more; see *How long the disclosing recording
  is* in `Proof/ServedAgreement.lean` for why twice the signing limit would not have been
  recoverable.
* **`hseed`** — the narrowing's leftover, as a term the caller adds.
* **`hdisclosing`** — the recorder's left test agrees with the log. Left to right is log
  faithfulness and is proved (`ServedBridge.signerRandomised_of_servedLog`); right to left is
  false while the test reads the cache, and retires when the test becomes the carrier's served
  set, which `ServedAgreement.agreesWithLog_run` now supplies in both directions.

### The shared half

`Obligations.SharedCharged`, read at the walk and the game together, bounded by
`(q - 2 ^ subtreeHeight + 259) / 2 ^ 128`. `SharedJoin.sharedCharged_of_two` proves it from
**two** charges and nothing else:

* **`hinput`** — `GoodWalk ∧ InputBad ∧ ¬ ordering`, charged to the record's **aiming** part
  plus the forgery's 259 claims;
* **`hordering`** — the ordering defect, charged to the record's **message-class** part.

There is no third hypothesis. The cover between the two is excluded middle
(`SharedJoin.cover_of_em`), which also means the ordering defect's event may be restated however
its owner likes without this step moving. The arithmetic closes on the nose: the two parts are
disjoint by construction, `Multiset.card record = counts.work`, and
`work + 2 ^ subtreeHeight ≤ q`.

### Where each hypothesis has to be discharged, which is not a free choice

`hinput` is discharged directly at `RandomiserRecord.recordedPairedRun`, **not** through
`SharedJoin.hinput_of_probesIn`. That adapter is sound and the input half cannot use it, because
it takes its charge per walk and the input half's charge cannot be read at a fixed walk: see
*A charge that defers its secret cannot be read at a fixed walk* below for the rule, which is
that a charge may be read at a fixed walk exactly when the randomness it spends is drawn after
the walk. `hordering` spends the oracle's own fresh answers and so may use the per-walk adapter;
the two adapters now say which owner each serves.

### What is no longer owed

The randomiser defect's charge is gone: the replay branch closes outright by strong freshness,
so no branch reaches it. With it went the four-term shared accounting, the three-way
classification of the record by first block, and the signer's coincidence — which was paying for
a cache proxy that the carrier's served set has replaced.

### One rule, three times paid for

**State a lemma against what it actually uses, and it survives the thing it was written for
changing.** This is not a style preference; it is the difference between a feared restatement
and an `exact`, and it has decided three changes in a single day:

* the **writer**: `StrippedGame.evalDist_countedRun_congr`'s proof never reads the monoid the
  phase carries, so the recorded game's stripping law is the counted game's with the writer
  freed — one argument, not two (`RecordedStripping.evalDist_writerRun_congr`);
* the **carrier**: the stalled stack consumes monotonicity at exactly two call sites and uses no
  property of the relation beyond what the step lemma hands it, so availability becoming
  carrier-valued cost a rebase rather than a redesign;
* the **disclosed set**: `CanonicalGraph.available_of_children_available` takes it as a
  parameter, so closure holds at the served log without a line of new proof
  (`ProbeContainment.closed_disclosedByLog`).

The converse is the warning: a lemma stated against the *occasion* rather than the content —
the warm filter for the input half's weights, `recordCanonical` for its part — looks right,
survives review, and is wrong in the direction that reads as a simplification. Both of those
narrowings kept only the probes that **succeed**, and both were caught by asking what the
statement actually quantifies over.

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

**Superseded** by *The first-principles architecture*, below, which replaced the budget this
section reasons inside. Kept for the dead ends it records.

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

**Superseded** by *The first-principles architecture*, below, which replaced the budget this
section reasons inside. Kept for the dead ends it records. The obligations are now the two in
*Where the proof stands*.

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

**Superseded** by *The first-principles architecture*, below, which replaced the budget this
section reasons inside. Kept for the dead ends it records. It is no longer the current target.

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

**Superseded** by *The first-principles architecture*, below, which replaced the budget this
section reasons inside. Kept for the dead ends it records.

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

**Superseded** by *The first-principles architecture*, below, which replaced the budget this
section reasons inside. Kept for the dead ends it records.

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

**Superseded** by *The first-principles architecture*, below, which replaced the budget this
section reasons inside. Kept for the dead ends it records.

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

**Superseded** by *The first-principles architecture*, below, which replaced the budget this
section reasons inside. Kept for the dead ends it records.

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

**Superseded** by *The first-principles architecture*, below, which replaced the budget this
section reasons inside. Kept for the dead ends it records.

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

**Superseded** by *Where the proof stands*, at the top. Kept because it records what the
architecture looked like before the two obligations were isolated.

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

## The input half, stated once and properly

Putting the last two sections together, the input half is one event, not two, and it is this:

> the adversary queries the canonical input of a node one of whose children's cells the
> signatures issued so far do not make available.

Call such a node **sensitive**. A cell is *available* when the signatures already issued let
one compute it: a WOTS chain value at or above that key's revealed digit, a FORS secret at a
signed position, and anything the public structure derives from those. Everything else — every
`wotsPrf` and `forsPrf` cell, every chain value below the revealed digit, every unsigned FORS
secret — is not.

Three things make this the right statement.

* **It is one event.** The seed guess and the chain-value guess are the same thing: a canonical
  input is `PK.seed ‖ ADRS ‖ (its children's cells)`, and the address says which node, hence
  which cell, is at stake. At a PRF node that cell is `SK.seed`; one step up a chain it is the
  previous chain value. Charging them separately would double the input half and break the
  budget; charging them as one costs `2 ^ -128` per query, two units, which is exactly what the
  half allows.
* **Every sensitive node has exactly one unavailable child**, so the rate really is `2 ^ -128`
  and not a multiple of it. `wotsPk` and `forsRoots` collect endpoints and roots, which sit at
  or above the revealed positions; tree nodes collect tree cells; `wotsHash`, `wotsPrf`,
  `forsPrf` and the FORS leaves each have one.
* **Availability depends on the signing log, not on the oracle transcript.** This is what makes
  the argument tractable where "which cells has the adversary *obtained*" did not: the
  predicate is decided by which messages were signed, so it is a function of the game's own
  state rather than of the adversary's queries. It is still adaptive — the WOTS part is fixed
  by the walk, the FORS part follows the adversary's messages — so the blind comparison with a
  region chosen in advance covers only the WOTS and PRF clauses, and the FORS clause needs the
  per-step form.

The per-step form is the one `DigestTape.prob_prefix_le` demonstrates: a lazy-sampling
invariant indexed by position in query order, conditioned on a predicate the run so far
determines. That technique is now proved in this development, for the digest tape; the input
half needs the same shape with "the payload matches an unavailable cell" in place of "the next
letter matches".

## The sensitive-query charge, and the condition it cannot do without

`SensitiveQuery.prob_probes_sensitive_le` charges the input half's event at `2 ^ -128` per
query — the rate the budget needs, exactly, with no conditioning factor, because the cell table
is drawn *after* the run so every candidate was fixed before its coordinate was.

The specification this file gave for it was incomplete, and the lemma is false as it was
stated. The missing condition: **availability must be closed under the structure** — a node all
of whose children are available has an available cell. Without it, take a node that is not
sensitive but whose own cell is unavailable; a run queries it outright, reads its cell off the
answer, and can then form the canonical input of the node above it at will. That node is
sensitive for the rest of the run, so a sensitive query happens with probability one.

The condition holds here, and `CanonicalGraph.available_of_children_available` proves it by
cases: every node with an unavailable cell has an unavailable child. `sensitive_of_not_available`
is the form the charge consumes — a protected cell is reached only through a sensitive query.

**What the charge still does not have.** It is stated for a run that does not consult the cell
table, with the table deferred to the end; what the game offers is a run against a cache
*programmed* from that table. Those differ by a step, and the step is not the blind comparison
already in the tree: the region to strip is `{the canonical input of p : p sensitive now}`, and
it **shrinks** as signatures release cells. `AgreeOff` is not preserved across a release — the
real cache holds the newly-non-sensitive entry, the blind cache does not, and the input has
just left the region — so `BlindComparison.prob_touched_eq`, which compares caches agreeing off
a set fixed in advance, does not apply. Over-approximating to the initial region restores the
invariant and destroys the bound; that is `sensitive_initial`, the `forsLeaf` failure recorded
above, now a lemma rather than prose.

The way to meet the hypothesis rather than prove the comparison: have the **signer** draw each
released cell fresh at the moment of release. A cell a signature discloses is uniform in the
view it is disclosed into, so this is a deferred-sampling rewriting of the signing oracle — the
move `Programming.warmup_seed_uniform` already makes for the walk — and it leaves exactly the
never-released cells for the deferred table. It is an obligation about the honest phase, not
about the adversary, and it is much weaker than the until-first-hit coupling. The honest phase
is being taken out of the experiment anyway (`StrippedGame`), so that is the shape to give it.

Note this does not conflict with the walk. The two halves are bounded separately on the same
game, so each may use its own presentation of it: the answer side needs the cells fixed before
the adversary runs, the input side needs them deferred.

## State of the proof, consolidated

**Superseded** by *Where the proof stands*, at the top.

The table under "State of the first-principles proof" above is superseded. Everything listed
here is proved, unconditionally, with no `sorry` and an axiom guard.

**The game.** `WarmedGame` puts `Security.experiment` into `liftM seeds >>= rest`, inserts the
canonical graph walk after the seeds, and splits the result into `graphWalk` and `tail`;
`probEvent_warmed` transfers the winning event for free, the walk touching only the cache.
`MainTheorem.totalSecurityBits_of_bound` is the target asking for nothing but a bound, since
the two halves live in different presentations.

**The split.** `SplitCharged.cases_of_win_charged`: an accepted forgery in the warmed tail is a
deviating structural collision, a WOTS residue, or the honest FORS secrets at the positions its
digest selects — every index bound to the forgery, no free existentials. Underneath:
`WarmedSplit` (the game's run factored through its phases), `VerifierProbes` (every cache entry
the charges ask for, reached from the verifier's own queries), `FaultCharge`, `ForsBranch`,
`WotsResidueReduction`.

**The answer side.** `WarmedCharges.prob_deviatingCollision_tail_le` and
`prob_combinedBad_tail_le` at the walk's own cells; `CoverageTail.prob_coverage_tail_le` at
`1 / 2 ^ 141 + qm / 2 ^ 128`, charged on the message class, resting on `DigestTape`'s
adaptive recording.

**The honest phase.** `HonestProbes`: key generation asks the warmed cache nothing new, signing
asks only its two message inputs. `StripCached` and `StrippedGame` take it out of the
experiment, leaving the adversary's oracle and the verifier untouched. `HonestGrowth`: it
spends at least `2 ^ subtreeHeight = 512` of the budget while adding nothing to the cache,
which is the slack the defects live in.

**The instrumentation.** `RecordedQueries` records the adversary's and verifier's own queries
with `card = counts.work` exactly and is invisible; `RecordedBudget` bounds that by `q`;
`AdversaryQueries.work_le_total` is the unconditional `work ≤ total`.

**The input half's charge.** `SensitiveQuery` charges a query at a node with an unavailable
child at `2 ^ -128`, given closure; `DrawnTable` holds that rate against a table drawn before,
during or after the run, by `missRun` — the probes made while every answer is "miss" are a
determined list, so no conditioning appears. `SensitiveShape` supplies the two graph facts: a
sensitive node has exactly one child, and availability is closed. `GraphStakes` instantiates it,
with the forgery's `C = 259` claimed cells charged as candidates.

**What is left**, none of it with unknown content:

1. the lazy drawing handler, the flag-free/flagged split, and the composition through
   `LazyBridge` / `TableBlind` / `StalledRun`;
2. `revealed` pinned to the *signer's* digit rather than the fault's — required exactly, since
   over-claiming puts the forgery outside the charged event and under-claiming makes
   `q / 2 ^ 128` false;
3. the position function from the forgery, and `claimedCandidates` wired into the record;
4. the final arithmetic: `(q − 512 + 259) / 2 ^ 128` for the input half, `(q − 512) / 2 ^ 128`
   plus `2 ^ -126 + 2 ^ -141` for the answer half, summing under `q / 2 ^ 127`.

## The strong-freshness replay case

A real gap, found by routing the FORS branch to the coverage event and discovering it cannot
be routed there.

Strong freshness excludes the forged *pair*, not the message. So an adversary may have `M`
signed, receive `(M, σ)`, and forge `(M, σ')` reusing the signer's own randomiser `R` and
changing the signature elsewhere. Then the forgery's message input `H_msg(R, PK, M)` *is* the
input the signer queried — one cached entry, and it is the forgery's own target. Coverage
requires the witnesses to be inputs *other* than the forgery's, so neither `ForgeryCovered` nor
`CacheCovered` fires; and the FORS branch's event — the forgery's secrets are the honest ones
at the digest's positions — holds with probability about one, the adversary having copied them
out of the signature it was given. Under `Notion.standard` the case evaporates, since the
message was never signed; the target is `.strong`, so that is not a way out.

The case is charged structurally, and nothing escapes:

* the FORS part differs — both recover the genuine key, so either a `ForsCollision`, or every
  secret is honest and the auth paths differ, which is a path collision, also a `ForsCollision`;
* the FORS part agrees and the hypertree part differs — a different hypertree signature
  verifying to the same root is a `HypertreeFault`;
* both agree — then `σ' = σ`, contradicting freshness.

**What blocked it** is that the split's left disjunct discards the fault.
`verify_fault_or_fors_canonical` concludes `forsKey = honestForsKey ∨ HypertreeFault`, and when
the hypertree is mauled *and* the FORS key is genuine both hold, so the left is taken and the
fault is lost. The repair is to strengthen the canonical branch to pin the whole *signature*
rather than the key: the no-fault branch of the recursion already establishes that each layer's
WOTS signature is the honest signature of the honest message, and that is what has to be
retained instead of being weakened to an equation about the root. The same on the FORS side,
where the non-collision branch currently pins only the secrets and not the paths.

`Fresh .strong` then has to be threaded into the split, where it currently does not appear —
nothing below `MainTheorem` mentions it. That is the honest place for it: the statement being
proved is about fresh forgeries, and this is the one step that uses what freshness says.

`CoverageRouted.forgeryCovered_of_witnesses` closes the branch the moment the structural side
rules out "the forgery's own input is the only witness", so everything else on that route is
already proved.

## `signedAt` was too generous, and what closing it costs

Found while routing the replay case: availability read "some cached message-class digest selects
this position". The adversary can pick a randomiser of its own, query `H_msg(R, PK, M)` itself,
and thereby mark all fourteen of that digest's positions available with its own input as the
only witness. Then the claim is not sensitive so the input half does not charge it, coverage
does not fire because the only witness is the target, and the canonical-signature route misses
because the randomiser is not the signer's — while the adversary still has to hold honest FORS
secrets no signature disclosed, which is the event the charge exists for.

The tightening: count a digest only when the signer's own randomiser entry is cached too — the
entry at `randomizerInput SK.prf PK.seed M`, whose answer truncates to the randomiser the
message input carries. The signer queries `PRF_msg` before `H_msg`, so every genuinely signed
message has it; it is still a function of the cache and still monotone along `Persists`; and in
the remaining witness-is-target case the randomiser is then the signer's, which is exactly the
hypothesis the canonical-signature route was missing.

**That moves the gate rather than removing it, and the gate has to be paid for.** The adversary
can still manufacture the entry by querying `randomizerInput` with the real `SK.prf`, which the
format carries in the clear, and such a query is not a canonical input so the sensitive-node
charge does not see it. It is the one-secret case — `SeedDeferral.prob_run_guesses_secret_le`
at `guessOf := the first n bytes as a Digest` — and the budget stays flat because the two
events sit on disjoint classes: a canonical input begins with `PK.seed`, a `randomizerInput`
carrying `SK.prf` begins with `SK.prf`, so each query falls in at most one and the two class
counts add to the record length. The exception, `SK.prf = PK.seed`, costs one unit of `2 ^ -128`
against the 760 units of margin, and joins the defect list.

This is the second place where an over-approximation of availability was sound-looking and
wrong — the first was stripping every FORS leaf. Both failed the same way: a predicate loose
enough to be convenient let the adversary reach a protected cell without being charged.

## The secret seed is not a coordinate the charge can be blind to

Landing the sensitive-query charge at the game ran into this, and it is sharp rather than
fixable: the charge fixes the computation *before* the table is drawn, while the game's
computation carries the secret seed as **data** — `afterSeeds` calls `keygenInternal sds.1 …`
— and that seed is the table's own `.secretSeed` cell. Stripping does not help; it keeps the
honest phase from *querying* canonical inputs precisely by having it *read* the warm cache
instead, which is the same dependence.

Blindness is needed per index, and `AgreeOff index` leaves every other coordinate alone, so for
every `index ≠ .secretSeed` the two tables agree at `.secretSeed` and a computation depending
only on that cell is literally the same computation on both. Exactly one term fails.

So the sum runs over `Finset.univ.erase Node.secretSeed`, and the excluded term is charged by
the machinery this development started with. The nodes staked on `.secretSeed` are exactly
`wotsPrf` and `forsPrf`; their canonical inputs are `TrackedQueries.prfInput`; and
`TrackedQueries.prob_meets_real_le` charges that event at `limit / 2 ^ 128` through
`BlindComparison`'s exact comparison and `SeedDeferral`. That half was never wrong — it was
waiting for the honest phase to be taken out of the computation, which `StrippedGame` has now
done.

The budget stays flat. A query's address determines its node, and a PRF node's address differs
from every other shape's, so each query is charged in at most one of the two classes and the
two counts add to the record's length. No new defect.

Worth recording as a pattern: the input half ended up needing **both** techniques, not one
replacing the other. The static blind comparison handles the one cell that is fixed before the
run and that the computation reads; the dynamic stalled comparison handles the cells whose
availability follows the signing log. Each is wrong for the other's case.

## `PRF_msg` and `H_msg` overlap, and the slack has to scale with signing

The sharpest finding so far, and it is faithful to FIPS 205 rather than an artifact. For the
SHAKE parameter sets,

    PRF_msg(SK.prf, opt_rand, M) = SHAKE256(SK.prf ‖ opt_rand ‖ M, 8n)
    H_msg(R, PK.seed, PK.root, M) = SHAKE256(R ‖ PK.seed ‖ PK.root ‖ M, 8m)

are the same function at two output lengths, and a SHAKE output of length `8n` is a prefix of
one of length `8m` — which is exactly how this model idealises them, `shortHash = truncate ∘
hash`. With `opt_rand = PK.seed` the second input is an instance of the first:

    messageInput R pk M = randomizerInput R pk.seed (bytesBE n pk.root ++ M)

by associativity alone (`RandomizerGate.messageInput_eq_randomizerInput`). So the signer's own
*digest* query is a `PRF_msg` input, and it can write the entry `SignerRandomised` looks for at
a message it never served: it needs the randomiser it derived for some served `M''` to equal
`SK.prf`, and the forgery's frame to be `PK.root ‖ M''`, which the adversary can arrange by
choosing its context once `PK.root`'s first byte is zero. Domain separation is not available as
a repair, because the standard does not separate them.

**The defect is affordable; the slack accounting was wrong.** The event needs a *served*
request whose derived randomiser hits a fixed secret — one fresh uniform value per request, so
at most `s / 2 ^ 128` for `s` requests, with the root-byte factor not even needed. Against that,
counting only key generation's `2 ^ subtreeHeight` hashes cannot work: a constant cannot cover a
term proportional to `s`.

But signing hashes too, and after the walk its canonical queries are cache hits — charged to `q`
and buying nothing, exactly as key generation's are. So the slack is `H_keygen + s · H_sign`,
and the condition becomes `1 ≤ 2 · H_sign`. **One** hash per served request suffices, and the
signer makes thousands; the margin is `2 ^ 9` even counting one.

The lesson generalises past this case: a defect proportional to the adversary's use of an oracle
must be set against the honest work that use provokes, not against a constant. Charging every
hash call in the game is what makes that available.

## The signer walks through the cells the charge protects

The deepest obstruction so far, and it is about where the honest signer *lives* rather than
about any probability.

The off-seed charge needs the computation blind to the staked cell. The honest signer computes
each WOTS chain from its start, so for a chain with revealed digit `d` it touches `wotsPrf` and
`wotsHash` at every step below `d - 1` — cells `Available` calls unavailable at *every* state,
since the revealed digit is fixed before the run. Those are exactly the cells the off-seed
charge is about. Stripped, the signer *reads* them and blindness fails; unstripped, it *queries*
them, those queries are off-seed sensitive, and the sticky flag fires with probability one.
Replacing it by its value does not help, the way it helped key generation: a signature's
components are available cells, but the walk that produces them is not.

**What rescues it is stalling, which is already built — one level up.** The charge is per index
and the run is stalled the moment that index becomes available; the signer reads a disclosed
cell only *after* the signature that discloses it, hence only after the stall, so the stalled
run never reads it. That is the content for the FORS secrets, whose availability follows the
signing log, and vacuous for the WOTS cells, whose availability is static.

But stalling freezes the **handler**, not the computation. So the signer has to move into the
handler stack the charge simulates, where its reads are frozen with everything else and
`lazyProgram`'s existing step condition — answer only what the signatures have made available —
is exactly the condition it must meet. In the computation no hypothesis of the `htouched` kind
can express "available at the state where it is read", because the computation is not stepped.

Two things that have to hold and are being checked rather than assumed: that the digest query
precedes the FORS reads, since `signedAt` is what makes those cells available; and that moving
the signing oracle out of its nesting is a `simulateQ` identity rather than a redefinition of
the experiment.

The pattern across the last three obstructions is the same one: **a value that is available,
computed by a walk that is not.** Key generation's root, the FORS public key, and now the
signature. Each time the fix has been to replace the walk by the value — and this time the
value has to be read at the right moment as well, which is what moving into the handler buys.

**A habit worth keeping.** Three times in this line of work the lemma that was needed already
existed one file over, twice in a more general form than the one being written — the writer's
run lemmas generic in the monoid, the Merkle node's cell identity, the sum handler's apply
lemmas. The rule that catches it is to look in the file that would *own* the statement before
writing it: the file about writers owns a lemma about writers, whatever the reason for wanting
it. Five accidental duplicates have been found here after the fact, and each cost more to find
than the look would have.

## A budget that admits an adversary at all pays for key generation

The accounting hands the charges `q - 2 ^ subtreeHeight`, and on `Nat` that subtraction
truncates, so it counts hash calls only once `q` is known to reach `512`. It does, and for a
reason internal to the budget: every run of the game builds the top subtree and is charged for
it, so a smaller budget is exceeded on every run the game has, and an event asserted with
probability one that holds nowhere has probability zero instead.

That argument also settles what looked like a gap. Nothing in the chain requires the support of
the run to be nonempty, and nothing has to: an adversary whose run can fail everywhere makes
`HasTotalBudget` false for every `q`, so the theorem says nothing about it. The empty case is
closed by the same line that closes the small-budget case rather than excluded by a hypothesis
no one had stated.

## The traps, consolidated

**The index.** Eight are known. Six are the numbered list in this section; the last two are
their own sections further down, because they are not defeq failures at all and the symptom is
different. Two of the six have since been *confirmed* — seen twice, from different directions —
and those are the ones worth reading first, because a trap seen once can still be a quirk of one
proof.

1. An opaque game definition — and the half that still costs builds, that
   `attribute [local irreducible]` is per file (**confirmed**).
2. Rewriting under a binder — and the variant where a rewrite that fires first moves the term a
   later one was going to match.
3. A choice-based lookup.
4. A semireducible index — never rewrite across it, convert by application. Three riders: the
   repair that looks right and is not, the **projection trap** (**confirmed**, in two distinct
   shapes), and the instance cousin at `rw [Scheme.sign]`.
5. An instance path.
6. Two spellings of one value — a convention, not a tactic.
7. *A disjunct that is true outright* — below. The elaborator cannot catch this one: the
   statement is well typed and vacuous.
8. *An ascription that changes which lift is meant* — below.

Each of these cost hours, and each presents differently. The common shape: two terms are equal
by unfolding but not by matching, so the tool that needs them to look alike declines — and the
way it declines points away from the cause.

1. **An opaque game definition.** The symptom is a rewrite that cannot see into the term at all.
   The cause is a definition that does not reduce where the lemma expects it to; the fix is a
   `show`, or an equation lemma stated at the shape the goal has.

   **The other half of it, which is the one that still costs builds.** `attribute [local
   irreducible]` is *local*, so every file that mentions `WarmedGame.afterSeeds`,
   `WarmedGame.tail` or the recorded pair of them has to declare it again. A file that does not
   does not fail with a missing pattern — it fails with `(deterministic) timeout at whnf`, on
   statements that look innocent, and the timeout is reported at whichever elaboration step
   happened to be running. `SharedJoin` cost three builds to this before the attribute line was
   added. The rule: a new file that names a game definition declares the attribute *before* its
   first lemma, not after the first timeout.
2. **Rewriting under a binder.** The symptom is `rw` reporting its pattern missing on a goal
   where the pattern is plainly visible — inside a `fun`. `simp only` goes under binders; `rw`
   does not.

   A variant with the same symptom and a different cause: **a rewrite that fires first can move
   the term a later rewrite was going to match.** Normalising a signature's randomiser before
   its digest makes one side's digest the digest of the *other* side's randomiser, so the
   digest's own congruence can no longer fire. The cure is ordering, not tactics: normalise the
   term everything else is indexed by first.
3. **A choice-based lookup.** The symptom is a congruence that will not close: two invocations
   of `Classical.choose` on propositionally equal inputs are not equal terms, so anything built
   over them is incomparable. The fix is to avoid choice in the definition rather than to fight
   it in the proof.
4. **A semireducible index.** `(spec₁ + spec₂).Range (Sum.inr t)` and `spec₂.Range t` agree only
   semireducibly. The symptom is `rw` reporting its pattern missing *and* `simp` declining
   silently, with unfolding producing terms that are not type-correct at `instances`
   transparency. The rule: phrase each lemma at the index its goal has, and convert once, inside
   that lemma's own proof.

   **The refinement, paid for twice.** "Convert once, inside the lemma's own proof" is not
   enough when the lemma is used on a *hypothesis*. Rewriting a hypothesis across the index
   succeeds — and then every later `rw` in the same chain fails with *did not find an occurrence
   of the pattern* on a goal where the pattern is plainly visible, because the term the first
   rewrite produced is no longer type-correct at `instances`. The failure is reported at the
   second rewrite, which is innocent, so the search starts in the wrong place.

   Two repairs that look right and are not. Ascribing the lemma's right-hand side at the sum's
   `Range` does nothing: an ascription is a defeq check, so the elaborator keeps the term's own
   type and the statement comes out at the summand's index anyway. A `show` localising the
   conversion inside the proof makes that proof go through and leaves the *statement* mixed, so
   the caller breaks instead.

   What works is to keep the conversion out of every rewrite. State the lemma entirely at the
   **summand's** index, where it is self-consistent and every rewrite inside it is sound, and
   **apply** it at the sum's index with `exact` — one defeq check at `default` transparency,
   which succeeds because the gap is only semireducible. `AdversaryQueries` already does this
   (`work_le_count_adversaryImpl` applied at `Sum.inl`), and `SigningFaithful` follows it. So
   the rule has a second half: never rewrite across the index, convert by application.

   **A third member of the family, which presents as a timeout rather than a mismatch, and
   which is now confirmed rather than observed once.** When a term the unifier has to solve for
   appears only under a *projection*, it leaves a constraint of the form `?x.2 =?= e`, which
   cannot be matched and is chased instead. The symptom is a `whnf` timeout, attributed to
   whichever step was running, and no heartbeat budget fixes it. The fix is always to supply the
   argument by name.

   Two distinct shapes have now been seen, which is what makes it a fact about the elaborator
   rather than about one proof:

   * an **implicit in a lemma's conclusion** — `AnswerSide.generatedKey_eq_walk` mentions its
     result only as `result.2`, so applying it leaves `?r.2 =?= e`;
   * a **placeholder at an application** — writing `_` for the secret key in
     `ServedBridge.carrierBelowLog_of_filed` left `?sk.publicKey =?= RoutedSplit.keyOf …`.

   The second caught the author of this note in his own file within a day of writing it. Both
   times the statement elaborated fine and only the proof looped, so the way to separate them is
   to stub the proof and check whether the declaration still times out: if it does, the
   statement is the problem; if it does not, look for a `_` or an implicit that only a
   projection determines.

   A related habit for statements: a big term written out several times — `RoutedSplit.keyOf`
   applied to a trace, say — makes the elaborator chase it at every occurrence. Taking it as a
   parameter tied by an equation and `subst`ing it in the proof costs two lines and elaborates
   instantly.

   The same transparency gap has a cousin that presents as a missing instance.
   `rw [Scheme.sign]` works at `m := OracleComp OracleWorld` and fails at `m := Id` with
   `failed to synthesize HasQuery HashSpec Id`, because `rw` elaborates the equation lemma on
   its own and `CacheReplay.replayQuery cache` is a term, not an instance. The fix is the same
   shape: prove the step monad-generically with the instance as a variable, and instantiate it
   by `@`-application.
5. **An instance path.** Two syntactically different `MonadLiftT` instances for the same pair of
   types, not definitionally equal, so a lemma stated at one cannot be applied at the other. The
   symptom is an instance search failing *downstream* of the mismatch — the search is for
   something the mismatch made unsatisfiable, so its error names the wrong thing. The rule:
   pin the instance in one definition and route everything through it, and let a law relating
   the pinned construction to the original be the check, since the pin itself cannot be checked
   by `rfl` when the terms genuinely differ.

6. **Two spellings of one value.** `BitVec.toFin x` and `⟨x.toNat, x.isLt⟩` are the same `Fin`
   and not the same term, so a lemma stated about a key spelled one way will not rewrite a goal
   that spells it the other. The symptom is the familiar one — a pattern plainly present and
   not found — but the cause is different from the rest and so is the cure: **a convention, not
   a tactic.** Name the preferred spelling, which is whichever the obligations are stated in,
   prove the crossing once in a named lemma, and arrive in it. Three ad-hoc normalisations in
   one proof is the signal that the convention is missing.

The habit that catches the first four early is to ask what the *goal's* shape is before writing
the lemma, rather than writing the lemma one would like and making the goal fit.

## A sixth, which the elaborator cannot catch: a disjunct that is true outright

*Entry 7 of the traps list; the index is under **The traps, consolidated** above.*

The five above are proofs that will not go through. This one is a proof that does, and a
theorem that says nothing. `RandomiserProvenance.randomiserBad_source` was first stated with its
overlap case as a bare equation,

```
∃ payload framed, randomizerInput prf pk.seed payload = messageInput prf pk framed
```

and `RandomizerGate.messageInput_eq_randomizerInput` exhibits a witness for *every* seed and
public key, so the disjunct held for every run and the theorem was vacuous. Nothing complained:
it elaborated, it was proved, its `#print axioms` was clean, and it even composed — the
downstream bound would have been honest about a case that always fired.

The cause is worth naming because it is easy to repeat. The case came out of the proof carrying
three things: an equation, *which request* the digest belonged to, and that the randomiser
behind it was `SK.prf`. The equation is the part that reads like the mathematical content, so
it is the part that got written down; the other two were existentially quantified away. But the
equation is the *consequence* and the coincidence is the *cause*, and once the cause is
quantified away all that is left is a fact about the two byte formats overlapping, which is
unconditional.

The habit that catches it: for each disjunct of a case split, ask what would have to go *right*
for an adversary to land in it, and check the statement mentions that. If a case is supposed to
cost `2 ^ -128`, something in it must be pinned to a single value — here, that the randomiser
*is* `SK.prf`, and which logged request or which forgery it came from. A disjunct with no such
pin is not a case, it is a tautology. The cheap mechanical check is to try to prove the
disjunct on its own, with no hypotheses; `nonvacuous`-style `example`s against an empty log and
an empty record are two lines each and would have caught this immediately.

## The coverage cap is a fact about the scheme, not slack in the proof

`CoverageTail`'s charge carries `qm ≤ 5 * 2 ^ 62`, inherited from the load-potential
concentration behind `ForsLeaveOneOut`. It looked like an artefact to be removed. It is not.

`qm` bounds the growth in `CombinedCharge.IsMessageInput` — *every* message-class input,
including the ones an adversary makes under randomisers of its own choosing. At around `2 ^ 70`
such digests spread over the `2 ^ 63` FORS instances the per-instance load is about `2 ^ 7`, a
given digest's fourteen positions are covered by the others with probability about
`(2 ^ 7 / 2 ^ 12) ^ 14 = 2 ^ -70`, and over `2 ^ 70` candidate targets the coverage event
becomes likely. So no bound of the form `qm / 2 ^ 128` can hold for unbounded `qm`, and the cap
is where the argument correctly stops. Nor is there a large-`q` escape: the target is still far
from trivial at `q = 5 * 2 ^ 62`.

What is wrong is the class, not the cap. **Coverage by an adversary-randomised digest discloses
nothing.** Only the signer's own digests reveal FORS secrets, which is exactly why
`CacheAvailability.signedAt` counts a digest as disclosing only when the `PRF_msg` entry is in
the cache. Charged at the disclosing class, `qm` counts signer-randomised digests, those are
bounded by the signing requests, and `signingLimit = 2 ^ 64` sits inside `5 * 2 ^ 62` with a
quarter of `2 ^ 64` to spare.

The gate is the same one `RandomizerGate` already charges: an adversary can manufacture a
disclosing digest by querying `randomizerInput SK.prf PK.seed M`, which carries the secret seed
in the clear. So the disclosing count is the signing requests plus the gate queries, and the
gate queries are paid on the other half.

## The two halves share the record by class, not by a shared rate

**Superseded** in its instantiation: there is no randomiser defect to share the record with any
more. The distinction it draws — two charges may share a *count* without sharing a *rate* — is the
live part, and is what `SharedJoin`'s two parts still rest on.

The input half and the randomiser defect are charged against one budget, and there are two ways
to read that. The one that does not work is a single hit predicate whose own rate is one unit:
the two events are not even about the same randomness — the sensitive hit is over the cell
table, while the gate's secret is drawn after the run and charged by deferral — so no single
draw carries both.

What they share is the **count**. A canonical input begins with `PK.seed` and a `PRF_msg` input
with `SK.prf`, so no input is both unless the two seeds coincide, which is one unit of `2 ^ -128`
already in the allowance. `RandomizerGate.card_add_card_le` is that statement: the canonical
part and the `PRF_msg` part of a record add to at most the record's size. The two charges are
then taken separately, each against its own part, and added — the sum of the two expected counts
is one expected record length, which is the `(q - 512) + 259` the obligation allows.

## What the theorem now rests on

**Superseded** by *Where the proof stands*, at the top: the split is two-way now, not three-way,
and `ReplayGate.RandomiserBad` is no longer one of the events.

`Obligations.target_of_charges` instantiates the target at the three events the split actually
produces — `RoutedSplit.AnswerBad`, `RoutedSplit.InputBad`, `ReplayGate.RandomiserBad` — so the
whole of `HasTotalSecurityBits .strong 127` reduces to three statements about the warmed tail.
The split itself is proved (`ReplayGate.cases_of_win_charged`); what is left is one fact about
the game and two bounds.

* **`AnswerCharged`** — the two answer-side charges added against one budget. Needs the coverage
  charge re-pointed at the disclosing class, so that its `5 * 2 ^ 62` cap is discharged by the
  signing limit, and the two-class counter that lets the structural and coverage limits be
  combined before the uniform bound rather than after.
* **`SharedCharged`** — the input half at the record's canonical part, plus the randomiser
  defect at its `PRF_msg` part, added under one record length by
  `RandomizerGate.card_add_card_le`. The input half needs `cellSign`'s congruence; the randomiser
  half needs the provenance of a `PRF_msg` entry and then the deferral.

`LogFaithfulGame` was the third and is now proved, unconditionally — `SigningFaithful`. The
invariant that made it go through is faithfulness *quantified over every later cache*, because
faithfulness at the cache in hand is not preserved as the cache grows.

Nothing above is a design question any more. Each is a proof.

### The three classes the shared budget pays for

**Superseded.** The three-way classification needed `SK.prf` to name two of its parts, and a
deferral reads its count before the secret is drawn. The split is now `aiming ⊎ message-class`,
which names only the walk.

The shared half ends up charging three things, and they have to be made exclusive before their
counts are added. A record entry is canonical — `PK.seed` first — or a `PRF_msg` input at the
real seed — `SK.prf` first — or a message-class input. The first two are disjoint
(`RandomizerGate.card_add_card_le`), and the first and third are disjoint given the walk's own
`hpublic`. The second and third are **not**: a message input is a `PRF_msg` input at its own
randomiser read as the seed, and they coincide exactly when that randomiser is `SK.prf`. So the
three are made exclusive by priority rather than assumed disjoint, after which

    canonical + 259 claims + `PRF_msg` + message-class ≤ (q - 512) + 259

which is the obligation's budget, since each class counts a subset of the adversary's charged
queries.
## The answer side's two classes add on one counter, and what is left to pay

`prob_answerBad_le_of_classes` asked for `qs + qm ≤ q - 2 ^ subtreeHeight` with `qs` and `qm`
fixed numbers. That hypothesis is not dischargeable and never was. Each is a *uniform* bound on
one class's growth, the split between the classes is chosen by the adversary run by run, and
the only pair that works on every run is `budget, budget` — the target twice over. The fault is
not the numbers; it is that the uniform bound is taken before the sum.

`ClassExpectation.prob_bad_or_coverage_le` takes it after. The machinery is three steps and
none of them is probabilistic:

* `ClassGrowth.splitCost` charges the class to one slot of the `Counts` counter and its
  complement to another, so one run carries both counts. `classCost` kept one class and
  discarded the other, which forced the two sides onto two differently instrumented runs, and
  counts on two runs do not add.
* `ClassGrowth.countAllHashes_eq_readOff` says the split-counted run *is* the
  all-hashes-counted run: any linear readout of a counter that recovers each query's hash cost
  recovers `countAllHashes`, and summing the two slots is such a readout. So the split is a
  resolution of the existing count, not a second experiment, and the existing budget bounds the
  two parts together.
* `ClassExpectation.add_le_of_shared_budget_const` adds the two expectations and applies the
  budget once, at the end.

`prob_bad_le_expected_cost` and `growthOn_le_count` are the single-class charge and growth bound
restated at an arbitrary counter and slot. Both need only that an in-class hash call is charged
at least one unit of the slot, so one proof serves the class and its complement, and the old
`classCost` statements come back as instances.

### What the coverage clause still owes, and why averaging will not supply it

`prob_bad_or_coverage_le` takes the coverage charge as

```
Pr[cov] ≤ constant + expected (in-class count) / 2 ^ 128
```

and `CoverageTail.prob_coverage_tail_le` does not have that shape: it charges at a limit fixed
in advance, with the run's growth required to stay inside it. The two are not related by
averaging, and it is worth being precise about why, because the gap looks like a formality and
is not.

Write `L` for the recorded length and `β(n)` for the uniform-tape coverage probability at
length `n`, so `β(n) ≤ 2 ^ -141 + n / 2 ^ 128`. The fixed-limit bound gives
`Pr[cov ∧ L ≤ n] ≤ β(n)` for each `n`, and nothing more. Summing over a partition by `L` pays
`β` once per cell and diverges; bounding `Pr[L > n]` by Markov costs `E[L] / (n + 1)`, which is
only small when `n ≈ 2 ^ 128`, by which point `n / 2 ^ 128` is one. Neither is a near miss.

The reason is visible in what the lazy-sampling route through `DigestTape.prob_prefix_le`
retains about the recording. It retains `Pr[w ⊑ record] ≤ 2 ^ -128 |w|` for each fixed word `w`,
and that alone is consistent with a process that puts *all* of its mass on bad words of one
length: such a process has `Pr[cov] = β(n)` with `E[L]` as small as `n · β(n)`, and
`2 ^ -141 + E[L] / 2 ^ 128` is then far below `β(n)`. No real run behaves that way, because
reaching length `n` leaves the word uniform — but uniformity *conditional on the length* is
exactly the fact the union bound over a `Finset` of bad words discards, and it is what the
expectation form needs.

The lemma that wants it already exists. `ForsLeaveOneOut.independent_tape_mixture_coverage_le`
charges `2 ^ -141 + E[uses] / 2 ^ 128` for a causal policy that may depend on auxiliary
randomness independent of the tape, and the policy this needs is "coordinate `j` is a real
recorded answer" — causal in the tape prefix once the run's coins and its non-class answers are
the auxiliary randomness. So the statement is true and the charge for it is already paid; what
is missing is a factorisation of `DigestTape.recordedRun` into that auxiliary randomness and a
uniform tape. `DigestTape` deliberately avoids such a factorisation, bounding prefix
probabilities by induction instead, so supplying it is new work on the coverage induction
rather than a restatement of it.

Until then `AnswerSide.prob_answerBad_le_of_budget` carries that one hypothesis and no `hsum`,
and concludes `budget / 2 ^ 128 + constant` — at `budget = q - 2 ^ subtreeHeight` and
`constant = 1 / 2 ^ 141`, the bound the target reads.

## Both sides of the answer half have to be in expectation, and why no re-capping reaches it

The two-class counter put the structural side in expectation. It is worth writing down why that
is not half the job but all but one step of it, since the arithmetic looks as though a tighter
uniform bound on the other side would do.

Pathwise `inside + outside ≤ count ≤ q - 512`. With the structural side in expectation that
gives `E[outside] ≤ q - 512 - E[inside]`. If the coverage side keeps a uniform limit `trials`
with `inside ≤ trials` on every run, closing the sum needs

    E[outside] + trials ≤ q - 512,

which forces `trials ≤ E[inside]` — a uniform bound on a quantity sitting below that quantity's
own mean. So no choice of `trials` works, and in particular uncapping `qm` by the index split,
which was necessary for its own reason, does not reach this.

What makes it the last step rather than a wall is that the expectation form already exists where
the tape is uniform: `BlockDisclosures.block_coverage_le` concludes
`1 / 2 ^ 141 + expectedUses policy / 2 ^ 128`, and only `expectedUses_le_trials` turns that into
a uniform bound. What is missing is the transport — carrying the game's recording to that tape
without discarding conditional uniformity. A union over a `Finset` of bad words is exactly what
discards it: it is consistent with a process putting all its mass on bad words of one length,
for which the expectation form is false. Real runs are not like that because reaching a length
leaves the word uniform, and that is the fact the transport has to keep.

## A charge that defers its secret cannot be read at a fixed walk

The randomiser defect is now reduced to exactly the charge that was meant to pay for it, and
that is where a shape mismatch shows up which is not about the randomiser half alone.

`RandomiserRecord.prob_randomiserBad_le_record` takes the defect at the warmed tail down to two
named events at a presentation of the tail that returns the adversary's own record:
the record meets the `PRF_msg` class at the real seed, or the digest overlap fires. The first is
literally `RandomizerGate.prob_run_randomizerInput_le`'s event — and that lemma, like every
deferral in this development, is stated at

    do let result ← run; let secret ← $ᵗ Digest; pure (result, secret)

with the secret drawn **after** the run. `SensitiveQuery.prob_probes_sensitive_le` and
`RedrawCell.prob_game_sensitive_le` have the same shape with the cell table in place of the
secret, and `TrackedQueries.prob_meets_real_le` draws its secret inside the experiment too.

`Obligations.SharedCharged` — and `Target.target_of_obligations`'s `hshared` with it — is stated
at a **fixed walk**, with the adversary quantified before it. The walk carries `SK.prf` as
`walk.1.1.2.1` and the cell table as `walk.1.2`, so both secrets those charges defer are fixed
before the adversary is chosen. `RandomiserDeferral.mem_support_withPrf` is the obstruction in
one line: every walk stays in the support when its `SK.prf` is replaced by *any* digest, with
the same cells and the same cache. An adversary whose first act is to hash a fixed
`prf ‖ seed ‖ message` makes `ReplayGate.RandomiserBad` certain on the walk carrying that pair,
at `signed = []`, while the obligation allows `(q - 512 + 259) / 2 ^ 128`. The input half is the
same story at `walk.1.2`: `SensitiveQuery.Sensitive` is a guess at one coordinate of the cell
table, and the table is the walk's.

**The repair for the randomiser half is cheap, because nothing in the walk reads `SK.prf`.**
`Presample.worldWarmup` is called at `sds.2.2` and `sds.1` only, so the draw commutes past the
whole warm-up — `RandomiserDeferral.evalDist_resample_prf` — and
`RandomiserDeferral.probEvent_le_of_prfTail` is `WarmedGame.probEvent_le_of_tail` with that one
draw moved inside the tail. Everything else about the walk stays fixed before the adversary
runs, so every charge that reads the walk as a fixed table reads it unchanged;
`mem_support_withPrf` carries `AnswerCharged` across unaltered. What moves is
`Target.GoodWalk`'s first clause, the seed coincidence, which becomes an event inside the tail
at the `2 ^ -128` the allowance already carries for it.

**The input half needs the same move at the cells, and that one is not free**, because the
walk's cache depends on the secret seed through the PRF nodes' canonical inputs.
`WarmedCharges.blindCache_indep_of_secret` is the lemma that makes it possible — the blind cache
is the same table for every secret — and `RedrawCell.prob_game_sensitive_le`'s own shape, with
`cells ← $ᵗ Cells` drawn inside, is where it has to land. So `SharedCharged` has to be restated
with both secrets deferred, and `target_of_obligations` reproved against it.

**And deferring is still not sufficient for the randomiser half.** With `SK.prf` drawn inside
the tail the run is not independent of it: the signer derives each randomiser by querying
`Hashing.randomizerInput SK.prf PK.seed framed`. The answers there are a random oracle's at
inputs nobody else has queried — which is the event being charged — so the real game and the one
whose signer draws its randomiser fresh are identical until that event, and the *equality* of
its probability in the two is what keeps the charge from being paid a second time. That equality
is the analogue of `TrackedQueries.prob_meets_eq` for two **handlers** agreeing off a set rather
than for two caches; `BlindComparison` has nothing at that generality, and writing it is a file
of its own, not a step inside a proof.

## A charge that defers its secret cannot be read at a fixed walk

*A second pass at the section above, written without noticing the first. Both are kept: they reach
the same rule by different routes, and the rule — a charge may be read at a fixed walk exactly
when the randomness it spends is drawn after the walk — has since been hit a third time, at
`SharedJoin.hinput_of_probesIn`.*

The shared obligation was stated per walk: for every walk in the support, a bound on the tail's
probability. That form is **false**, and the counterexample is short. Conditioning on the walk
fixes `SK.prf` and the cell table. The adversary is quantified before the walk, so it may be one
that hashes a constant `PRF_msg` input; on the walk whose `SK.prf` is that constant — which is in
the support, and good — the entry is in the final cache with no signing request behind it, so
the defect holds with probability one while the obligation allows `2 ^ -128` a query.

The same argument breaks the input half: `Sensitive` is a guess at one coordinate of the cell
table, and the table is the walk's.

Two threads reached this independently, from the two halves, which is what settled it. The clue
in both cases was the same: every deferral in this development draws its secret *after* the run,
and a secret the walk has already drawn cannot be deferred past anything.

The repair is to read the shared obligation on `Target.pairedRun` — the walk and the game taken
together, with the walk's value retained — and to keep `GoodWalk` as a conjunct of the event
rather than a hypothesis about a parameter. The arithmetic does not move: the walk's own two
coincidences are the same two units, now paid inside the paired run by `prob_bad_walk_paired`.

**The answer side is untouched and stays per walk**, and the reason is worth stating because it
is what makes the two halves genuinely different. Its charges are guesses at the *tail's own
fresh answers* — a collision with a canonical target, a coverage pattern among digests drawn
during the run. No choice of adversary biases an answer that has not been drawn. A charge may be
read at a fixed walk exactly when the randomness it spends is drawn after the walk.

## The whole budget, charge by charge, and why every term has a home

**Superseded** by *Where the proof stands*, at the top. This is the four-term accounting: the
randomiser defect's term and the signer's coincidence are both gone, and the shared side is now
two terms against the record's aiming and message-class parts. Read it for the method — write the
accounting into the statements rather than trusting the margin — which still holds.

The target allows `q / 2 ^ 127`, which is **two units of `2 ^ -128` per counted query**. Six
charges are now in flight and three of them are stated against counts loose enough to look as
though they do not fit. They do, and this is the accounting that says so. Write it into the
statements rather than trusting the margin: the margin is 247 units and every one of these terms
is proportional to `q`.

Let `work` be the adversary's own charged queries, `req` the served requests, and note
`work + req + 2 ^ subtreeHeight ≤ q`, since key generation's subtree is charged and each request
costs at least one counted hash.

**The answer side spends one unit per query, and its two charges partition the queries.**

* structural collisions — the growth *outside* the message class;
* FORS coverage — the growth *inside* it.

They add to the run's own count, which is at most `q`. Nothing else is charged there.

**The shared side spends one unit per query too, and its four charges partition the record.** A
record entry opens with `PK.seed` (canonical), with `SK.prf` (`PRF_msg`), or is message-class;
made exclusive by priority these three are disjoint, and the fourth charge is not about the
record at all:

* the input half — the canonical part, plus the forgery's 259 claims;
* the randomiser defect — the `PRF_msg` part, plus one for the forgery's own digest input;
* the ordering defect — the message-class part, which is where the *right* recording lives:
  the signer queries its `PRF_msg` input before its digest, so a signer's digest is disclosing
  when made and is recorded on the left, and the right recording holds only the adversary's;
* the signer's coincidence — **two per served request**, not one, and not one per query.

So the shared side costs at most `work + 259 + 2 · served`, and since a served request costs at
least two counted hashes (`AdversaryQueries.work_add_keygen_add_served_le_total`), that is
`≤ (q - 2 ^ subtreeHeight) + 259`, which is its obligation on the nose.

**Two corrections to the line above, both found by trying to prove it.**

*It is two per served request, not one.* A served request names **two** inputs of the `PRF_msg`
class at the real seed, not one: its randomiser's input, and its digest's — because a message
input *is* a `PRF_msg` input at its own randomiser read as the seed. The second is of the class
exactly when the coincidence has already fired at that request, so it is only ever spent on a
request that has already lost; but it cannot be dropped, because the growth bound would then be
false, and a false growth bound is worse than a rate twice as large. The `2` is what makes the
fit exact rather than slack: `work + 2 · served + 2 ^ subtreeHeight ≤ q` is the two-hashes-per-
request fact, and the budget has no room for a third unit per request.

*The forgery's `+ 1` is not a separate term.* The verifier's own queries are charged to
`counts .verification`, hence to `work`, and the recorded presentation records them, so the
forgery's digest input is already inside the record's `PRF_msg` part. Counting it again is what
pushed the sum one unit over `q - 253`. Taking the record from the presentation that records the
verifier removes the term and the four add to the obligation exactly.

**And a third thing the line cannot say.** The signer's coincidence is attributable to a
*query*, not to a request, at a fixed walk: an adversary with `SK.prf` hardcoded may query
`randomizerInput SK.prf PK.seed m` for `N` framings of its own, keep the one whose answer
truncates to the seed, and make a single signing request on that message — the event fires at
about `N / 2 ^ 128` with one request logged. What rescues the per-request shape is not the
counting but the **partition**: those `N` queries are themselves of the class and recorded, so
they fire the randomiser defect's own event, which is charged on the record. On the complement,
where no recorded input is of the class, the only in-class entries left are the signer's own,
and `2 · served` is exact. So the two terms do not merely happen to add — the branch that makes
one of them small is the branch the other one pays for.

**A fourth thing the accounting cannot be read as, found by writing the join.** The four terms
add *pathwise*, and that is not the same as four of them each being capped. The partition
`work + 2 · served + 2 ^ subtreeHeight ≤ q` holds on each run, and the split between `work` and
`served` is a property of the run — one adversary spends the budget on its own queries, another
on requests. So an almost-sure cap for each count has to cover that count's own worst run, and
four worst-case caps are four budgets, not one. `SharedJoin.prob_sharedBad_le_expected` is the
sum at the shape that works: each charge bounded by its **expected** count, the four
expectations added by `ClassExpectation.expected_add`, and the one uniform bound taken at the
end. `SharedJoin.prob_sharedBad_le` is the same sum at four constants, kept because it is what a
cap-shaped charge produces, and it is sound only when those constants bound the expectations.

This is the move the answer side already made for its coverage term, and
`ClassExpectation.prob_bad_le_expected` states the reason in general: each charge's limit is
chosen by the adversary run by run, so the only number that bounds one on every run is the whole
budget, and a pair of fixed limits can only be `budget, budget`. It applies to all four shared
charges, the signer's coincidence included — its charge holds at every constant limit, because
the growth is a conjunct of its event rather than a hypothesis, but whoever supplies that
conjunct can only supply `2 · served`, which is again a property of the run.

**What the conversion to expectations costs, and the one count it cannot reach.** Three of the
four move with no new machinery: `ClassGrowth.run_splitCost_eq_map` identifies the split-counted
run with the plain one, so a charge may be read at the instrumented presentation and the bound
carried back, which is what `SharedJoin.prob_signerHitsSeed_tail_le_expected` does for the
signer's coincidence. But `ClassGrowth.splitCost` is indexed by the **input** — one unit for a
hash call at an in-class input, whoever makes it — and the adversary's in-class call and the
signer's are calls at the *same* input. That is not an accident of the instrumentation; it is
the search attack restated. So no input-indexed cost can charge the signer's call and not the
adversary's, and what the conversion gives is the expectation of **every** in-class hash call,
pathwise at most the record's `PRF_msg` part plus twice the served requests — the randomiser
defect's allotment and the signer's together, not the signer's alone.

The overshoot lies entirely on the branch the record half already pays for: where the adversary
makes no in-class call, the in-class calls are the signer's alone and `2 · served` is exact. Two
things would close it, and neither is a missing lemma. An expectation **restricted** to a
monotone side condition — "no in-class call has been made by the adversary", which only ever goes
from true to false along a run — would be a genuine generalisation of
`ClassExpectation.prob_bad_le_expected_cost`'s induction, and the obstacle is that the condition
is not visible at the world oracle, which is blind to the caller. Or a count that can tell the
two callers apart, which an input-indexed cost cannot be and an instrumentation wrapped around
the signer's own sub-computation could: a presentation change of `RecordedTail`'s kind, whose
slot must be at least one per in-class call the signer makes and at most twice the served
requests.

**What this forbids.** No charge on the shared side may be stated against `q` or against the
whole record. Three of them currently are, or were: the randomiser defect against the record's
whole cardinality, the signer's coincidence against `q`, and the ordering defect against every
message-class query rather than the recorded ones. A fourth form is forbidden too, and it is the
one that looks sharpest: no charge on the shared side may be stated against a count that is not
bounded by the budget — `signingLimit` alone would make the signer's coincidence a constant
`2 ^ -64`, which is far larger than `q / 2 ^ 127` at small `q`. Each is true and each is a factor of two or
three too loose to add. The sharp form is the one above, and it is the one the statements have
to carry.
## The coverage charge in expectation: what it needs, and what it does not

The two-class bound takes the coverage clause as `constant + expected inside count / 2 ^ 128`
and `CoverageTail` supplies a fixed limit instead. The gap is not closable by averaging, for the
reason recorded above. This is what closing it actually requires, written down before the work
rather than after, because the first estimate of it was wrong by a wide margin.

### The direct induction is not the cheaper option

Charging the coverage clause at the recorded run, without going to a tape, means proving the
run-level analogue of `ForsLeaveOneOut.selected_local_hit_le`:

```
Pr[run reaches target j ∧ good ∧ Covered(block, target j)] ≤ Pr[run reaches target j] · 2 ^ -128
```

That lemma is proved at the tape by *resampling coordinate `j`*, which is legitimate there
because `hrevealed` holds: the disclosure set is an index-restricted function of the tape and
does not read `j`. At the run it does read `j`. Resampling the `j`-th target answer changes what
the adversary does next, hence which signing requests it makes, hence the block — so the
disclosure set moves and the hypothesis fails. The symmetry the argument runs on is a property
of the tape, not of the run, and a direct induction would have to recover it by hand. That is
strictly more work than getting to the tape, not less.

### What the tape actually needs, which is less than a derandomisation

The obvious reading of "get to the tape" is `ForsLeaveOneOut.independent_tape_mixture_coverage_le`:
auxiliary randomness drawn first, a *function* from it to a causal policy, a uniform tape second.
Supplying that means presampling every random choice the run makes — including the adversary's
`unifSpec` coins, whose answer type varies with the query, so the coin tape is a dependent
object. That is a derandomisation of the whole game and it is not worth its price.

It is also not needed. Reading the resampling argument for what it uses rather than for how it
is packaged: the policy never has to be a function of anything. What has to hold is that the
three parts of the event behave correctly when the `j`-th target coordinate is overwritten with
a fresh value —

* the disclosure set and its load condition must not move. They do not, if the disclosures are
  taken from a **separate** tape drawn independently, which is exactly what the index split
  already arranges: the block is the left recording and the targets are the right one.
* the coverage test must read the `j`-th coordinate and nothing else of the right tape. It does.
* "the run reaches target `j`" must have the same probability under the overwrite. It does, by
  causality: the run reads right-tape position `j` only when it makes its `j + 1`-st target
  query, and whether it makes that query is settled before.

Causality is a statement about *conditional* probabilities and survives the run keeping its own
randomness inline. So the coins and the non-class answers never have to be presampled, and the
factorisation is needed only for the two class tapes. The chain is then

```
Pr[cov] ≤ Pr[¬good(left)] + Σ_j Pr[reaches j ∧ good(left) ∧ Covered(disc(left), right j)]
        ≤ 2 ^ -141 + Σ_j Pr[reaches j] · 2 ^ -128
        = 2 ^ -141 + E[right length] / 2 ^ 128
```

the last step because `Σ_j Pr[length > j]` is the expectation, which is where the per-run weight
that averaging destroys is kept: it is carried by `Pr[reaches j]`, one factor per coordinate,
exactly as `expectedUses` carries it at the tape.

### The parts, and the one that is risky

1. A two-headed tape-reading variant of `SplitPrefix.recorder`: a fresh class query takes its
   answer off the head of its own tape instead of drawing one, with a fresh draw as the fallback
   when a tape is spent, so the factorisation needs no side condition. Everything else —
   coins, cached queries, fresh out-of-class queries — keeps drawing inline.
2. `𝒟[paddedRun] = 𝒟[left ⊗ right >>= rest]`, by induction on the computation. Four of the five
   cases are the answer-irrelevant commute, for which
   `OracleComp.DeferredSampling.evalDist_step_commute_tape` is the generic form; the two drawing
   cases splice a head off a uniform tape, which is the list-at-a-time shape `DigestTape.padding`
   already has. **This is the part that can go wrong**, and the framework is less help than it
   looks: `Factorizes` and `evalDist_step_commute_tape` have no instance anywhere in VCVio, and
   the worked example their docstrings name does not exist in the package. The vocabulary is
   there; the content is not.
3. Causality: overwriting an unread right-tape position does not change the law of the run's
   prefix. An induction in the style of `DigestTape.recorder_cache_value_persists`.
4. The mixed-space resampling lemma — `selected_local_hit_le` with the disclosure set and its
   load condition taken from the independent left tape and the policy replaced by a causal
   event. The existing proof carries over nearly verbatim.
5. Assembly: the load failure on the left tape is the existing `2 ^ -141`; the coverage event of
   the cache is carried to the recordings by the transport that already exists; disclosures are
   taken from the whole left tape including its unused suffix, which only adds disclosures and
   so is sound.

Items 1, 3, 4 and 5 are each in the range the existing modules occupy. Item 2 is the one with
real risk, and it is the one to attempt first: if the factorisation does not go through, nothing
downstream of it is worth writing.

## The coverage charge in expectation: what it cost

The estimate above was right about the route and wrong about the price. The factorisation was
named as the part with real risk and the part to attempt first. It was attempted first and it
did not resist: `TapeFactor.evalDist_tapeRun` and `evalDist_splitTapeRun` are the one-block and
two-block identities, and between them they took one afternoon rather than the module-sized
effort the estimate allowed for.

Two things account for the difference, and both are worth keeping in mind the next time
something is costed by the shape of its statement.

**The fallback removes the side condition.** A tape-reading oracle that *draws for itself* once
its block is spent factorises for every block length, with no hypothesis that the block is long
enough and nothing owed when it is too long. The estimate assumed a "never runs out" invariant
threaded through the induction from the budget; there is none to thread. The uniform cap comes
back later, as a cap on the *count*, which is where it was always allowed to be.

**Causality is not determinism.** The obvious reading of
`ForsLeaveOneOut.independent_tape_mixture_coverage_le` asks for a *function* from auxiliary
randomness to a policy, and supplying one means presampling every draw the run makes — including
the adversary's `unifSpec` coins, whose answer type varies with the query. Reading the
resampling argument for what it uses instead, the three things that must survive overwriting one
target cell are: the disclosure set (which sits on the other block), the coverage test (which
reads that cell and nothing else), and the selection. The selection is the only one that touches
the run, and what it needs is that its *probability* is unchanged — `probEvent_length_set` — not
that it is a function of anything. So the coins and the out-of-class answers never leave the
run, and only the two class blocks are front-loaded.

What came out is `TapeFactor.prob_exists_hit_le_expected`: a run whose disclosing block is good
pays, for the event that some cell of its target recording is hit by that block, its expected
recording length times the rate. The per-cell factor is `prob_selected_hit_le`, which is
`ForsLeaveOneOut.selected_local_hit_le` at the run, and summing the factors is where the
expectation appears — `∑ index, Pr[reached index]` is an expected length, not a block length.

### What is left

The machinery is generic in the two class tests, the block predicate and the hit relation.
Connecting it to `CoverageTail` is instantiation, not new argument:

* carry the game's recorded run to `blockRun` through `evalDist_splitTapeRun`, which is a
  distribution identity and so moves any event;
* instantiate the block predicate with the load condition and `Pr[¬good]` with
  `BlockDisclosures.block_bad_load_probability`, the left block being uniform by construction;
* instantiate the hit relation with `ForsCoverage.Covered` and its rate with
  `ForsCoverage.fresh_coverage_le_of_loads`;
* read the game's coverage event as a hit at a cell, for which `rightOf_getElem?` is the bridge:
  the `index`-th recorded target answer *is* cell `index` of the block.

Then `ClassExpectation.prob_bad_or_coverage_le` takes it and the answer side has no hypothesis
left but the budget.

## Where the two obligations stand

**Superseded** by *Where the proof stands*, at the top. Its shared half says four terms; there are
two. The paragraph on `PotentialCharge.prob_fired_le` — a potential on the state paid down against
a gauge read off the state — is still live and is why that lemma exists.

`Obligations.target_of_charges` reduces the theorem to `AnswerCharged` and `SharedCharged`.
Neither has an open problem left; what remains in both is instantiation.

**The answer half.** `AnswerSide.prob_answerBad_le_of_budget` wants the budget and one coverage
bound in expectation form, and that bound is now proved — `TapeFactor.prob_exists_hit_le_expected`
charges the coverage event at the *expected* recording length rather than at a cap. Two things
made it cheap, and both are reusable. A tape-reading oracle that draws for itself once its block
is spent factorises for every block length, so there is no "long enough" side condition to thread
from the budget. And causality is not determinism: the resampling needs only the *probability* of
the selection to be unchanged, so the run's coins and out-of-class answers never have to be
front-loaded, and only the two class blocks do.

**The shared half.** Four terms, partitioning the record by class plus one per request; the
accounting is above. The input half has its congruence (`cellSign`); the randomiser defect has
its provenance and needs the handler-level identical-until-bad for the signer's randomiser; the
ordering defect has its general charge (`PotentialCharge.prob_fired_le`) and needs instantiating.

That general charge is worth naming for its own sake: a potential on the state paid down against
a gauge read off the state, which covers "a fresh answer landing in a set the cache named
earlier" — the shape neither `prob_badWithin_le` nor `SecretGuessCharge` reaches, and the third
place in this development that wanted it. The count has to be a gauge on the *state* rather than
a counter on the queries: with the counter in the value, a step's own increase can only be
recovered by cancelling across an `ℝ≥0∞` inequality, which needs a finiteness nothing supplies.
## The walk deferred is a drawn table, and that is all it costs

`Obligations.SharedCharged` is now stated at `Target.pairedRun`, the walk and the game in one
measure. The charges want something that looks different — `RedrawCell.prob_game_sensitive_le`
begins `cells ← $ᵗ Cells; pad ← $ᵗ Padding` — and the two are the same presentation.
`CanonicalGraph.Programming.warmup_seed_uniform` is why: with the secret seed drawn, the walk's
cells and cache *are* a uniform cells-and-padding pair read through `cacheFrom`. `WalkTable`
carries that across to the paired run, and `WalkTable.probEvent_pairedRun_le` is what the
obligation now reduces to — a bound for each fixed `SK.prf` and public seed, with the table and
the secret seed it carries still in the measure.

**The secret seed is recovered, not re-drawn.** The walk's value carries it and the table's law
does not, so the presentation reads it off the table's own `secretSeed` cell. That is sound only
on the walk's support — the traversal never overwrites that cell — so the step needs a
support-wise congruence under a bind, which VCVio does not have;
`WalkTable.evalDist_bind_congr_support` is four lines and is the only place the support fact is
used.

**`WarmedGame.seeds` draws the seeds in the wrong order for this.** It draws the secret seed
first, and the table's law wants it drawn last, after the public seed its canonical inputs
mention. The draws are independent, so `DeferredSampling.evalDist_bind_comm` twice is the whole
of the reordering, but the order is not an accident of presentation: fixing the public seed
before the table is what makes the charge's `publicSeed` parameter legitimate, and fixing the
secret seed is what the obligation may not do.

**Nothing stated per-walk has to be restated.** `WalkTable.mem_support_graphWalk_walkOfTable`
says a drawn table names a walk in `support graphWalk`, so `WarmProbes.length_record_le_of_budget`,
the walk's cache being clean, and every other per-walk fact apply at the new shape unchanged.

## The input half cannot be charged at the flag

`TableTail` now takes `WarmedGame.tail` at a drawn table all the way to the handler's own run,
in six equalities and no bound. What it hands over is a run of the linked game under
`OpenCache.lazyProgram` at total availability, started from nothing, with the record and its
count as parameters — which is the presentation both of the charge's two endpoints are stated
at. They are not the same endpoint, and the input half needs the second.

`RedrawCell.prob_game_sensitive_le` bounds the probability of the **flag**, and a flag fires
only on a query the run makes. The input half's event does not: `RoutedSplit.InputBad` is about
the cells the *forgery claims*, and `ClaimedProbes.claimedCandidatesOf` builds one candidate per
claimed cell from the signature, not from the run's probes. That is exactly why the budget gives
the half `259` beyond the canonical part — a term that would be unnecessary if the claims were
queries.

So the input half's charge is the record form: `SensitiveQuery.prob_record_hit_le` over

    WarmProbes.warmProbes warm (handler's record) ++ WarmProbes.claimedEntries …

whose length `WarmProbes.length_record_le_of_budget` bounds by `(q - 2 ^ subtreeHeight) + 259`.
The filter is not optional either — the honest phase's probes are not in the budget, and
charged against the handler's whole record the half would come in at `2 ^ -64`.

**What stands in the way is a hardcoded projection, and the two halves of the record are not
equally easy to free.** `ChargedProbe.sum_weighted_le` already takes the record as a function of
the run's result, but `RedrawCell.prob_charged_index_le` and `prob_sensitive_run_le` spell it
`z.2.1.2.1` — the handler's own list — in both the event and the `aiming` count.

The filtered probes should follow the existing argument unchanged. The stalling step underneath
is `StalledRun.expectation_stalled_eq` applied at the weight `fun p => if ∃ entry ∈ p.1.2.1, …`,
a function of the **handler's state alone**, and `ChargedProbe.withFlag_charged_quiet` is what
discharges its quietness: a stalled step adds an entry that is not charged against the index. A
filter of that list is still a function of the state, and an entry that is not charged does not
become charged by being filtered, so the same quietness argument applies.

The forgery's claims do not have that shape. `WarmProbes.claimedEntries` reads the run's
**value** — the forgery and the final cache — and a weight that reads the value is not what
`expectation_stalled_eq` takes. So the claims are either appended after the stalling step, where
they are a constant `259` the sum does not have to carry, or the stalling lemma has to be
restated at a weight over the whole result. Which of those is right is the first thing to settle
before generalising, and it is not settled by reading the statements.
## Two things that make a tape factorisation cheap, and one that VCVio does not give you

These came out of the coverage charge but none of them is about coverage. Anything in this
development that wants to move a run onto a tape drawn in advance will meet all three.

**A tape-reading oracle that draws for itself when its tape is spent factorises for every tape
length.** The expensive-looking version of a factorisation carries a "the tape is long enough"
side condition, threaded through the induction from whatever budget bounds the run's queries.
There is nothing to thread. Give the tape-reading oracle a fallback — once its block is empty it
draws its own answer, exactly as the un-factorised oracle would — and the identity holds for
*every* length, with no hypothesis and nothing owed when the block is too long.
`TapeFactor.evalDist_tapeRun` and `evalDist_splitTapeRun` are stated that way. The uniform cap
comes back later as a cap on the *count*, which is where a cap is harmless; put it in the
identity and it is a cap on the charge, which is the thing being avoided.

**Causality is not determinism, and the difference is a whole layer.** Read
`ForsLeaveOneOut.independent_tape_mixture_coverage_le` literally and it asks for a *function*
from auxiliary randomness to a policy. Supplying one means presampling every draw the run makes,
including the adversary's `unifSpec` coins, whose answer type varies with the query — a
derandomisation of the game. But the resampling argument underneath needs only that three things
survive overwriting one tape cell: the disclosure set, which can be put on a separately drawn
block; the test, which reads that cell and nothing else; and the selection of the cell. Only the
selection touches the run, and what it needs is that its **probability** is unchanged
(`TapeFactor.probEvent_length_set`), not that it is a function of anything. A conditional
statement survives the run keeping its own randomness, so the coins and the out-of-class answers
never leave it and only the class blocks are front-loaded. This is what separated the real cost
from the estimate, by about an order of magnitude.

**`DeferredSampling.Factorizes` and `evalDist_step_commute_tape` have no instances anywhere in
VCVio, and the worked example their docstrings name does not exist in the package.** The
vocabulary is there; the content is not. `evalDist_step_commute_tape`'s `proj`/`tapeCont`
signature did not fit the two-headed state shape here either, and doing the induction directly
on `evalDist_bind_comm`, `evalDist_bind_congr_left` and `evalDist_bind_const_neverFails` was
shorter than bending the state to fit. Budget against those three, not against the framework.

Note for whoever takes the *input* side's deferral — the until-first-hit seed, recorded under
"What is not done" as a `Factorizes` obligation. It is a different shape from this one (a secret
drawn **last**, not answers read off a block drawn **first**), so `TapeFactor` does not discharge
it. The two observations above should still apply, and the three primitives are the same.

## `SeedRandomised` has a fourth source, and it is the signer's own randomiser query

`SplitWitness.SeedRandomised prfSeed pk cache` — the cache holds a message input that is also a
`PRF_msg` input at the real seed — was introduced to narrow the coverage recorder's target test,
with the residue to be folded into the shared side as "the adversary's query, the signer's digest
query, or the verifier's digest query". There is a fourth party, and it makes the event cheap.

The signer's **randomiser** query for a request whose frame is `PK.root ‖ M` is made at
`Hashing.randomizerInput SK.prf PK.seed (PK.root ‖ M)`, and by
`RandomizerGate.messageInput_eq_randomizerInput` that byte string *is*
`Hashing.messageInput SK.prf pk M`. So it is a message input whose randomiser is `SK.prf`, and
it is in the cache because the signer put it there. The frame is legal whenever `PK.root`'s
leading byte is zero, which is `FramingClosure.prepend_digest_exists_frame`. An adversary that
reads `PK.root`, sees a zero leading byte and asks for one such signature makes `SeedRandomised`
hold outright, so `Pr[SeedRandomised] ≥ 2 ^ -8` for that adversary and no `2 ^ -128` charge
covers it.

**It is in neither of the two things the shared side charges.** The record is the adversary's
own queries and the verifier's — `RecordedQueries`' handler records at exactly those two places,
and the signer's hashing goes through `liftM` into the base monad, invisible to it. And
`RandomiserProvenance.SignerHitsSeed` asks in addition that the *answer* truncate to the seed,
which this case says nothing about.

`RandomiserRecord.recordMeetsPrfClass_of_cached` is the fold with that party named and excluded:
a cached `PRF_msg`-class input that is **not** `RandomiserRecord.SignerRandomiserInput` — not the
`PRF_msg` input of a request the log names — is in the charged record or gives `SignerHitsSeed`.
It is stated at `RandomizerGate.PrfClass` rather than at `SeedRandomised`, which is stronger and
is what both consumers want.

What the answer side needs is therefore a target test narrowed by the *excluded* class rather
than by `SeedRandomised`: the signer's own randomiser inputs are cached message inputs that
disclose nothing, since their answers are randomisers and not digests, and the coverage argument
has no reason to count them. Narrowing by "message input, `PRF_msg`-class, and not a served
request's own `PRF_msg` input" is the test that both excludes them and leaves a residue the
shared side can pay for.

**Third time for the same root cause.** `PRF_msg` and `H_msg` are one function on byte strings in
this model, as they are in FIPS 205 for the SHAKE parameter sets, and the two formats are
distinguished only by what their first block happens to be. Every statement that says "this
cached input is of class X" has to be checked against the possibility that some *other* party
wrote it under the other reading. Two such statements have already been repaired; this is the
third.
## The claims need blindness too, and the weight that carries it is zero rather than frozen

The input half's charge is now at an expectation — `RedrawCell.prob_sensitive_run_le_expected`
weighs a run by whatever bounds its own aiming probes run by run, and
`prob_sensitive_run_le_canonical` takes that weight to be the record's canonical part, which is
a whole class of inputs and so a count an input-indexed cost can report. The `259` claims are a
separate term added after it.

**That term is not free of the stalling machinery, and this is exactly where.** A claimed
candidate is charged against the cell its address names, and the per-candidate rate is `2 ^ -128`
only for a run whose law does not depend on that cell. The real run's law does depend on it —
the handler serves the cell whenever its node is available — so the chance has to be read at the
*stalled* run, exactly as the probes' does. What the claims cannot reuse is the step that
transports the event there: `ChargedProbe.prob_charged_stalled_eq` goes through
`StalledRun.expectation_stalled_eq`, whose weight is a function of the handler's **state**, and
a claim is a function of the run's **value** — the forgery — and of the final cache.

**The way through is not to generalise that lemma.** Its hypothesis is that a quiet step leaves
the weight where it found it, which a value-dependent weight cannot even state. But the claims
do not need it: a claim targets an index only if that index is *unavailable at the cache the
claim carries*, which is the final one, and availability only grows — so once the stall has
fired the index is available at the end and no claim targets it. The claims' weight is therefore
**zero on a frozen run**, not frozen. That is a different statement about `stalled`, with both
sides zero, and it can be proved beside `expectation_stalled_eq` without touching it.

## The budget does not close as decomposed, and why disclosure is the cause

Adding the charges up on a particular run showed the decomposition spending more than the target
allows, and the run is short. An adversary queries `Hashing.messageInput r_i pk M` for `N`
distinct randomisers at **one** message, then asks for a single signature on it. Then `q ≈ N`,
and three terms each spend about `N / 2 ^ 128`: the answer side's coverage, the shared side's
record charge, and the ordering defect. Three units a query against a target of two.

The first instinct — re-apportion, or tighten the loosest term — does not work, and the reason
is worth keeping. **Two of the charges are real and tight.** The seed guess, "some record entry's
first block is `SK.prf`", is tight because an adversary can simply try `q` guesses. The late
randomiser, "some `PRF_msg` answer truncates to a randomiser already named at its own message",
is tight because the run above realises it. Together they are the whole target, and a term of one
full unit does not fit in what is left of one unit however small the other becomes. Coverage has
real slack — with the disclosing block capped by the signing limit its true per-target rate is
nearer `2 ^ -136` than `2 ^ -128` — and the slack is useless for the same reason.

**Neither event is a forgery.** An adversary that knows `SK.prf` can predict digests but holds no
FORS or WOTS secret; one that names a randomiser the signer later derives has merely pre-queried
a digest. They are places where the extraction gives up, and the decomposition was paying for
giving up.

### The cause is that disclosure is defined by the cache

**Superseded** by the carrier: disclosure is served-indexed now, read off `HandlerCarrier.State`'s
own served set rather than off the cache, and `ServedAgreement.agreesWithLog_run` proves that set
is exactly what the log names. The diagnosis here is still the right one — it is why the carrier
exists.

`CacheAvailability.signedAt` counts a digest as disclosing when the `PRF_msg` entry for its
message is in the cache. That is a proxy for *the signer produced a signature at this digest*,
and an adversary that knows `SK.prf` satisfies the proxy by making the query itself. The proxy
lets a fiction count as a disclosure, and the seed guess is the charge that pays for the fiction.

Defined by the **signing log**, the replay case closes by strong freshness alone: if the only
disclosing input is the forgery's own, its message was signed at the forgery's own digest input,
which pins the randomiser and the message by `Hashing.messageInput_injective`, which makes the
forgery the logged signature. Both steps are already proved. Index by the digest *input*, not by
the digest value — two inputs can carry the same digest, and then nothing pins the randomiser.

So `ReplayGate.RandomiserBad` has no branch reaching it, the ordering defect goes with it — under
the log notion nothing can become disclosing after it is filed — and the disclosing cap becomes
one per served request with no hypothesis.

### The prerequisite, which is not optional

`Security.signingOracle` appends the log entry **after** `Scheme.sign` returns. So under plain
"logged" the signer reads its own FORS secrets while they are still undisclosed, the stall that
the input half's blindness argument depends on has not happened, and the stalled run reads a cell
it must be blind to. The cache proxy got that ordering right, which is why it was chosen.

Disclosure must therefore be **"logged or in flight"**: the request being served discloses from
the moment it starts. Then the stall precedes every read by construction rather than by proxy.
That requires the handler to know which request it is serving, so the handler-separated
presentation is a dependency of this repair and not an independent convenience.

## The count the input half spends is calls, and cache growth cannot report it

The half's two terms are now charged at expectations: `RedrawCell.prob_sensitive_run_le_canonical`
weighs the probes by the record's canonical class, and `prob_claimed_run_le` weighs the
forgery's claims by their own number, a constant. What is left is to say which function of the
*paired run* those weights are, since `SharedJoin.prob_sharedBad_le_expected` takes
`countCanonical : Pair → Nat`.

**It cannot be cache growth, and the reason is worth stating because growth is what the pair
most obviously carries.** The tail starts from the walk's cache, which holds a canonical entry
at every node. A probe that is *sensitive* is the canonical input of a node with the table's own
cell in it — so it is answered from that cache and installs nothing. Growth at canonical-class
inputs therefore counts exactly the probes that **miss**, and none of the ones the charge is
about.

That is not fatal by itself, since a targeting probe is a miss or the hit itself: each one
either names a cell it has wrong, which is a fresh in-class input and so growth, or names it
right, which is the bad event. So the weights are bounded by `growth + 1` run by run, and by
`growth` on the complement of the event being charged. Whether the join can absorb that `+ 1` is
an arithmetic question for the join and not for this half, and `259` is already exact.

**The alternative is that the count is a count of calls, which the plain pair does not carry.**
`ClassGrowth.splitCost` counts calls per class, which is exactly the weight the charge uses —
repeats included — but it reports them into `Counts`, and `pairedRun`'s game is instrumented
with the plain hash cost, so its `Outcome.counts` has only `hash` and `verification`.
`ClassGrowth.probEvent_splitCost` moves an *event* between the two presentations and not a
count, and the map that identifies them forgets the split, so no function of the plain pair
recovers the slot. Either the join's counts are read at the split-counted presentation, or this
half's count is `growth + 1`.

## The reopening, settled: what disclosure is and what the budget then costs

Three threads checked the repair independently and two of them arrived at the same correction,
which is the strongest evidence the development has produced for any of its design choices.

**The notion.** A request discloses the positions selected by the cached answer at its **digest
input**, for a request that is logged or in flight — and only once that input is in the cache.

Each clause earns its place:

* *served, not cached* — the proxy's failure was that it accepted inputs **nobody served**, which
  an adversary knowing `SK.prf` can manufacture. `served` is the state's own record of what the
  signer served, so the fiction has nowhere to enter.
* *in flight, not merely logged* — `Security.signingOracle` logs after `Scheme.sign` returns, so
  under "logged" the signer reads its own FORS secrets while they are still undisclosed and the
  stalled run reads a cell it must be blind to.
* *once the digest input is cached* — before its digest is drawn an in-flight request has no
  positions to contribute, and counting it anyway would make the disclosed set *move* when the
  answer arrived. A disclosed set that moves is useless to a charge that stalls on it. The signer
  reads no FORS secret before that point, so the conjunct is still early enough.
* *indexed by the digest input, not the framed message* — otherwise an adversary picks its own
  randomiser for a message the signer did sign and has its own digest's positions counted. This
  is the same correction as in the replay branch, and it is now load-bearing in two places.

Closure survives for free: the disclosed set enters availability only at the `forsPrf` leaves and
a parent's availability is decided by its children, so **no** disclosure notion can lose it.

**The recorder keeps filing on fresh draws only.** Filing a cache hit would break three things at
once — the disclosing list's distinctness, the block factorisation, and the joint-uniformity
induction whose exponent rests on "recorded implies freshly drawn, and one draw extends at most
one word". The handler split therefore *relocates* the ordering defect rather than removing it.

**And that is affordable, because the seed guess is gone.** The budget now reads: the answer
side spends one unit per query, its two charges partitioning them; the shared side spends the
record's canonical part for the input half, plus the forgery's `259` claims, plus the record's
message-class part for the ordering defect. With `work + 2 ^ subtreeHeight ≤ q` that is
`(q - 2 ^ subtreeHeight) + 259`, and the total is `2 q - 247`. The randomiser defect's term and
the signer's coincidence both disappear with the proxy that created them.
## What the stalled stack asks of monotonicity, and the one way it could fail

Moving `availableAt`'s domain from the cache to a serving carrier is safe for the stalling and
redraw arguments, and the audit is short because the dependency is narrow. The whole stack
consumes monotonicity in **two places of the same shape** — `ChargedProbe.withFlag_frozen` and
`ChargedProbe.flagged_frozen`, each of them

    hmono state.1.1 inner.2.1 (CacheAvailability.lazyProgram_persists …) index hstate

and nowhere else. Neither uses a property of `Persists`: not transitivity, not reflexivity, not
a lookup. The relation is passed from the step lemma straight into `hmono`, so any relation
whatever will do. `StalledRun` mentions no cache at all — it is generic in the state — and
`OpenCache.lazyProgram` feeds the state's first component to availability at exactly one site.

**So the burden moves entirely onto the carrier analogue of
`CacheAvailability.lazyProgram_persists`**: that a handler step grows the carrier. Its present
proof is two cases — a coin step leaves the state *identical*, a hash step adds at most one
cache entry — so it needs only reflexivity and "adding a cache entry grows the carrier".

**The one shape that would make it false is a step that clears the in-flight framing.** If
`Grows` is componentwise — cache grows, served grows, in-flight unchanged — then the step in
which a request completes, and its framing moves from in-flight to served, is not `Grows`, and
the lemma fails exactly there. Since "logged **or** in flight" is the point of the notion,
`Grows` has to be a statement about what the carrier *discloses* — served together with
in-flight — rather than about its three components separately.

**Two sites keep a cache and must not be swept along.** `RedrawCell.probEvent_rom_eq_lazy` and
`probEvent_rom_eq_lazyProgram` compare the game's own rom cache with the programmed entries by
lookup, through `Compatible` and `unionCache`, at total availability where nothing reads a
carrier. They are about cache contents, not disclosure, and stay cache-level.

**And the record's entries change type with it.** A record entry is the probe paired with the
object availability is read from, so it becomes `Bytes × Carrier`; the claims charge requires
every claim to carry the run's own final one, so `WarmProbes.claimedEntries` must pair with the
final carrier. The event has to agree: `RoutedSplit.InputBad` reads disclosure at the trace's
final cache, and whatever that becomes must be the same object the entries carry.

## The containment, and what it actually rests on

Reading the input half's count off the record — `(record.filter CanonicalClass).card` at
`RandomiserRecord.recordedPairedRun` — asks that the probes the charge weighs be among the run's
recorded queries. The recorded ones are the adversary's and the verifier's; the handler's own
record holds more, because the stripped honest phase still asks for each signature's randomiser
and message digest. So the containment needs those probes to weigh nothing.

**It is not the warm filter that does it.** `ChargedProbe.Targets` is read off a probe's
*address*, so a probe that names a sensitive node with the wrong payload aims at a cell without
being answered by the walk's table. The weights are dominated by the canonical *class*, which is
address-level, and not by the warm-answered part — the correction recorded above under "The
count the input half spends is calls" applies here too.

**What does it is `Target.GoodWalk`, both clauses, and they are already conjuncts of the event
being charged.** A randomiser input opens with `SK.prf`, so it is a tweakable input at the
public seed only if `SK.prf = PK.seed` — the walk's first coincidence.  A message-digest input
is a tweakable input only if the public key's seed and root spell a structural address — the
walk's second. Both are `HashSeparation.randomizer_tweakable_ne` and `message_tweakable_ne`,
with `AddressBounds.withinBounds_structural` supplying the address bound;
`RedrawCell.locate_randomizerInput`, `locate_messageInput` and `not_targets_of_locate_none` read
them through the stakes' own `locate`, which is the form the weights are stated at.

**What is left is the induction, and its invariant is a multiset inequality rather than a
count.** For every result of the handler run,

    ((handler record).filter Targeting).map Prod.fst ≤ recorded.filter CanonicalClass

in the multiset order, whose cards then give the bound. It adds across binds, the honest phase
contributes nothing to the left by the facts above, and an adversary or verifier query adds the
same element to both sides. That is the shape of `WarmProbes.warmCount_strippedAfterSeeds`'s
phase decomposition with the warm filter replaced and the work counter replaced by the recorded
multiset — a mirror of that file's skeleton, not a new argument.

## The containment is a provenance argument, not a filter argument

The plan to mirror `WarmProbes`' five-phase skeleton for the containment does not survive
contact with the honest phase, and the reason is worth keeping because it is the same near-miss
as before wearing a different hat.

`WarmProbes`' honest-phase obligation is that the stripped phase's probes are **cold** — the
walk's table cannot answer them. That is path-independent: `StripCached.queriesUnder_strip_none`
reads it off the stripping impl alone, whatever the oracle answered. The containment's
obligation is that those probes are **not targeting**, and coldness does not give it: a cold
probe can target, since targeting is read off the address and a wrong payload is cold. What is
needed is the probes' *shape* — randomiser or digest — and shape is path-dependent, because
`QueriesUnder` follows the replay path while the run follows the oracle's answers.

**The development has already paid for exactly this.** `SignerRandomiser.probes_signInternalAt`
says every probe of the signer past its randomiser is a canonical input or its own digest input,
and `signInternal_eq` adds the randomiser; `PhaseProvenance.signerMade_of_fresh_step` is the
device that reads such a statement at a *later* cache, which is what makes it apply to the run's
own probes rather than to a replay. `provenance_phase_subset` then says where an entry came
from: the adversary's record, or a signing sub-run on a logged request.

**But provenance speaks of cache entries, and the charge weighs record entries.** The two differ
by repeats. They can be made to agree by de-duplicating the record the charge is handed —
`ChargedProbe.prob_run_cell_le` already takes the record as a function of the result, and
`∃ entry ∈ record, …` is unchanged by `List.dedup` — after which the weight counts *distinct*
probes, which is what provenance talks about. A distinct targeting probe is then either one the
adversary or the verifier made, hence recorded, or one the signer made first, hence
non-targeting by the shape argument.

So the containment is a provenance argument over a de-duplicated record, not a filter argument
over a fresh skeleton, and the honest phase is where the difference lies.

## An unapplied bridge is a missing bridge, and probe files are how you find out

**A bridge that exists but sits unapplied is indistinguishable from a missing one at the moment
someone hands work over, and the cost lands on whoever assembles.** This has now been the shape
of four mismatches in this development, twice found before assembly and twice after, and the
difference each time was whether anyone had tried to hand the work over.

The two joins both had it. `AnswerJoin` stated its recorder hypotheses at the split-counted run
while every producer writes at the all-hashes-counted one; the bridge
(`CoverageCount.mem_support_recorder_countAllHashes`) existed and sat unapplied, so a producer
would have handed over something that did not fit and both statements would have read correctly
on their own. `SharedJoin` defined `ProbesIn` and `card_le_of_probesIn` but never showed how to
get from them to the hypotheses it takes — four lines that two of its three owners would each
have discovered.

### The check that finds it

Not reading. Write a probe file per hypothesis, state it the way its *producer* would state it,
and try to discharge the join's version by bare `exact` with no tactic. Compile it with
`lake env lean` on a scratch file; it does not belong in the library. Three things make it work:

* **`exact` and nothing else.** A tactic that succeeds hides whether an adapter was needed. The
  question is not "is this provable" but "does it plug in", and only a bare term answers it.
* **State the producer's form, not the join's.** The whole failure mode is that both read
  correctly in isolation, so the test has to put them in the same place.
* **Expect timeouts, and treat them as failures.** Two of the probes exhausted `whnf` rather
  than reporting a mismatch. That *is* the answer — the elaborator could not equate the terms —
  but a cleaner probe is worth writing: compare the one component that differs rather than the
  whole statement. `(recordedTraceOf pair).2 = pair.2.2` settles in milliseconds what the full
  filter could not settle at all.

Probe files need the same `attribute [local irreducible]` line and `maxHeartbeats` as the module
they probe, or they time out on the game's definitions rather than on the question.

### The conventions that came out of it

* **Hypotheses are stated at the run their producer writes at**, and the join bridges. A
  side-effect worth having: `AnswerJoin`'s hypotheses then stopped mentioning the counter slots
  at all, because they only ever did through the run.
* **A charge is taken per walk**, which is both the habit and the shape charges naturally prove;
  the averaging is the join's step, not the owner's (`SharedJoin.prob_le_expected_of_perWalk`).
* **Keys are named at the walk's cache, never the run's.** The walk's key is fixed before the
  run, so statements about it compose; the run's is a function of the result and drags
  `AnswerSide.generatedKey_eq_walk` into every use. Applied once, in the join, where the support
  is in hand.
## Where the containment's honest phase has to be read

With the weights now at distinct probes, the containment's shape is settled and one interface is
not. The invariant to prove is

    every targeting input in the handler's cache is in the recorded multiset

which suffices because the handler starts empty, so each distinct probe installs its input the
first time it is made, and because every probe is cached once it is answered.

**Stripping disposes of the honest phase's canonical probes for free.** `strippedKeygen` and
`strippedSign` answer from the walk's table *inside the computation*, so a canonical probe never
reaches the handler and never enters its record. Key generation therefore contributes nothing at
all, and the signer contributes only what the table cannot answer: the randomiser and the
message digest, which `RedrawCell.locate_randomizerInput` and `locate_messageInput` show aim
nowhere.

**The interface that is not settled is which cache that shape argument is read at.**
`SignerRandomiser.probes_signInternalAt` is stated along `QueriesUnder cache`, which follows the
replay path at `cache`, and the stripped signer's actual path is: the walk's table where it can
answer, the oracle elsewhere. That path is the replay path at neither the table nor the
handler's cache — it is the replay path at their **union**, which is exactly
`RedrawCell.unionCache`, the game's own cache. So the provenance machinery
(`CacheProvenance.queriesUnder_sign_of_fresh`, `PhaseProvenance.provenance_phase_subset`), which
lives on the game's side, applies there and not directly at the handler's.

What is left is therefore an interface rather than an argument: state the invariant at the
game's cache, where provenance applies, and carry it to the handler's record through
`unionCache`, which `probEvent_rom_eq_lazy` already maintains step by step.

## The input half's part of the record is the aiming one, not the canonical one

`SharedJoin.recordCanonical` filters the record by `HonestProbes.Canonical` — the inputs that
are canonical at the **walk's own cells**. The input half's probe list cannot sit inside that,
and the reason is the same one that has now surfaced three times in different clothes.

The weights count *guesses*. The per-cell argument gives each probe that names a sensitive
node's address one chance at a freshly drawn cell, so what it counts is probes with the right
**address** and any payload. A probe is canonical at the walk's cells exactly when its payload
is the cell's true value — that is, exactly when the guess is **correct**, which is the event
being charged and not the count paying for it. So:

* aiming and canonical — the correct guesses, which is the bad event;
* aiming but not canonical — the wrong guesses, which is almost the whole weight;
* canonical but not aiming — canonical inputs of parents with more than one child, which no
  probe of this half aims by.

`RedrawCell.AimsSomewhere` is the test the weight is taken at, and the part of the record the
containment can be proved into. Widening the join's part from `Canonical` to that costs the
arithmetic nothing: `card_parts_le_record` is disjointness **by construction** — the message
class carries `¬ Canonical` as a conjunct — so the two parts fit inside the record whatever they
are, and the same holds with `¬ AimsSomewhere` in its place. The message-class owner's adapter
changes by one lemma, `canonical_not_messageInput` becoming `RedrawCell.locate_messageInput`,
which has the same `GoodWalk` hypotheses because an aiming address is a structural node's and so
is within `HashSeparation`'s bounds.

## A seventh defeq trap: an ascription that changes which lift is meant

*Entry 8 of the traps list; the index is under **The traps, consolidated** above.*

`simulateQ_spec_query` is stated as `simulateQ impl (liftM (spec.query t)) = impl t`. Writing the
same term as

    (liftM (OracleWorld.query (Sum.inr input)) : OracleComp OracleWorld HashOutput)

makes the lemma **fail to match**, while writing it without the ascription — letting the bind
that consumes it fix the type — makes it match. The ascription forces `HashOutput` where the
lemma has `OracleWorld.Range (Sum.inr input)`; the two are definitionally equal and not
syntactically so, so the `liftM` elaborates through a different `MonadLiftT` path, and `rw` sees
two different terms.

It is trap 5 in new clothes, and the rule it gives is the general one: **spell a term the way
the lemma that will have to match it spells it, and let the context supply the type rather than
ascribing it.** An ascription is not free; it is a choice of elaboration.

## Where a charge concludes decides what it can say

The answer half's charges used to conclude at the shared oracle's run, where the recordings are
gone. That is fine while every conjunct of the charged event reads the result and the cache, and
it stops being fine the moment one of them reads a recording — which is what happened when the
ordering defect stopped being assumed away and became a conjunct instead. No amount of plumbing
rescues it: `¬ LateDisclosure` is not *expressible* at a run whose state is a cache, so the
hypothesis cannot be threaded, only moved.

Moving it cost nothing, and the reason is worth keeping. `CoverageCount.prob_coverage_le_expected`
began with a single rewrite — the event-level move from the recorded run to the shared one — and
every step beneath it already stood at the recorded run. So the recorded form is that proof with
its first line deleted. The structural charge crosses the other way, by `recorderOf_eq_rom`,
because `GrowthCharge.Bad` reads only the result and the cache.

The general rule: **a charge should conclude at the richest presentation its proof already
passes through, not the poorest one its first consumer happened to want.** Concluding early
costs nothing — a consumer that wants less can always forget more — and concluding late throws
away the state that a later conjunct will need, after which the only repair is to find the line
where the state was dropped and stop dropping it.

The corollary for a reviewer: when a hypothesis "cannot be threaded", check whether the thing it
talks about still exists where the statement lives. Often it does not, and the fix is a move
rather than an argument.

## A recorder's state is a parameter, and its one law buys the bridges too

`RecorderView.CacheView` asks a recorder's state for `cacheOf`, `update`, and the single law
`cacheOf (update s i a) = (cacheOf s).cacheQuery i a`. The question when re-threading the
coverage stack over the handler's carrier was whether that law is enough, or whether the
tape-reading and budget arguments need something the class does not give.

It is enough, and not by luck. The two facts those arguments actually use are that the recorded
run is a run of the shared oracle (`mem_support_rom_of_recorderOf`) and that an event about the
result and the cache cannot see the recordings (`recorderOf_eq_rom`). Both were proved at the
cache in `SplitPrefix`; both follow at a general view from `cache_update` alone, by the same
inductions. So they are new **lemmas**, not a second law, and the carrier may carry a flag and a
served set beside its cache while staying invisible to every charge.

One friction is worth naming. `SplitPrefix`'s inductions never had to write down the ascription
`ProbComp (OracleWorld.Range (Sum.inr input) × …)`, because both sides of each step were spelled
at one state and so elaborated at one type. At a view the two sides are spelled at different
states, `rw` meets `HashSpec.Range input` where the goal has `OracleWorld.Range (Sum.inr input)`,
and the rewrite fails under `instances` transparency. `CoverageCount.rom_run_inr_some/none` are
the shared oracle's two branches with that ascription written down, and they exist only for this.

## The ledger, and what it decides

Every architectural choice left is decided by one piece of arithmetic, so it is worth writing
down once rather than rediscovering it. `Target.allowance` closes

    (q - 2 ^ subtreeHeight + 259) / 2 ^ 128 + (q / 2 ^ 128 + defects)  ≤  q / 2 ^ 127

with `2 ^ subtreeHeight = 512`. Reading the two sides apart:

* **The `q` coefficient is exactly two, and there is no slack in it.** The answer side spends
  one unit per query; the shared side spends the expected record, bounded by `q - 512`. The
  target is `2q / 2 ^ 128`. Nothing `q`-proportional can be added anywhere.
* **The constants have `247` units spare**: `259` claimed cells and `6` for the defects, against
  the `512` that key generation's spend reserves.

So the question to ask of any new charge is not whether it is small but **what it is charged
against**:

> A charge against a single output — the forgery, its signature, its published randomiser — is
> a *constant*, and the constants have room. A charge against a query set *scales with `q`*, and
> there is nothing to give.

**That rule as stated is wrong, and the way it is wrong is the more useful fact.** Counting the
adversary's *outputs* is not the same as counting its *chances*. A guess at a secret is a
constant only when the adversary cannot tell a right guess from a wrong one; if some published
value is a known function of that secret, each query is a **test**, and `q` queries buy `q`
chances however few objects the adversary ever outputs.

The forgery's published randomiser is the case that taught us this. It looked like one guess at
`SK.prf` — the adversary never sees the seed, and the forgery is a single object. But
`ObligationShapes.publishedRandomizer_eq_truncate` says the randomiser a signature carries for a
framing is `Hashing.truncate` of the oracle's answer at `Hashing.randomizerInput SK.prf PK.seed
framed`. So one signing request hands the adversary a *test*: for each candidate `x`, query
`randomizerInput x PK.seed framed` and compare truncations. The seed is unseen and perfectly
testable, and the charge is `(q - 1) / 2 ^ 128`, not `1 / 2 ^ 128`.

So the question to ask of a leftover is in two parts, and the second is the one that gets missed:

> What is it quantified over — and if it names a secret, is that secret **testable** from
> anything the game publishes?

The same obstruction is visible from the formal side, which is the check that the reading is
right rather than merely plausible. A constant can only come from an identical-until-bad hop
against a game that does not read the seed (`HandlerComparison.prob_bad_eq`), and that hop's bad
flag is *a query at a `PRF_msg` input at the real seed* — whose probability is the randomiser
defect's own, for which the ledger has no room. `RandomiserDeferral`'s docstring already said
deferring the draw past the walk is necessary and **not sufficient**, "because the tail's signer
derives every randomiser by querying at it".

Two leftovers were settled by exactly this distinction, in opposite directions.

**The forgery's randomiser being `SK.prf`** is one guess at a secret the adversary never sees —
the signer publishes `truncate (PRF_msg …)`, never the seed itself. One unit, payable. It cannot
be paid *at a fixed walk*, because the walk fixes the seed and an adversary that hardcodes one
makes the event certain on the walk where that value is drawn; so it leaves `AnswerBad` as a
conjunct and is paid at the paired run, where the walk is averaged.

**The disclosing cap** — that the signer-randomised recording is no longer than the signing
limit — fails the same way and cannot be repaired the same way. At the walk whose seed is `r`,
an adversary that hardcodes `r` asks `randomizerInput r pk.seed mᵢ`, reads `aᵢ`, then asks
`messageInput (truncate aᵢ) pk mᵢ`, which is signer-randomised at that moment and is filed left.
That is one entry per *pair of queries*, past the limit once `q > 2 ^ 65`. The charge is
`q`-proportional, so by the ledger it cannot be bought; and it cannot be aimed at the unspent
part of the record either, because the record's two parts are disjoint — `recordAiming` filters
by `AimsSomewhere` and `recordMessageClass` takes the message-class entries that aim **nowhere**
— and a message input aims nowhere. Nor is the cap re-tunable: `prob_not_goodBlock_le` wants
`length ≤ 5 · 2 ^ 62`, which is `1.25 · signingLimit`.

A cap that must hold exactly, cannot be bought, and cannot be relaxed has to be **true by
construction**: one entry per served request, filed on the framing rather than on a cache
coincidence. That is what `HandlerCarrier.FilesLeft` is for, and it is why the framing match is
load-bearing for the budget rather than a convenience.

The general lesson, stated so it survives this particular cap: **a test that an adversary can
satisfy by computing is not a cap, however small the coincidence looks.** The cache-based test
calls an input disclosing when nothing was disclosed — the adversary made both queries itself
and no FORS position was revealed — so it was never counting the right thing. Being wrong by a
`2 ^ -128` guess at a fixed walk is how that showed up, but the over-counting was there first.
## What a charge is indexed by decides whether it can be paid

The ledger has two kinds of room and they are not interchangeable. In units of `2 ^ -128` the
assembly must close `(q - 512 + 259) + q + 6 ≤ 2 * q` — `Assembly.le_target_of_full`, applied by
`Target.allowance`. So the **`q` coefficient is exactly two and both units are spent**, while the
constants have `512 - 265 = 247` units spare. (`Target.lean`'s own docstring says the margin is
`759`; that belongs to `le_target_of_counts`, which `allowance` does not call. The figure is 247.)

Hence the first half of the rule, which holds: **a charge quantified over the query set scales
with `q` and cannot be paid at all.** Two leftovers that read almost the same sit on opposite
sides of *statability*.

* `SplitWitness.SeedRandomised` — *some* cached message input has `SK.prf` for its randomiser.
  Quantified over the whole cache, so it cannot leave the answer side without a `q`-shaped
  charge. Unpayable, and not movable either.
* `AnswerCoverage.ForgerySeedRandomised` — the **forgery's** published randomiser is `SK.prf`.
  One object, so it *can* be moved to the paired run and charged there as `seedUnits`.

**The second half of the rule, as I first wrote it, was wrong, and the correction is the entry
above this one.** I said a charge against a single published object *is* a constant. It is not:
`ObligationShapes.publishedRandomizer_eq_truncate` makes the seed testable one candidate per
query, so `seedUnits` is `q`-shaped and is deliberately left a parameter. Naming one object buys
**statability at the averaged run**, not a constant. Counting the adversary's outputs is not
counting its chances — a guess is a constant only when a wrong guess cannot be told from a right
one.

`SplitWitness.mem_records_of_covered` only ever needed the narrowing at the forgery's digest, so
the second is what the argument actually uses and the first was an artefact of stating it over
the cache. Narrowing it is the same repair as the weakened cover, not a second one.

The corollary a reviewer can apply without the arithmetic: **before asking how tight a leftover's
bound is, ask what it is quantified over, and then whether what it names is testable.** A
leftover quantified over the run's queries is dead on arrival whatever the constant in front of
it. One quantified over the adversary's single output can at least be moved to where the
randomness lives — which is necessary, and, as this entry had to learn, not sufficient.

## And the same test condemns the disclosing cap

`hleftBound` says the disclosing recording is no longer than `signingLimit`. It is **false**, and
by a counterexample rather than a gap. `SplitWitness.disclosingKeep` is a *cache* test — the
`PRF_msg` entry the randomiser truncates from is present — so at the walk whose `prfSeed` is `r`,
an adversary that hardcodes `r` manufactures one disclosing entry per **pair** of queries: ask
`randomizerInput r pk.seed mᵢ`, read `aᵢ`, ask `messageInput (truncate aᵢ) pk mᵢ`, which is
signer-randomised at that moment and so is filed left. With `q` queries that is `q / 2` entries,
past `signingLimit` once `q > 2 ^ 65`. `GoodWalk` excludes two seed coincidences and not this, and
the statement is `∀ walk ∈ support graphWalk`, so one such walk is enough.

There is no q-proportional restatement either: `BlockViews.prob_targetCovered_le` needs
`leftLength ≤ 5 * 2 ^ 62` for its `2 ^ -141` term, which caps the recording absolutely. And the
complement cannot be charged, by the rule above — it is one unit per query.

So the cap has to become **structurally** true, by filing on served requests rather than on a
cache coincidence. `ServedAgreement.record_length_le_cap` is exactly that, at the carrier: the
served set is the image of the signing log, so the recording is one entry per request by
construction, with no seed secrecy anywhere. The same move repairs `hdisclosing`, whose false
direction is the same event read at the forgery's digest — at the carrier the disclosing test
*is* the log, and `ServedAgreement.agreesWithLog_run` is the iff.

## A cover is read where the query was answered, not where the event is read

The plan for retiring `hnarrowCached` was that `cover_of_served_or_narrow` makes the witnesses'
half free: an input the left test already keeps is filed for that reason, so the narrowed class
is needed only at the target. The conclusion is right and the route is not, and the gap is worth
remembering because it is invisible from the statement.

`RecorderView.mem_recordOf_of_cache` reads its cover **at the view in force when the input was
answered fresh**. The coverage event reads disclosure **at the end**. A witness disclosing at the
end need not have been disclosing then; and if it was neither disclosing nor narrow when
answered, it was filed on neither side. `¬ Late` does not exclude that case, because `Late`
speaks only of what the *target* recording holds, and this entry is in no recording at all.

So the witnesses' demand does not vanish. It becomes `Served.WitnessCover`: an input disclosing
at the end was already keeping at every view where it was still fresh, or else is narrow. That is
not a charge and must not be turned into one — it is a **presentation defect**, the gap between a
test read at answer time and an event read at the end. Charging it would be paying for the wrong
thing, and it is q-proportional anyway.

A serving flag closes it outright: the flag is set when the request's own query is answered and
never cleared, so end-served implies keeping-when-fresh by construction. That is the third of the
three hypotheses the carrier settles, beside the disclosing cap and the log/test iff — and it is
the same statement about the same object each time.

The rule: **when a hypothesis quantifies over a run, check which state it is read at before
concluding that something else implies it.** Two predicates that agree at the end can disagree at
every earlier view, and a filing decision is made at the earlier view.

## The forgery-seed leftover is the `PRF_msg` clause, and nothing else

Asked whether the leftover is a probability gap or a bookkeeping one, the answer is: bookkeeping,
and the bookkeeping is one conjunct. `SplitWitness.narrowClass` is `IsMessageInput ∧ ¬ PrfClass`,
and the leftover is exactly what the second conjunct throws away — the forgery's own digest input,
when its published randomiser is `SK.prf`, is message-class but not narrow, so the recorder files
it on neither side and the coverage join has nothing to point at.
`AnswerCoverage.narrowTarget_messageClass` is the check: at the message class the narrowed demand
is no demand at all, so removing the conjunct removes the leftover outright rather than paying it.

**The reason the conjunct is there is not the one its docstring gives.** That says the budget has
no room for one target entry per served request. It has. `BlockViews.prob_targetCovered_le` caps
only the *disclosing* recording, at `5 * 2 ^ 62`, and leaves the target recording's length free;
`CoverageCount.rightRecord_length_le_count` charges target entries against the inside slot of the
split counter, which the budget already covers, because the signer's randomiser probe is a hash
query and is counted in `q`. The extra entries are free.

What the conjunct really pays for is one case of `LateProvenance.hrecord_of_signerDigestFree`:
every target-recorded input must be a query `SharedJoin.recordOf` holds, and the case where the
entry is the signer's own **randomiser** probe is closed by `¬ PrfClass` itself. Widen the class
and up to `signingLimit` signer probes become target-recorded while the record holds only the
adversary's and the verifier's queries.

**The repair is the framing, not the class.** `HandlerCarrier.not_filesLeft_randomizerInput`
already excludes the signer's randomiser probe from the disclosing recording by comparing against
the frame in flight, and `RecorderView.noticingRecorderOf` now lets a filing test read a state
that has been told about the query. Excluding it from the target recording the same way retires
`¬ PrfClass` entirely.

The general shape, which is the third instance this week: **a clause added to a class to keep one
query out of a recording is a provenance fact wearing a syntactic disguise.** It works only while
the syntax happens to separate the two, it charges whoever meets the case where it does not, and
the honest version asks the handler who made the query instead of asking what the bytes look
like.

## A harness trap: `lake env lean` reads oleans, not sources

After editing a module, `lake env lean` on a file that **imports** it still type-checks against
the old `.olean`. The new name is simply absent, `autoImplicit` turns it into a variable of
unknown type, and the error surfaces as a type mismatch several lines from the real cause rather
than as a missing identifier. Rebuild the edited module (`lake build <Module>`) before
type-checking anything downstream of it.

This has cost an hour once. It is worth knowing in the same breath as the probe-check discipline,
because the two interact: a probe that "passes" against a stale olean is checking a statement
that no longer exists.

## When two lemmas will not meet at a step, quantify over the states

Three of this week's hardest moments were two true lemmas that could not be put together, and
the repairs that suggested themselves were all of the same expensive kind: carry more state,
refine the induction, match the objects up. One of them was closed instead by **not matching
anything**, and that is the escape worth generalising.

The signer's digest branch needed "the cache at which the recorder filed this entry already
holds the randomiser answer". `SplitPrefix.right_record_witness` hands back the cache before the
installing query, *inside* the signing sub-run; `provenance_phase_subset` inducts over the phase,
where one signing request is a single step, so its pre-state is from *before* the randomiser
query. The two lemmas both hand back a state and are about different steps — a **granularity**
mismatch, which carrying the state faithfully does not fix, because it would carry the wrong
cache faithfully.

What closed it was `SplitPrefix.right_record_suffix`, applied one bind later: for *every* entry
the rest of the computation files, it hands back a cache sandwiched between the one the first
step left and the final one. Every such cache holds the randomiser answer, by sandwiching alone.
No step is named, so there is nothing to match.

> When two lemmas cannot be matched at a step, look for one that **quantifies over the states**
> instead of naming one.

The same shape is why a charge proved for a strictly larger event is immune to what the smaller
one turns out to be, and why a lemma stated against what it uses survives the thing it was
written for changing. All three are the same move: weaken what the statement commits to, and the
seam disappears instead of needing a bridge.

## Hand back the most you know, not the least your first consumer asked for

A lemma on the way to the provenance mirror concluded

    mid (randomizerInput sk.prf pk.seed framed) ≠ none

which is true, provable, and useless. It leaves the entry's randomiser and the cached answer
unrelated, so no contradiction is reachable at the consumer. Returning **the answer and the
containment** instead — `mid … = some a` together with `mid ⊆ result.2.1` — closes the branch
immediately, because a target entry of the request's digest shape is then `SignerRandomised` at
`mid`, which is exactly what the target test denies there.

> An existential that drops the witness the consumer must match is the same failure as naming
> the wrong state.

This one is nastier than the granularity mismatch, because **the broken version looks like the
strongest reasonable statement**. A disequality is what you write when you do not yet know what
the consumer will want, and it reads as appropriately general rather than as lossy. Its
signature is a conclusion that is existential, negative, or otherwise opaque about a value that
something downstream has to relate to another value.

So, in the same words as the presentation rule one level down: a lemma should conclude with the
most it knows, not the least its first consumer asked for. **A consumer that wants less can
always forget more.**

### Knowing the rule does not fire the rule

Instances nine and ten of the dropped-witness class were written **one round after** the rule
was corrected, by the person who corrected it, in the same file. Both times the carrier version's
first consumer needed neither conjunct, so the conclusion was written to that consumer — which is
precisely the judgement the two-case rule says not to make.

> The rule is easy to state, easy to agree with, and does not fire on its own at the moment of
> writing a conclusion.

So it is not a belief to hold, it is a **step in the procedure**: *write the conclusion, then
diff it against the proof's hypotheses before moving on.* Ten instances, and the only ones caught
early were caught by running that diff deliberately rather than by knowing it was a good idea.

### A second signal, about when to stop

In the same sitting, a long single stretch produced a mangled edit — duplicated tactic lines and
two `sorry`s — which was reverted. The author's note is the useful part: **the edit quality
dropped before the judgement about edit quality did, and the signal was in the diff rather than
in how it felt.** Reading the diff is therefore the check; feeling fine is not.

### The mirror image: a hypothesis that looks necessary at one layer

The cell correspondence relates a final recording's offset to a starting block's. Chaining it
across three stages appeared to need an invariant — *the block shortens by exactly as much as
the recording grows* — and that was flagged as a real lemma, true, obvious and load-bearing.

**It is the hinge, and the correspondence does not have to turn on it.** Stated with the
continuation as a parameter, each layer's hypothesis is the conclusion **at the continuation's
own starting recording and block**, so no global index arithmetic ever appears: the outer layer
relates the original offsets to the intermediate, the inner relates the intermediate to the
final, and nothing counts how many cells an earlier stage consumed.

> The single-run form made the invariant look **required**, because at one layer the intermediate
> offsets *are* the original ones.

So this is the mirror of the second-consumer failures above. Those are errors invisible until a
second consumer distinguishes a statement from its specialisation. This is a **hypothesis that
looks necessary** until the statement is put in the shape a second consumer forces — and then
turns out not to be needed at all. Both have the same cause and opposite symptoms: at one layer
the general and the specific coincide.

Fifth payoff of the continuation shape, and the first where it **retired** a lemma rather than
enabling one.

### The three failures are one failure

Polarity (a hypothesis supplied in one direction and read in the other), granularity (two
lemmas that both hand back a state, about different steps) and the dropped witness are all a
statement **committing to less than it knows, or to the wrong thing, in a way that is invisible
until a second consumer appears.** That is also why every one of them was found by the side that
had to *supply* the hypothesis rather than by the side that wrote it, and why building a second
instance of anything keeps paying: an assumption that is invisible rather than absent is the
worst kind of missing one.
## Land both readings of a pending change, not the one you expect to win

`narrowClass`'s `PRF_msg` clause is going, and the answer half's leftover goes with it. The
temptation is to wait, or to write the post-retirement version and rewrite the chain when it
lands. Both are worse than leaving the class a **parameter** and carrying the demand it makes —
`Served.NarrowTarget` — as a conjunct of the charged event.

Then the two readings are instantiations of one theorem rather than versions of each other:

* at `narrowClass`, `narrowTarget_of_not_forgerySeedRandomised` turns the leftover into the
  conjunct, and the chargeable bound is a case of the general one;
* at `CombinedCharge.IsMessageInput`, `narrowTarget_messageClass` holds of every result, so the
  conjunct drops by `probEvent_mono` and `answerRecordedBound_wide_of_parts` has the obligation's
  own event with nothing left to charge.

`answerRecordedRunAt_narrowClass` is `rfl`, so the run does not move either. The retirement is an
`exact` at one call site, and if the two readings ever disagree about anything but the class, the
second stops elaborating. That is the same discipline as probing a hypothesis before handing it
over, applied to a change that has not happened yet.

One trap worth naming: the widened class is `IsMessageInput` **at the walk's own key**, so the
parameter has to be walk-indexed (`walk → Bytes → Prop`). A class parameter fixed across walks
type-checks at the narrow instantiation and fails at the wide one, which is the sort of thing
that only shows up when the second instantiation is actually written — which is the argument for
writing it now.

## Two harness traps, and a pointer rule

**`simp only` can fail silently in the stalled files.** `RedrawCell`, `ChargedProbe` and
`StalledRun` set `backward.isDefEq.respectTransparency false` at file level. Without it,
`simp only [..., map_pure, ...]` does not fire on these `ProbComp` goals — no error, just an
unsolved goal with the `<$> pure` still standing, which reads like a missing rewrite rather than
a missing option. A proof mirrored out of those files needs the option as much as it needs the
lemmas.

**`lake env lean` reads oleans, not sources** — see the note above; the two interact, because a
probe that passes against a stale olean is checking a statement that no longer exists.

**And a pointer rule, from a round lost to it.** When a definition is widened by *wrapping* it —
`recorderOf` to `noticingRecorderOf`, a fixed handler to a parameterised one — the wrapped thing
gets a forward pointer in its docstring. A wrapper is invisible to someone reading the name they
were given: they find a statement that will not go through, and nothing in front of them says a
repair exists. That is the same failure as a hypothesis that is invisible rather than absent,
seen from the other side, and a one-line `see <name>` is cheaper than a convention of reading
whole files.

The same applies wherever a poorer statement survives beside a richer sibling — a `≠ none` next
to a `= some a`, a cache-monotonicity next to a value-persistence. Whoever finds the poorer name
first has no way to know the richer one exists.

## A bolted-on guard is a dropped witness, seen from downstream

The signature of a dropped witness is a `≠ none` in a conclusion where a consumer has to relate
the value to something. That is a shape, and shapes are easy to argue about. There is a
**symptom** that is easier to notice and harder to dismiss:

> A bolted-on guard is always the workaround a dropped witness forces, when the underlying
> lemma cannot say *which* answer. The guard disappears with the strengthening — not because the
> guard was wrong, but because its job was to stand in for a witness that had been thrown away.

`LateProvenance.SignerDigestFree` grew a `≠ none` guard after a one-query adversary refuted the
unguarded version. The guard narrowed the failure set from almost everything to exactly the
ordering defect; it was an improvement and it did not make the statement true. The cause was
upstream: `CacheProvenance.sign_randomizer_cached` concludes `… ≠ none`, carried forward by
`PhaseProvenance.SignerMade`, so a consumer relating the signer's *published* randomiser to the
cache has to go through `CacheReplay.replay` — which answers a miss with `default`. The
statement could not say which answer, so it accidentally said something about `truncate default`
for messages never signed.

So when a hypothesis grows a guard, look upstream for the lemma that could not name a value.

**One correction to the sweep's classification.** `SplitPrefix.right_record_fresh_nodup` was
filed as a free win beside its richer sibling `right_record_suffix`. It is not free:
strengthening its conclusion from `≠ none` to `= some entry.2` also strengthens its `hcached`
hypothesis the same way, so it is a **two-sided** change to a file several threads build on.
Nothing is blocked meanwhile, since `right_record_suffix` already hands back the rich form.

**And a smaller rule from the same round: duplication is a symptom of a missing pointer.** The
four-case analysis over `appended` was written inline twice before anyone noticed, by the same
person, for the same reason a wrapper is invisible to someone reading the name they were given.

## Each branch asks its question of the object that can answer it

The recorder-side decomposition of the game looked as though it would need the recorder
everywhere, and therefore a recorder mirror of every input-shape lemma that keygen and the
verifier already have at the ROM. It does not.

`SplitPrefix.mem_support_rom` projects a recorder sub-run to a ROM sub-run, so each phase can be
asked its question at whichever object answers it:

* **keygen and the verifier** are questions about *input shapes* — is this probe canonical, is it
  in the record. The ROM answers those, and `queriesUnder_keygenInternal_of_fresh`,
  `probes_keygenInternal` and `mem_record_countRecorded` apply unchanged.
* **the signer** is a question about the *recording* — which entries were filed, and at what
  cache. Only the recorder answers that, and that is the one branch with a recorder-side lemma.

So the decomposition is three counted-bind splits, `right_record_suffix` on each to say which
part filed an entry, the recorder mirror for the middle, and the ROM lemmas for the outer two —
**with no matching anywhere**, because nothing is ever asked of an object that would have to be
lined up with another first.

This is the general form of the escape recorded above. *Quantify over the states instead of
naming one* is this rule applied to a single lemma; *ask each branch of the object that can
answer it* is the same rule applied to a decomposition. Both avoid a bridge rather than building
one, and the tell in both cases is the same: when a proof starts needing two objects to be
identified, ask whether one of them was the wrong object to have asked.

## Put the statement's edge where the proof's knowledge already ends

Two economies that look opposite are the same act, and both came up in one lemma this week.

**Drop a hypothesis the lemma can discharge.** Both outer phase lemmas took freshness at the
phase's start as a hypothesis, and both already had it: `right_record_suffix` hands back a cache
containing the start in which the entry is absent, so the start cannot hold it. Carried three
times, once per phase, for no reason. *A hypothesis a lemma can discharge from what it is
already given is one the caller carries for no reason.*

**Hand back a witness the consumer needs.** The same lemma's mid case returned a cache and the
randomiser's answer and dropped which *entry* the cache belonged to, so the consumer could not
build the witness that the two descriptions of the entry are the same. The repair is to return
the sub-run's queries as well, after which the branch closes from one lemma about one sub-run
and needs no shared-oracle provenance at all.

> Make the statement's edge sit where the proof's knowledge **ends** — not where it is
> **widest**. Too far in and the caller does your work; too far out and the consumer cannot use
> what you had.

**"Hand back the most you know" is wrong as stated, and the habit found the counterexample on
its first serious run.** The strengthened lemma's proof also had the sub-run's start contained
in the mid cache, and returning it would have been noise: *no consumer can name that object.*
What makes a dropped witness a defect is not that something was omitted, but that the consumer
**could have named it and needed it**; what makes an extra conjunct noise is that the consumer
cannot name its subject at all. One test, two directions.

A third outcome looked available and **it was wrong**. The same proof had the entry's own value
in the final cache — nameable, not currently wanted, recoverable by one call — and the judgement
recorded here was to leave it out *and say so in the docstring*. One round later two new lemmas
wanted it, and the docstring did not help: a note tells the next person where to look only
**after** they have noticed something is missing, which is the expensive half.

> **"Not wanted" is a claim about the consumer in front of you, and it does not survive the next
> one.** "Return it" and "the consumer cannot name it" are stable properties of the lemma;
> "nobody wants it yet" is a property of a moment.

So the rule has two cases, not three. When the only reason to omit something the proof already
has is that the present consumer does not want it, **return it.** That is less elegant than the
three-way version and it appears to be true — the eighth instance of this class was a fact
someone had explicitly judged, documented, and deliberately left out.

### The workaround that would have been worse than the wall

The blocked branch could have been closed by matching the lemma's `framed` against provenance's,
proving the two keygen outputs equal — both are the replay of the same final cache, so it goes
through. It was refused, rightly: it would have made the signer's branch depend on the shared
oracle for a fact the signer already knows, recreating the coupling the decomposition exists to
remove.

> Asking each branch of the object that can answer it means the signer's branch should not be
> asking the shared oracle what the signer queried.

A workaround that compiles and quietly restores the coupling is worse than a wall, because
nobody gets a second chance to notice it.

### A habit, since the grep is not enough

Three instances of the dropped witness have now been found, each at the wiring and each one
lemma earlier than the last. The `≠ none` grep catches the *signature*; the general form is any
conclusion weaker than what the proof has in hand, and no grep sees that. The habit that does:
**when writing a lemma, write down what the proof knows and what the conclusion says, and diff
them.**
## The assembly layer had a ledger per generation, and the headings did not say so

`Assembly.lean` accumulated five ledger theorems as the design moved, and **four have no
consumers**. That would be harmless if the narrative said which was which. It did not: the
module docstring described the first (`le_target_of_terms`), the section headed *"The accounting
the finished proof has to meet"* described the fourth (`le_target_of_counts`, margin `760`,
defects bounded by `defects_le_five`), and the live `le_target_of_full` — margin `247`, defects
`defects_le_six` — sat under a heading about a different theorem with no narrative at all.

The `759`/`1024` figures that reached `Target.lean`, `ClaimedProbes.lean` and a brief came from
that heading. Reading top to bottom gave a margin wrong by a factor of three, and every layer was
individually true.

`MainTheorem.lean` had the same shape one level up: *"What remains after this file is exactly its
three hypotheses"* listed the hypotheses of `totalSecurityBits_of_halves`, which nothing calls,
while the live route is `totalSecurityBits_of_bound` into
`ObligationShapes.target_of_answer_and_leaves` and a different three.

The convention that fixes it is cheap and already present in seven docstrings, four of them in
one file: **a narrative that says what the proof does names the theorem, and a theorem with no
consumers says so.** It is checkable by grep, which is the point. Both files now carry a liveness
table or note, and the dead ledgers say they are dead.

## And a check of mine that was cut off by `head`

While reporting the above I claimed `2 ^ 102` appeared nowhere in the Lean. It appears in **38
places**. The grep was `grep -rn "2 ^ 102" SlhDsaSecurity/ | head -5`, and `PROGRESS.md` alone
supplied five matches, so every Lean hit was truncated away. I then wrote the negative conclusion
into a docstring and into a report that was acted on.

Both caps are live, for different terms: `2 ^ 102` is `ForsConcentrationSharper`'s, giving the
`2 ^ -126` additive and the halved FORS term, and is what `CombinedCharge`,
`WholeGameStructural` and `WarmedCharges` take as `hmoment`; `2 ^ 103` is the coverage tape's,
where `BlockViews.GoodBlock` is the cap and `prob_not_goodBlock_le` turns it into the flat
`2 ^ -141`. The old header's remark that `2 ^ 103` "cannot be used" is about the FORS *term* in a
dead ledger and is correct about it.

The rule, which is this week's defect in a new disguise: **a grep that establishes an absence
must not be truncated, and `| head` on a search whose hits are dominated by a log file
establishes nothing.** Count first, read second. A positive finding survives truncation; a
negative one does not.

## The rate audit: no wrong rate, and the reason is that the three parts are hypotheses

Twenty-four FORS claims, thirteen in `LateCharge`/`CoverageTail`/`DigestTape`, thirteen in the
input-half family: **not one wrong rate, and not one mismatched consumer on a live path.** Worth
recording why, because it is a design property and not luck.

The answer side's rate machinery makes all three parts of a rate claim *hypotheses* rather than
prose. `ClassExpectation.prob_bad_le_expected_cost` asks for the rate (`hrate`, at a **fresh
uniform** answer), the item-to-count link (`hcost : inClass input → 1 ≤ cost input slot`), the
item-to-event link (`hclass : bad input answer → inClass input`), and `GrowthCharge.CleanBad` for
the freshness the rate assumes. A reader cannot apply it with the wrong item count, because the
wrong item count will not elaborate. Where a rate's validity depends on a *law* rather than a
hypothesis — adaptivity, where the adversary sees a digest before choosing which signatures
disclose — the law is proved: `BlockViews.evalDist_recordedRun_eq` identifies the recorded run's
law with a blocked run of independent uniform tapes, so the per-entry rate meets a block the
adversary did not choose.

**Every live count is `q` or a named constant.** `HasTotalBudget` pins the only two counts there
are — total hash calls by `q`, served requests by `signingLimit` — and no live charge is
proportional to the second. `Target.defects` decomposes exactly into the answer obligation's
tail plus `prob_bad_walk`, with no term uncounted and none counted twice. The two halves are each
charged a whole `q` against a target of `2q`, so a query charged on both sides is budgeted, not
double-spent.

What the audit did find is everywhere else: **items attached to the wrong index set, ledgers
quoted from superseded designs, and figures with no lemma.** The pattern that produces them is
always the same — a sentence written when one design was live, left standing when the next one
landed. The liveness convention is the cheap defence, and the census is the expensive one: of
thirty-three FORS lemmas, sixteen have no consumer at all, and three parallel coverage designs
exist of which one reaches the top.

The methodological residue, which cost me two retractions in one round: **an absence is only
established by an exhaustive check.** `| head -5` on a grep whose hits were dominated by a log
file, and `grep -v` filtering on line *content* when the intent was to exclude a *file*, both
produced confident negatives that were wrong. Count first, read second; and when the conclusion
is "nothing anywhere", say how the search was bounded.

## A charge that costs nothing where the rate is spent is a warning, not a saving

Splitting `LateRate`'s filing predicate from its firing predicate produced what looked like a
bonus: at the carrier, `endKeep` would be `Served`, which does not read the cache, so a fresh
answer cannot change it and `hrecord` and `hentry` both discharge by `probEvent_eq_zero`. The
per-query charge did not move to the other side — it **vanished**. That was reported as an
improvement, and recorded here as one.

**It was a defect, and the widening of `PotentialCharge.prob_fired_le` is what exposed it.** If
the firing predicate never changes where a fresh answer is drawn, it changes somewhere else —
at the notice. The notice is **deterministic**: its firing probability is one or zero, and a
deterministic step cannot be paid for out of `potential * rate`. The third invariance condition
the notice parameter now carries is exactly what rules that out, and `endKeep := Served` fails
it.

> A charge whose per-step cost is zero everywhere the rate is spent is not cheap. It means the
> event fires somewhere the charge is not looking. Ask where the firing went before banking the
> saving.

### The split is three-way, not two

Two of the three had been collapsed, and each is needed by a different consumer:

* **what files** — the flag (`HandlerCarrier.FilesLeft`). Unforgeable, because the adversary
  cannot set the framing; down again at every step boundary.
* **what fires** — the cache-readable `SignerRandomised`. It must change *only* at fresh draws,
  or the rate cannot pay for it. This is what `LateRate` already uses, so nothing there moves.
* **what is recorded** — the served set. It must be faithful to the log, because that is what
  `ForgeryCoveredBy` reads at the end.

No two of these can be the same predicate, and the first bounds the third through the second:
**served ⇒ signer-randomised at the end**, because a filed entry had the flag up, so by
`not_filesLeft_adversary` the query was the signer's, so it used the real randomiser and that
randomiser's `PRF_msg` entry is in the final cache.

## The projection trap, three sightings and one fix

`rw` cannot solve for a metavariable that sits under a projection, and it cannot see through a
redex. Three forms of the same obstruction have now cost a build each:

1. a lemma whose conclusion is a projection of a structure the rewrite has to infer;
2. `ForgetsAlong`'s projection **applied as a lambda** — an instance of it is a redex, so the
   rewrite does not fire and the error points at the goal rather than at the application;
3. a lemma that has to be applied at a state the *previous* rewrite produces, so its implicit
   type arguments are determined only after that rewrite lands — a `bind_congr` attempted
   before then has nothing to resolve and reports a stuck `Bind ?m`.


**Two more, from elaboration rather than rewriting, with the same repair.**

4. `refine le_trans (big_lemma …) ?_` exhausts `maxRecDepth` at 1000000 *and* overflows the
   stack at 4000000, where `have h := big_lemma …` followed by `refine le_trans h ?_` elaborates
   immediately. `refine` unifies a large term against the goal; `have` elaborates it on its own.
5. A support-congruence goal arrives **un-beta-reduced** — `((fun pair => …) ∘ fun result =>
   (result, cells index)) z` — so `rw` finds no occurrence of the pattern until
   `simp only [Function.comp_apply]` has run.

6. A `refine` whose continuation is left as `_` fails higher-order unification against a nested
   expected form, and the error reports a **pair-eta mismatch** rather than the missing
   continuation. Supplying it explicitly elaborates at once.

So the repair generalises past rewriting: **name the instance instead of asking a tactic to find
it**, whether the tactic is searching for a pattern or unifying a term. Five obstructions, one
fix, and every one of them reports the goal rather than the cause.

### A counter-case: `irreducible` can be the cause rather than the cure

`attribute [local irreducible]` is the right move where a rewrite must **avoid** unfolding. At a
join where the unifier has to **see through** two runs in order to match them, it is the
opposite: blocking the unfolding makes the search diverge instead of succeed. One statement went
from *four million heartbeats, no elaboration* to **two seconds** when the attribute was removed,
and the attribute had been added by reflex from the rule above.

> Having the rule is not the same as asking whether this is the shape the rule is about.

Two further corrections from the same diagnosis, both worth more than the fix:

* A **`whnf` timeout reported at the `theorem` line does not mean the statement is at fault.**
  The event, the `tsum` and both bound hypotheses each elaborated in two seconds alone; the cost
  was in the proof. The error's location was as misleading here as everywhere else in this family.
* The remaining cost was **six implicit arguments left as `_` under a three-stage run.** Supplying
  them is the same repair again — name the instance rather than asking the elaborator to find it.

The order that found all this was: **positive control first** (does removing the suspect change
the symptom — one `#check`), then bisect. The bisect came back negative and that was its value.

**The fix in all three is the same: name the instance at the state it is used at**, as a `have`,
rather than asking `rw` to find it. Three lines. The diagnosis is the expensive part and the
symptom is misleading in every case — the error names the goal, not the application.

**But form 3 had a cheaper fix than the one that diagnosis endorses, and it is the general
lesson.** The stuck `Bind ?m` in `CarrierTail.forget_carrierTail` went away not by steering the
tactic but by **restating the three stage laws as binds**, so `bind_assoc` flattened both sides
and `bind_congr` walked them with nothing left to solve for. Changing what the lemmas say was
cheaper than changing how the rewrite is applied. The rule: when a rewrite has to match on
*both* sides of an equation, normalise the **statements** until there is only one shape, rather
than teaching the tactic to see through two.

Related and already recorded: `simp only` fails silently in the files that set
`backward.isDefEq.respectTransparency false`, and `lake env lean` reads oleans rather than
sources. All three are cases of a tactic failing in a way that does not name its own cause.

## The target now rests on five leaves

With `FinalAssembly.lateOrSeed` instantiating the defect as
`LateProbes.Ordering ∨ AnswerCoverage.ForgerySeedRandomised`, the answer obligation's `¬ late`
is the answer side's own two conjuncts by `not_or`, and
`AnswerShape.answerChargedLateSeed_of_parts` composes the presentation move with
`AnswerJoin.answerRecordedBound_narrow_of_parts`. `hseed` is gone from the answer side: it is a
conjunct of the charged event, and its complement is paid on the shared side at `seedUnits`.

What `HasTotalSecurityBits .strong 127` now rests on, beyond the two arithmetic side conditions
`hclaims` and `hfits`:

| leaf | side | status |
| --- | --- | --- |
| `hjoinNarrow` | answer | the narrowed class at the forgery; `Served.mem_records_of_covered_narrowTarget` is its shape |
| `hleftBound` | answer | `CarrierFiles.leftRecord_length_le_cap` |
| `hdisclosing` | answer | `CarrierFiles.agreesWithLog_carrierRun` |
| `hinput` | shared | `SharedAssembly.InputBullet` |
| `hseed` | shared | the forgery-randomiser charge at `seedUnits` |

The provenance hypothesis is not among them — `LateProvenance.hrecord` is proved and its
consumer switched, so `target_of_answer_and_leaves` takes three hypotheses rather than four.

Two of the five are the carrier's and are proved already; what is missing there is the tail
object, not the lemmas. The composition was probe-checked before landing, as every join in this
development now is, and the probe is what recounted the leaves after the provenance retirement
changed the arity under me.

## The carrier run is not the recorded run, and the bridge is an interface not a map

`AnswerShape.map_fusedTail` reads the fused tail as `answerRecordedRun` because both are the
recorder at a **cache** test. The carrier tail has no such reading: its disclosing test is
`HandlerCarrier.FilesLeft`, a comparison against the frame in flight, and the two disagree by
construction — which is the repair, since it is what lets the carrier file a served request whose
digest is already cached and refuse the signer's own randomiser probe. `forgetRecord` keeps the
recordings, so the differing records sit inside the mapped value. Independently, the carrier tail
is bracketed and three-stage under `noticingRecorderOf` while `answerRecordedRun` is one
computation under `recorderOf`.

So the answer side's bound has to be **restated**, and the question is what it has to be restated
over. Not the recorder: the place where the two charges *meet* mentions no recorder at all. It
takes the structural clause at its own expected count, the coverage clause at its own, and the
pathwise fact that the two counts share one budget — `prob_bad_or_coverage_le_of_charges`, three
lines, generic in the run. Everything run-specific lives in the two charges handed to it, and the
coverage one is the hard half, being the tape factorisation at a bracketed noticing run.

`AnswerCarrier.answerCarrierRun` is the name for the run itself, defined once so two shapes
cannot drift; `answerCarrierRun_eq` is `rfl` against what the presentation move asks for.

**And one premise survives the change of recorder, which had to be checked rather than assumed.**
`noticingRecorderOf` runs `recorderOf` at `CacheView.onQuery state.1 input`, and `cacheOf_onQuery`
says the notice leaves the cache alone — so `appendedOf`'s guard is still freshness, and
`noticingRecorderOf_run_inr_some` shows a cache hit leaves both recordings untouched. The carrier
files on a **fresh draw only**, exactly as the cache recorder does. Everything resting on a filed
entry being a fresh uniform answer keeps its premise; what the notice moves is which state the
two *tests* are read at, which is the point and costs those steps nothing.

## State what you prove, or the ledger reserves for a term nobody spends

`answerRecordedBound_narrow_of_parts` proved `q / 2 ^ 128 + 1 / 2 ^ 141` and then added
`1 / 2 ^ 126` by `le_add_right`, for no reason but to match a stated right-hand side. That is
four units of `2 ^ -128` the ledger was holding against a term nothing spends, and no arithmetic
could have found it, because the weakening is *valid*. It was found by asking what the proof
ends on rather than what the statement says.

With `Obligations.AnswerChargedAt` parameterised over the allowance and
`Target.answerDefectProved` naming the proved one, the tighter statement is what the assembly
consumes, and the margin is 251 rather than 247.

The rule: **a weakening added to match an expected shape is a silent reservation.** If the proof
ends on something tighter, say so and let the consumer weaken — the consumer knows what it can
afford and the producer does not.

## The exclusion clause had the sign the wrong way round, and the fix reads the state

`not_filesLeft_randomizerInput` keeps the signer's own `PRF_msg` probe out of the **disclosing**
recording. The target test is `narrow ∧ ¬ FilesLeft`, so that same lemma says the probe *passes*
the second conjunct — it is `¬ FilesLeft` that sends an input to the target side. Retiring
`narrowClass`'s `¬ PrfClass` on the strength of it would have made the probe target-recorded, and
a target-recorded signer query is one `SharedJoin.recordOf` does not hold, which is exactly what
`LateProvenance.hrecord` needs.

The honest clause is `AnswerCarrier.FilesRandomiser`: the `PRF_msg` input for the frame **in
flight**, the exact counterpart of `FilesLeft`, which is the digest input for that same frame.
It is false at every adversary query because the flag is down at every boundary
(`not_filesRandomiser_of_clear`), true at the probe itself (`filesRandomiser_probe`), and
unforgeable for the same reason `FilesLeft` is, since only the signing oracle sets the flag.

`filesRandomiser_prfClass` is the check that was missing the first time a clause was swapped
here: the flag's version is **implied by** the syntactic one, so the new target test keeps
everything the old one kept and more — a weakening, not a different test.

The general shape, now with its repair: **a clause added to a class to keep one query out of a
recording is a provenance fact wearing a syntactic disguise**, and the way to undress it is to
ask the handler *which query this is*, not what the bytes look like. But check the sign: the
disclosing side and the target side read the same flag with opposite polarity, and a lemma that
excludes an input from one of them admits it to the other.
## The Poisson block: sound, and the margins are a quarter of a bit

The concentration machinery under `prob_not_goodBlock_le` — `ForsMoments`,
`ForsConcentrationPoisson`, `ForsConcentration`, `ForsConcentrationOccupancy`,
`ForsConcentrationExtended`, `ForsConcentrationSharper` — was read line by line. **No leaf, no
hypothesis discharged by something weaker, nothing vacuous.** The chain, so the next reader does
not have to reconstruct it:

```
prob_not_goodBlock_le
  ← ForsDisclosureTape.bad_load_probability
  ← uniform_load_tail_extended_of_le
  ← uniformLoads_monotone, uniform_load_tail_extended
  ← uniformLoads_mul_poisson_tail_le, poisson_count_tail_extended_half, poisson_load_tail
  ← poisson_sixth_sum_bound, poisson_centered_sum_moments
  ← independent_sum_moments, centeredMoment_bounds
  ← iIndepFun_pi, poisson_integral_centered_power, touchard_bounds
```

**Four places an error would have hidden, each closed by reading.** The sixth-moment partition
formula is a *definition* whose value is pinned by `sumMoment_zero` and `sumMoment_succ`, both
proved, so it never has to be trusted. `iIndepFun_pi` is Mathlib's, read from its statement and
applied at the coordinate-composition shape it actually has. Integrability is unconditional —
`poisson_integrable_power` and `poisson_integrable_centered_power` hold at every rate, degree,
order and centre, so there is nothing to discharge. And the two rates match on both sides of the
Poissonisation: `poissonLoads` is rate 3 per bin, the mixture and both Chebyshev steps are at
`3 * 2 ^ 63`, and the singleton densities agree exactly, so `poissonLoads_eq_mixture` is an
identity rather than an inequality in disguise.

**The margins, which decide whether a parameter is re-tunable.** Both final divisions are
verified exactly over rationals by `norm_num`, not estimated:

| chain | bound | threshold | ratio | needed | slack |
| --- | --- | --- | --- | --- | --- |
| main | `≈ 2 ^ 468.91` | `2 ^ 612` | `2 ^ -143.09` | `< 2 ^ -142` | **1.09 bits** |
| sharper | `≈ 2 ^ 468.91` | `≈ 2 ^ 596.14` | `2 ^ -127.24` | `< 2 ^ -127` | **0.24 bits** |

A quarter of a bit is not room. **Anyone who changes `forsHeight`, the Poisson rate 3, or the
`5 * 2 ^ 62` cap should expect `ForsConcentrationSharper` to break first**, and should check it
before the main chain rather than after. The cap itself is already known not to be re-tunable
upward: `2 * signingLimit = 2 ^ 65` is past the mean of the rate-3 Poisson.

**Where the reading stopped**, named separately from the conclusion so the rest stays usable:
the kernel numerics were not re-executed (confirmed `decide +kernel` over a Stirling table proved
equal to Mathlib's, and magnitudes checked by hand); Mathlib was not audited beyond `iIndepFun_pi`,
the one place a misapplication would have been invisible; and the presampling coupling
(`DigestTape.padding`, `TapeFactor`, `BlockViews.evalDist_blockTape`) was read only far enough to
confirm both joints are **equalities of laws** rather than bounds, so the block attaches to the
game without slack.

## The presampling coupling is an identity, and three never-fails carry it

`TapeFactor` and `BlockViews` were read end to end. **The coupling from the adaptive run to the
drawn blocks is an equality of laws, not a bound, and it is unconditional in the block lengths.**
`evalDist_splitTapeRun` is proved by induction on the computation with no hypothesis on
`leftLength`, `rightLength`, `leftKeep` or `rightKeep`: a block that is too short is fallen back
from (`splitTapeRecorder_run_*_nil` draws), and a block that is too long has its remainder
dropped. That is why no length hypothesis appears anywhere in the factorisation and why the whole
route is affordable — only the two *class* blocks are front-loaded; coins and out-of-class
answers keep drawing inline.

**The selection has to be causal, not deterministic, and that is the one subtle step.**
`probEvent_length_set` says overwriting cell `index` of the target block does not change the
probability that the recording reaches past `index`. Its only hard case is the step that reads
the cell: the two runs genuinely diverge past it, and the induction does not go through — but at
that step the event is already true and a recording that only grows keeps it true, so both sides
are `1`. **A circular argument would hide exactly here, and it is discharged by a proved lemma
rather than by an assumption.** What it buys is `prob_exists_hit_le_expected`: the charge is the
*expected* recording length times the rate, never a block length.

**Three never-fails are load-bearing**, and all three are proved: `padding_neverFails` (dropping
an unused block), `splitTapeRun_neverFails` and `blockRun_tail_neverFails` (`prob_leftBlock`
moving a block-only event off the run). A failing oracle anywhere would make
`evalDist_bind_const_neverFails` and `prob_leftBlock` silently wrong rather than unprovable.

**What crosses into the block is three hypotheses, all elaborated**: `hcap : leftLength ≤ 5*2^62`,
and `hleftBound`/`hrightBound`, the on-support caps saying neither recording outruns its block.
The cell correspondences (`rightOf_getElem?`, `leftOf_getElem?`) are claimed **only where the
block still has a cell**, which is why those two caps exist; a too-small `rightLength` makes
`hrightBound` unprovable rather than fudgeable. `rightLength` is otherwise free: it caps a
*count*, and the charge stays an expectation in the cells actually read.

Taking the disclosures off the **whole** block rather than the reached prefix is an over-count in
the safe direction, and `GoodBlock` is stated at the whole block too, so the cap and the coverage
read the same object.

## The Lean was repaired and the justification was not

A sweep of every block in the development that asserts what an adversary can or cannot do — two
greps over the 199 files of `SlhDsaSecurity/Proof`, about forty sites, thirty blocks read in
full — turned up one error worth the sweep, in two copies, both in `ProbeContainment`.

Each said the input half owes a **constant**. Each was contradicted by the same file's own
`InputBullet`, which pays `expected (card recordAiming) + 259`, and by `InputBullet.lean`, which
spells out why: a claimed cell is checkable against the authentication path, so the adversary's
chances are its queries. The two commits are in the record in the wrong order on purpose —
`Say which lemmas the half no longer stands on` is an ancestor of `Put the aiming count back
into the half's obligation`. The obligation moved and the prose explaining it did not.

The dangerous one is not the stale claim but its standing. It opened by naming the objection
("an adversary reads the cell off the answer, so no constant bound can be right"), answered it,
and closed with *"the claims charge is sound on its own"* — written explicitly as the thing to
point at if a constant is ever proposed here again. The objection it refutes is the one the
development has since accepted. A stale justification that invites the reader to repeat the
mistake is worse than no justification: it is a warrant aimed the wrong way at exactly the error
we already paid to find. The second copy carried an extra edge, telling the reader the aiming
machinery would only be wanted by some hypothetical other split, when the aiming part of the
record *is* precisely those tests — true that nothing consumes it today, false about why.

Both halves of the original argument had to be kept, because they have different answers.
*Reading* a cell off an answer really is impossible and `hclosed` really is why: a canonical
input contains its children's cells, and an unavailable node has an unavailable child.
*Guessing* one is possible and the guess is **checkable**, and that is the whole of the half's
cost. The repair says both, and says which one the charge turns on.

Three smaller defects of the same family were repaired with them —
`AnswerCoverage.ForgerySeedRandomised`'s docstring still read "One object, one guess, one
constant" while its own module prose refuted it, `CacheAvailability` still said the seed guess
"is charged as one" after that charge left for `Target.pairedRun`, and `RandomiserProvenance`
justified its `+ 1` as "one guess at the seed and nothing more". That last one is the
instructive case, because the number survives and the reason does not: the `+ 1` is right as a
**count**, since it is literally one query and the deferral pays per recorded query — with the
seed drawn after the run, testability buys nothing. Say that, or the next reader fixes the
number too.

Two distinctions earned on the way. First, **a load-bearing negative is not a leaf in
disguise**: `RecorderView` and `ServedBridge`'s claim that a cache-readable "the signer served
this" test is forgeable by anyone holding `SK.prf` is design-forcing — if it were wrong the
whole carrier parameterisation would be unnecessary — but no stated obligation becomes false.
`AnswerJoin`'s `hseed` block is the other class: an obligation's truth rests on the capability,
negatively, and that is what a leaf in disguise looks like. Second, the governing rule in
`Target` survives its own audit. All four surviving constants pass it — the walk's two
coincidences, drawn before any adversary exists and never compared against anything, and the two
tape bounds, which are concentration rather than guessing — and that is what makes the ledger
trustworthy rather than merely arithmetically closed.

## A parameter widened where it is read, and the two ways I nearly got it wrong

`Served.targetKeep`'s `narrow` now reads the view: `Bytes → σ → Prop`. The argument for it is
that `narrow` is consulted at **one input and one view** — the view in force when that input was
answered fresh — so nothing in the development depends on its being a property of the bytes
alone. A class that is state-free costs nothing by `fun input _ => …`, and the old family keeps
its signatures by exactly that lift, so nothing downstream moved. A carrier's class is not
state-free: `AnswerCarrier.carrierRightKeep` excludes the signer's randomiser probe by the frame
in flight, which no predicate on bytes can see.

`NarrowTarget` gains the view and a freshness side condition with it — the demand is "narrow at
every view where the target is still fresh", which is where `mem_recordOf_of_cache_fresh` reads
the cover. Its class argument is state-free, so the two call sites that used to pass `narrow`
now pass `fun probe => probe = <the target input>` and take the class from the hypothesis at the
view instead.

**Two methodological failures in one sitting, both mine, both caught by looking rather than by
anything downstream.**

First: I grepped the build output for `File.lean:NN:NN: error` when Lean emits `error: File.lean:NN:NN:`.
Three "green" builds in a row were nothing of the kind. The pattern matters as much as the search:
**a filter that can only ever match zero things reports success indistinguishably from one that
matched none.** Count the total too, and sanity-check the count against something you know is
non-zero.

Second: a `str.replace` whose pattern never occurred, because the file held ASCII `->` where I
had written `→` — left there by an earlier script of my own. `replace` is silent on a miss. Every
replacement now asserts its count, and the stray arrows are normalised.

Both are the absence rule in a new costume: **the check that something did not happen has to be
able to fail.**

## A check that something did not happen has to be able to fail

Three rounds were reported green on a filter that could only ever match zero. Lean emits
`error: File.lean:NN:NN:`; the grep looked for `File.lean:NN:NN: error`. **No match reads
identically to no errors**, and nothing downstream distinguishes them. In the same sitting a
`str.replace` whose pattern never occurred silently dropped an edit, and the next build's
"greenness" hid that too.

Both are the absence rule in new costume, and the costume is what makes them hard:

> A check that establishes an **absence** must be able to **fail**. Run it once against a state
> you know is dirty, and confirm it says so.

So: every replacement asserts its count; every error filter is sanity-checked against a
deliberately broken file. This is cheap — adding one bad declaration, building, confirming the
filter reports it, and reverting takes one round trip — and it is the only thing that separates
"the check passed" from "the check ran".

The same reasoning retires a weaker habit. Counting matches is not enough either: a count of
zero from a pattern that cannot match is still zero. What is needed is a **positive control** —
a state where the answer is known to be non-zero.

Related, already recorded: an absence established an hour ago is not an absence now, because the
thing that invalidates it is usually something that arrived rather than something that was
missed; and a grep establishing an absence must not be truncated.

## The composition side is finished, and it is margin-free

`CoverageCount.prob_bad_or_coverage_le_of_two_charges` is where the answer half's two charges
meet, and it has nothing in it: two events, two count functions, one budget, over an arbitrary
`ProbComp β`. No recorder, no state, no `Counts`, no `σ`. Three lines, because the place two
charges meet cannot see how either was proved.

That matters for the concentration margin, which is **0.24 bits** on the sharper chain. The
composition adds two expectations and a constant and contains no tail bound, so it cannot spend
any of it. The margin lives entirely in whatever proves the coverage charge — the tape
factorisation — and the one thing that would change what that sums, or at what rate, has been
checked and does not: filing is fresh-only under `noticingRecorderOf`, so the per-entry rate is
still a fresh uniform answer and the index set is still the target recording.

`AnswerCarrier.answerBound_of_charges` is the same composition stated at the carrier's own run,
with the four things it needs named: `hsplit` (the charged event implies one of the two clauses),
`hstructural`, `hcoverage`, `hshare`. Each is a thing somebody owns, and naming them is what
lets two sides meet by `exact` rather than by a second shape appearing — the habit that has now
paid four times.

The general lesson, which is the fourth instance this week: **the right abstraction was smaller
than the one asked for.** "Abstract over the run" would have meant carrying a recorder; what the
charges actually share is three propositions, and finding that out took reading what the
composition reads rather than what the chain carries.

## The coverage charge at the recorder that notices

`NoticingBlockViews.prob_noticingTargetCovered_le` is `BlockViews.prob_targetCovered_le` at
`RecorderView.noticingRecorderOf`, with the same statement, the same hypotheses and the same
`1 / 2 ^ 141 + expected(target recording) / 2 ^ 128`. Every proof in the file is the cache
version's with four names changed, because `NoticingTape` landed the whole tape layer beneath
the line — factorisation, causality, the two cell-for-cell readings, the leave-one-out charge —
with statements that differ from `TapeFactor`'s only in the word `noticing`.

**It spends none of the 0.24-bit margin, and the reason is structural rather than arithmetic.**
The notice moves which state the two *tests* are read at. It moves neither the freshness guard
that decides when a cell is filed (`cacheOf_onQuery`), nor the rate a filed cell is charged at.
So what is summed is still the target recording and the per-cell factor is still a fresh uniform
answer; the concentration input is the identical lemma at the identical cap.

The boundary that made this cheap is worth recording: **below the line everything is about `σ`
and two predicates; above it everything names the game's own FORS events** — `GoodBlock`,
`BlockHit`, `RecordCovers`, `TargetCovered`. Drawn there, the lower half generalises once and the
upper half mirrors mechanically. Drawn anywhere else, both halves would have had to know about
each other.

Two people each referred this piece to the other for a round. The line is what decided it, not
the argument — which is the case for drawing one early even when it looks like bureaucracy.

## `AgreesWithLog` is not the iff the coverage join wants, and my saying it was needs correcting

I reported that `hsplit` at the carrier needs nothing beyond `CarrierFiles.agreesWithLog_carrierRun`,
on the grounds that `CoverageRouted.forgeryCoveredBy_congr` wants the iff one input at a time and
`AgreesWithLog` gives it at every input. The conclusion survives; the reason does not.

`ServingCarrier.AgreesWithLog` is `Served state input ↔ ServingCarrier.logServed sk state.cache
signed input`, and `logServed` names the **replayed** randomiser,
`HonestProbes.replayRandomizer cache sk framed`. What the join wants is `ServedLog.servedLog`,
which names the **published** one, `parsed.randomizer`, read off the signature bytes. Those agree
only because the signer published what it computed — `ServedAgreement.servedLog_iff_logServed`,
a theorem, not a definitional unfolding.

So my side had the **same shape** of issue as the input half's: an interface whose two readings
look interchangeable and are not. The difference is luck of ordering — ours was already bridged
one file over, and packaged as `ServedBridge.ServedAgree`, the two-way containment. Theirs had to
be proved. Calling mine "enough" without naming the bridge was the kind of claim that is right
for a reason the claimant has not checked.

**The gap this exposes:** `ServedAgree` is produced at the serving-program run
(`ServedAgreement`, from `logFiled_run_with` and `agreesWithLogAt_run_with` composed with
`servedLog_iff_logServed`) and **not** at the carrier tail's run. `agreesWithLog_carrierRun`
gives only `AgreesWithLog`. Both ingredients exist at the carrier; the composition does not.

Method, twice in one sitting: I first asserted the gap before checking the bridge existed, then
nearly withdrew it on a `grep "ServedAgree"` that was matching the module name `ServedAgreement`
as a prefix. **A substring search for a short name inside a namespace that starts with it will
match the namespace**, and both the false positive and the false negative were resolved the same
way — by reading the matched lines instead of counting them.

## A probe that assumes the hypothesis containing the problem proves nothing

`probe_carrier_everything` elaborated: the whole target from the carrier tail, with `seedUnits := 0`
and six named hypotheses. That was read — by me — as evidence that the carrier route retires the
seed charge. **It was not evidence at all.** The probe takes `hsplit` as a hypothesis, and
`hsplit` is exactly where the seed charge lives: at the carrier's class,
`Served.NarrowTarget ↔ ¬ ForgerySeedRandomised`, so discharging `hsplit` is what costs the units
the probe had set to zero.

> A probe that assumes the hypothesis containing the problem proves nothing about the problem.
> Before reading an elaboration as evidence, ask which of its hypotheses the question is hiding in.

This belongs beside the positive-control rule, and for the same reason: both are checks that
cannot fail. An error filter that cannot match reports zero; a probe that assumes the open thing
reports success. Neither distinguishes the world where the answer is good from the world where
it is bad.

### And the finding it concealed, which is a quantifier rather than a design fault

`Served.NarrowTarget` quantifies over **every** view at which the input is still uncached.
`HandlerCarrier.State` is an ordinary record, so a view carrying a framing and an empty cache is
a value like any other — and the frame-reading clause `FilesRandomiser` is satisfiable there,
with the frame forced by `FramingLeak.randomizerInput_eq_messageInput` and
`Hashing.randomizerInput_injective`. So the clause cannot narrow the demand.

> Read at **one** state the clause works; read at **all** states it collapses.

Read at the single state the signer's probe is made from, it still does its real job — keeping
that probe off the target recording, which is what `LateProvenance.hrecord` needs. The repair is
therefore to read the demand at the view its input was **actually answered at**, which is the
discipline the rest of the `Served` family already keeps (`SplitWitness.lean:57-65`) and which
`NarrowTarget` alone did not inherit when `narrow` was generalised over the state.

## A hypothesis quantified more widely than its use site

`Served.NarrowTarget` asked for its class at **every** view where the target input is still
uncached. Its consumer, `mem_recordOf_of_cache_fresh`, consults the cover at exactly **one** view
per step — `state.1`. The statement offered all of them.

That gap is free to state and expensive to discharge, and it is **invisible until a class arrives
that can tell the two apart**. For a class reading the bytes alone — `IsMessageInput ∧ ¬ PrfClass`
— the two are the same demand, so the over-quantification cost nothing and nobody saw it. For a
class reading the handler's state, the wide form is satisfiable at a view with a framing and an
empty cache, and it collapses.

> Ask **where** a hypothesis is instantiated, not only what it says. A hypothesis quantified more
> widely than its single use site is free to write and expensive to meet.

The repair, `NarrowTargetAt`, cuts the views down by a caller-supplied predicate, and the caller
owes exactly two things: the predicate at the start, and that it survives a cache update. Two is
enough **because inside that induction a view changes no other way** — the recorder's only move is
a cache update, which is the same fact `ServingForget` uses from the other side to show a
bracketed run cannot be a plain recorder run.

### What it bought, stated exactly

On the carrier route the leftover stops being a probability question: at views with no request in
flight the demand is free, with **no hypotheses** (`narrowTargetAt_clear`). What replaces it is a
statement about the run — *the views this recorder is run at have no request in flight* — which
is discharged per stage by the bracketing, holds by construction for the adversary's stage, and
is **open for the signing stage**. That residue is a question about that stage, not a residual
`2 ^ -128`.

The cache route inherits the repair and **not** the benefit: its class reads the bytes alone, so
cutting the views down changes nothing, and it still owes its seed charge. What it gains is the
diagnosis — the leftover there is an artefact of the class being *syntactic*, not of the forgery
being one object.

## Never substitute a string that is a substring of a tactic name

A generator script substituted ASCII placeholders for Unicode and rewrote `omega` into `ω`,
turning a tactic into a type variable. It failed as `unknown tactic` at a column in the middle of
a line, **naming neither the tactic nor the substitution**.

> Never make a substitution whose source is a substring of a Lean identifier or tactic name.

`omega`, `beta`, `delta`, `gamma`, `sigma` and `alpha` are all live tactic or lemma fragments, so
the Greek-letter mapping is the dangerous one.

**The general form, from a second instance.** Generating a mirrored lemma by transforming the
original's text went wrong twice, both times silently plausible: a rename keyed on a token caught
the `intro` lines as well as the conclusion, producing duplicated binders and an error reported
at the one *use* site that was still correct; and a section docstring inside a grabbed range got
attached to the wrong lemma.

> A mechanical transformation must be scoped to the **statement**, never the proof.

Splitting each theorem at its `:= by` and transforming only the head fixes both. **The statement
is where names mean things; the body is where they are merely used.** Same cause as the Greek
mapping — a substitution whose scope is wider than its meaning. This joins the family of tactics that fail without
naming their own cause — and it is the only member whose cause is outside Lean entirely.

## The availability of a mechanical route is not evidence that it is the right one

The coverage charge at the bracketed run could be had by transporting the single-run version —
the transformation was working — and what it was producing was a **second copy of the charge**:
the `2 ^ -141`, the per-entry `2 ^ -128` and the index set written down a second time, in a
95-line proof to be kept in step with the first by hand. That is exactly what the one-copy
argument forbids, and it was about to happen *because the mechanical route was available*.

The charge is parameterised instead: it takes a **pair** of runs, handler-side and tape-side, and
the five facts it uses of them — their laws agreeing once the blocks are kept, the tape run never
failing, the two cell correspondences, and the selection's causality. Nothing else about either
run appears. The three-stage version is one application.

> The three earlier parameterisations were **forced** by a second consumer. This one had to be
> **chosen**, with the mechanical alternative sitting in front of it and working.

That is the harder case and the one worth naming, because the forcing is what usually does the
work: a second instance makes the general statement necessary. When there is no second instance
and a copy would compile, nothing external stops the copy — only noticing what it would cost.

### Two more substitution hazards, same family

* A placeholder set where one token is a substring of another (`LAN`, `AN`) turned `⟨⟨` into
  `⟨ L∧`. **A substitution set must be prefix-free, or ordered longest-first and checked** — and
  asserting that no placeholder survives catches it.
* `SigningLog` and `SigningSpec` resolved to the wrong namespace in a file without `open Security`,
  and the error named the *arguments whose types mentioned them* rather than the names. Qualify
  both.

## A parameter is not a guard: `Nat` units against a `q`-shaped event

`seedUnits` was introduced as a parameter precisely so that no constant would be asserted
without proof. It did not help. `seedUnits : Nat` makes `seedUnits / 2 ^ 128` a constant
however it is instantiated, and the event it was meant to pay for costs one query per
candidate — so the probability is `q`-shaped and **no numeral is large enough.** The hypothesis
was false, not open, and the arithmetic that made `251` fit was sound while bounding the wrong
thing.

> Parameterising a quantity records that you did not want to assert it. It does not check that
> the shape is right. A `Nat` parameter against a `q`-shaped event is the same error as the
> numeral, written more carefully.

The check that would have caught it is one question asked of the parameter rather than of the
proof: **does the thing being paid for grow with `q`?** If it does, no element of `Nat` is the
answer and the obligation has to move, exactly as a pathwise hypothesis has to move when its
exception set is non-empty.

And the resolution was not a new charge: the event is **contained in a defect the ledger already
carries**, by one rewrite reading the verifier's own digest query as a `PRF_msg` query at the
real seed. The remaining question is whether that defect's count has the room — a question
about an existing charge's slack, not about a new rate.

## A pathwise hypothesis and a probability bound fail differently

Three rounds were spent asking whether the seed residue was *small enough* to let `hsplit` be
taken in its strong form. That was the wrong question, and no amount of sharpening the residue
could have answered it.

`hsplit` is **pathwise** — `∀ result ∈ support …` — so it gets no relief from an exception set
being small. The runs where the forgery's published randomiser is the secret are *in the
support*, so the strong form is **false**, not expensive. Every bound around it is a
probability statement, where a small exception set is exactly the thing that helps; the two
sit next to each other and read alike.

> When a hypothesis is `∀ result ∈ support`, ask whether the exception set is **empty**. If it
> is not, the hypothesis **moves** rather than shrinks.

Moving it cost nothing: the same two charges and the same proof, with the exception carried as a
conjunct of the event, and a smaller event bounded by the same quantity. It also removed a
`probEvent_mono` from the composition — the step where the strong assumption had been hiding in
the plumbing rather than in a hypothesis. **A weakening step in a proof is where an assumption
goes to avoid being written down.**

## The dual: a hypothesis stronger than any proof could supply

`BracketedOrdering.prob_ordering_le`'s per-walk hypothesis was missing `Target.GoodWalk`, which
made it **unprovable**: off a good walk the probe multiset is empty, so the hypothesis read
`Pr[Ordering] ≤ 0`. Nothing complained when it was written, because at the one layer where the
bound is **read**, `GoodWalk` is in hand from the event being charged. It surfaced only when
something had to **produce** the hypothesis for every walk.

Same cause as the dropped-witness family — at one layer the general and the specific coincide —
with the symptom reversed:

| | symptom | found by |
| --- | --- | --- |
| dropped witness, over-quantified demand, untied hypothesis, hard-coded projection | a **conclusion weaker** than what the proof knows | the second **consumer** |
| this | a **hypothesis stronger** than any proof could supply | the first **producer** |

So the diff habit has a dual, and it fires earlier:

> Write the hypothesis, then ask what would have to prove it — **before the consumer exists.**
> And before naming it as an input at all, **grep for it**: the clause was added after an input
> was named, handed to another owner and recorded in a report, when it was already proved,
> already generic and one application away.

The consumer-side habit asks *what does my proof know that my conclusion drops*. This one asks
*what would a caller need in order to hand me this*. Both are answered by writing one thing down
and comparing; neither fires on its own.

## `hcoverage` lands at the answer side's run for free, and why

`CarrierCoverage.prob_carrierTail_targetCovered_le` charges `BlockViews.TargetCovered` at
`CarrierTail.carrierTail`. `AnswerCarrier.prob_targetCovered_answerCarrierRun_le` is that at
`answerCarrierRun`, and the whole proof is `probEvent_map` and `tsum_probOutput_map`.

It is free because of a choice made two weeks earlier: `AnswerShape.forgetRecord` drops the
record from the **value** and keeps the whole recorder state. `TargetCovered` reads the two
recordings and nothing else, so it is the *same proposition* at either run rather than a
transported one. The one thing that would have broken this is a forgetting map that drops a
recording — `FinalAssembly.forgetFused` is such a map, which is why the target had to be restated
at a refining tail in the first place.

**The counts line up for the same reason.** The coverage charge is one unit per *expected target
recorded*, and `insideCount := fun r => r.2.2.2.length` is literally that, so `hcoverage`'s shape
in `answerBound_of_charges` needs no adapter either.

## What the split counter costs at a bracketed run — the open question

`hstructural` and `hshare` are not free in the same way, and the reason is one object the carrier
does not have.

On the cache side both charges are read off `ClassGrowth.splitCost`, a counter installed by
instrumenting the *computation* with `countQueries`, whose two slots partition the queries and
sum to the run's own count. `CoverageCount.rightRecord_length_le_count` then bounds the target
recording by the inside slot, and the budget bounds the sum. `NoticingCoverage` has all of that
at the noticing recorder — but at `noticingRecordedRun`, which is **one computation**.

`CarrierTail.carrierTail` is three-stage and bracketed, and its count is read off the handler's
`CountedState`, not from `countQueries`. So there is no split counter to read the two charges
against, and the two obvious substitutes both fail: `insideCount := targetRecording.length`
matches the coverage charge exactly but leaves `outsideCount` undetermined, and
`outsideCount := count - targetLength` makes `hshare` trivial while making `hstructural` strictly
harder than the version anybody has proved.

So the question is not "how do I prove `hstructural`" but **"what counts the carrier tail
admits"**, and it is a question about the counted handler rather than about the charge. Recording
it here because it is the kind of thing that looks like a proof obligation and is really an
interface decision.

### What counts the counted handler admits — answered

**A counted handler admits exactly the per-query accumulations of a cost into a component beside
the carrier**, which is to say the `CountedHandler.withExtra` instances, and nothing else. It
does *not* admit the cache side's count as it stands: that one is installed on a computation
(`countQueries cost computation` under the plain shared oracle) and `ClassExpectation.
prob_bad_le_expected_cost` inducts over that computation, which is the original reason
`withCount` exists — a bracketed game is not one computation.

That answer is enough, because **the split is such an accumulation**. `ClassGrowth.splitCost` is
already a `Domain → Counts`, so the split counter is `withExtra` at `ω := Counts` with the
update `(· + splitCost inClass inside outside queried)` — the *same cost function the cache side
installs*, moved from the computation to the handler. No new notion of cost, and the `hcost`
side comes back as `splitCost_inside` / `splitCost_outside` with the step law in front
(`SplitCounted.withSplit_step_inside`, `withSplit_step_outside`, `withSplit_step_coin`).

**The interface change costs nothing downstream, and that is the part worth recording.** The
obvious move is to widen `BracketedRun.CountedState` from `… × Nat` to `… × Counts`, and that is
a shape change under four readers plus the whole carrier-tail stack. It is not needed.
`SplitCounted.run_withSplit_withCount` says the split-counted run **is** the counted run with its
counter split: map a state's two slots to their sum and the split handler becomes `withCount`,
started at the summed counter. So a split tail sits *above* the existing tail rather than
replacing it, and

* the coverage charge transports **up** the map for free — `probEvent` and `expected` of a mapped
  run are the run's own, so nothing about the tape factorisation is redone;
* `hstructural` is stated at the `outside` slot, which is the proposition
  `CoverageCount.prob_bad_or_coverage_le_of_charges` already takes, so the cache side's shape
  transports rather than being restated;
* `hshare` carries no new content: `splitCost_add_eq_hashCost` makes `inside + outside` the count
  the tail already has, so "the two counts share one budget" is the budget hypothesis that is
  already there.

`BracketedRun.CountedState`, `IsBracketedRecorderRun`, `CarrierTail.carrierTail` and everything
read off them are untouched. The two substitutes recorded above stay rejected for the reasons
given; what was missing was not a cleverer derived quantity but the observation that the counter
slot is a parameter of a wrapper that was already generic.

**On the two riders.** The seed charge is not retired and nothing here assumes it is: the split
partitions the *hash* calls of a run and sums to that run's own hash count, so whatever is
charged in seed units is charged elsewhere and neither slot touches it. And `hcoverage`
transporting free is the same fact as before — `AnswerShape.forgetRecord` drops the record from
the value and keeps the whole recorder state, and the map here drops a counter slot and keeps
the carrier, so both charges read what they always read.

The generic transport lemmas `withExtra_step_map`, `run_withExtra_map` and
`forgetsAlong_withExtra` now carry the `withCount` ones as one-line corollaries, which is the
third instance the `withExtra` note asked for.
