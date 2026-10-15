# Security of XMSS in the random-oracle model, in Lean 4

Machine-checked security statements and proofs for the XMSS instance of Ethereum's
post-quantum consensus, in Lean 4 using [VCVio](https://github.com/Verified-zkEVM/VCVio).
The development started from the 127-bit SUF-CMA proof in
[leanEthereum/leanVM](https://github.com/leanEthereum/leanVM/tree/main/formal/xmss) and
separates *what is claimed* from *why it holds*.

The strong-unforgeability exact-security statement is proved for **all 16 counting modes** by
`XmssSecurity.xmss_sufCma_exact`: exactly 122 bits when no honest-party hashes are
charged, and exactly 127 bits when key generation, signing hashes, or verification
is charged. The statement layer is unchanged.

Standard (non-strong) EUF-CMA is being developed separately on `proving-standard-uf`,
branched from the completed `proving-stuff` development without merging `main`.
A standard forgery must use an epoch/message pair never requested from the signer,
including requests that returned no signature. `XmssUnforgeability.lean` currently
proves at least 122 bits in every counting mode and at least 127 bits in the fourteen
modes charging some honest-party hashes. The proposed exact bound is 127 bits in
all sixteen modes; the stronger direct-query lower bound and the standard-forgery
attack are still open. The strong-security statements and proofs are preserved.

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
| | `XmssSecurity/Statement/Security/EUFCMA.lean` | standard unforgeability, with freshness of the requested epoch/message pair |
| Bit security | `XmssSecurity/Statement/BitSecurity.lean` | `SecurityNotion` and `HasClassicalSecurityBits`: `Pr[win] ≤ q / 2^bits` for every `q`-query adversary |
| The scheme | `XmssSecurity/Statement/Scheme/Parameters.lean` | the parameter table (`n`, `w`, `v`, `T`, `h`, `L`, `A_max`, …) |
| | `XmssSecurity/Statement/Scheme/Construction.lean` | tweaks, target-sum encoding, chains, Merkle tree, key generation, signing, verification |
| | `XmssSecurity/Statement/Scheme/Xmss.lean` | `xmss`, the scheme as a `SynchronizedSignature` |
| Claims | `XmssSecurity/Statement/Claims.lean` | the bit-security statements, one per notion |
| | `XmssSecurity/Statement/EUFCMAClaims.lean` | separate standard-unforgeability targets |
| Proofs | `XmssSecurity/Proof/` | proofs of the unchanged statement layer, including stronger numerical bounds |
| | `XmssSecurity/Proof/Direct/` | the direct-count proof: pruning a semantically bounded adversary to a syntactically bounded one (`Basic`, `Prune`, `Bridge`), the per-term bounds (`FirstLane`, `Structural`, `Prehit`, `SeedGuessing`, `VerifierBound`), and the assembly |
| Main theorems | `XmssSecurity.lean` | one theorem per claim, with an axiom guard |
| | `XmssUnforgeability.lean` | standard-unforgeability lower bounds, with axiom guards |

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
| Direct queries and signer hashes | 127 | `xmss_sufCma_signer_127` |
| Every mode charging signer hashes | 127 | `xmss_sufCma_secure_127_of_signer` |
| Every hash call and every signing request | 127 | `xmss_sufCma_everything_127` |
| Every hash call and every signing request: attack against 128 bits | upper bound 127 | `xmss_sufCma_everything_attack_127` |
| Every counting mode: attack against 128 bits | upper bound 127 | `xmss_sufCma_attack_127` |
| Every mode charging key generation or verification, both bounds | exactly 127 | `xmss_sufCma_exact_127_of_keygen_or_verifier` |
| Every hash call, both bounds | exactly 127 | `xmss_sufCma_allHashes_exact_127` |
| Every hash call and every signing request, both bounds | exactly 127 | `xmss_sufCma_everything_exact_127` |
| `XmssSufCmaExactStatement`: all sixteen modes, both bounds | exactly 122 or 127 | `xmss_sufCma_exact` |

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

`Proof/Modes/Exact.lean` reduces exact security for all sixteen modes to six basis
obligations. All six are proved; `Proof/Modes/Signer.lean` completes the last one,
127-bit security when only signer hashes are additionally charged.
For this signer-counted bound, `Proof/EncodingAcceptanceBudget.lean` proves that
the probability of obtaining any accepted encoding is at most its acceptance probability
times the expected number of encoding queries, starting from a cache with no accepted encoding.
The bound allows adaptive queries and cached replies; it also bounds successful reference
signing and proves the initial condition after reference key generation.
`Proof/Direct/DecidingSecondLaneAccepted.lean` uses this bound to replace the second lane's
constant forty-query verification allowance by `40` times the acceptance probability times
the expected encoding-query count before verification.
`Proof/Modes/SignerAccounting.lean` identifies the signer-counted experiment's charge with
all hashes in the adversary phase and derives a bound on that phase's expected hash count
from the unchanged statement's query-bound hypothesis.
`Proof/SignerEncodingCost.lean` proves that the seeded signer's expected hash count is
exactly twice its expected encoding-query count, including early termination and cached replies.
`Proof/SignerSuccessBudget.lean` consequently bounds successful seeded signing by half the
acceptance probability times the expected signer hash count, whenever the starting cache
contains no accepted encoding.
`Proof/Seeded/KeygenEncodingCache.lean` discharges that starting-cache condition for every
supported run of the actual seeded key generator, so the half-cost success bound applies
directly to signing immediately after key generation.
`Proof/FirstLaneEncodingExpected.lean` bounds the encoding component of the existing
first-lane experiment by its actual expected encoding-query count, using the monitor's
expected risk and an exact connection back to the original execution trace.
`Proof/FirstLaneChainExpected.lean` supplies the corresponding hidden-chain bound, including
probes before a reveal, and combines both components into an expected-query bound for the
existing first-lane experiment. `Proof/FirstLaneExpectedTrace.lean` identifies that count
with the execution trace and proves that enforcement can only decrease it.
`Proof/Direct/DecidingFirstLaneExpected.lean` carries the bound through the existing
couplings to the original first-lane winning event in the reference game. The resulting
expected hazard count is related to the signer-counted budget by the source accounting
and public budget enforcement described below.
`Proof/Direct/DecidingAcceptedProbe.lean` removes the unconditional extra deciding probe:
the probe runs only for an accepted forged encoding, and its expected charge is exactly
the probability of that condition. The proof preserves the original winning-event bound.
`Proof/FirstLaneEncodingAcceptance.lean` bounds accepted sampling observations by the
acceptance probability times expected encoding samples. `Proof/FirstLaneEncodingCache.lean`
tracks accepted cache entries through every direct-query and signing step, then uses this
bound to pay for the conditional deciding probe in the original first-lane event.
`Proof/Modes/SignerReferenceBudget.lean` transfers the statement's budget to every supported
reference key-generation outcome, charging direct hashes once and reference signer hashes twice.
`Proof/Direct/CountedSourceBudget.lean` preserves this budget at every supported continuation,
including signing calls with random costs. `Proof/Modes/SignerFirstLaneCoupling.lean` carries it
through the complete first-lane prefix coupling: while the executions agree, the ideal hazard
count plus twice the actual reference signer count is at most the statement's budget.
`Proof/FirstLaneEncodingCount.lean` identifies fresh encoding observations with the exact growth
of the ideal encoding cache. `Proof/Direct/FirstLaneSampleBudget.lean` then bounds those observations
by direct encoding queries plus source signer hashes, and obtains a shared charge expressed
entirely through the ideal trace and attacker log on the coupling's good branch.
`Proof/Direct/FirstLaneStepBudget.lean` extends the observable bound through every supported
ideal query from related states, including the first query that triggers a collision. The
stronger charge counts all direct calls and uses no hidden-table information.
`Proof/QueryLimiting.lean` implements an aborting query limiter and proves exact preservation
under semantic bounds on supported executions. `Proof/FirstLaneSampleLimit.lean` specializes
it to fresh encoding samples, retaining the observed prefix and exact unused fuel on abort.
`Proof/FirstLanePublicBudget.lean` combines direct-query credits with the sample limiter.
`Proof/Direct/FirstLaneBudgetEnforcement.lean` implements the complete limited ideal prefix,
proves its joint budget and hazard bounds even after divergence, and proves exact preservation
of each action from related states, including the first action that triggers a collision.
`Proof/Direct/LimitedPrefixCoupling.lean` carries the source coupling through that complete
limited prefix: either the outputs and states agree, or the retained trace contains a collision.
`Proof/Modes/SignerLimitedCoupling.lean` applies the unchanged statement budget to this coupling,
with both the source charge and the public ideal charge bounded on every coupled execution.
`Proof/Direct/LimitedPrefixSupport.lean` recovers an exact original execution from every
successful limited run, preserves the returned-signature coverage invariant, and bounds
accepted encodings in its final cache by the acceptance probability times fresh samples.
`Proof/Direct/LimitedAcceptedProbe.lean` transfers accepted source events to a deciding probe
after the limited prefix and proves that its extra expected hazard is exactly the forged
encoding's acceptance probability. `Proof/Direct/LimitedFirstLaneExpected.lean` carries this
through key generation to the original source-prefix probability; the signer-mode statement
budget now instantiates that bound directly.
`Proof/Deterministic/ExpectedReferenceQueries.lean` transfers the expected seed-query count
to the memoized reference experiment, so it can share that experiment's budget with the
other losses. It also proves that memoization cannot decrease seeded-game advantage.
`Proof/Direct/SeedGuessingExpected.lean` refines the seeded-to-reference reduction to charge
only the expected number of seed-derivation-tag queries, instead of all direct hash queries.
`Proof/Direct/SeedQueryPartition.lean` proves that seed, encoding, and structural query counts
are disjoint under any stateful interpretation. `Proof/Direct/SourceClassBudget.lean` combines
all three expected counts with twice the source signer cost under the same semantic budget.
`Proof/Direct/ReferenceSeedQueries.lean` removes honest operations from the seed count exactly.
`Proof/Direct/SourceQueryProjection.lean` preserves selected counts when forgetting source
instrumentation. `Proof/Modes/SignerClassBudget.lean` consequently bounds the reference
experiment's expected direct encoding, structural, and seed queries, plus twice its expected
signer hashes, by the original signer-counted statement budget.
`Proof/Direct/SourceSignerQueries.lean` bounds all prefix encoding queries by direct encoding
queries plus actual reference signer hashes. `Proof/Direct/SourceLossBudget.lean` combines
prehit, second-lane, and seed losses when the forged encoding is cached; its numerical bound
uses at most half the nonstructural budget weights. `Proof/Modes/SignerSecondaryLoss.lean`
places those source losses within `q / 2^128` and retains an explicit reserve for the first lane.
`Proof/Modes/SignerCachedLoss.lean` assembles the seeded-game loss for cached forged encodings.
`Proof/Direct/CachedEncodingCost.lean` proves that an always-cached forged encoding consumes
at least one expected direct encoding query or signer hash. `Proof/Direct/LimitedPrefixProbability.lean`
bounds prefix collisions by `q / 2^128` and charges the extra deciding probe only to acceptance.
`Proof/Direct/LimitedAcceptanceTransfer.lean` transfers that acceptance probability from the
counted source with an explicit prefix-collision term, allowing the executions to diverge afterward.
`Proof/Direct/SourceEncodingReserve.lean` retains three quarters of the encoding and signer
credit. `Proof/Modes/SignerCachedSecurity.lean` uses it to discharge the first-lane estimate
and proves the original signer-mode advantage bound at 127 bits whenever the memoized
adversary always caches its forged encoding. This conditional result includes every budget size.
Fresh forged encodings are handled by the shared-prefix construction below.
`Proof/Direct/VerificationAcceptance.lean` bounds fresh verification success by the exact
encoding acceptance probability, rules out cached invalid encodings, and retains the
acceptance factor when restricting to any prefix event whose cache has no accepted encoding.
`Proof/AcceptedEventCoupling.lean` proves a joint event inequality that cancels the
collision allowance for accepted probes on rejected source prefixes.
`Proof/Direct/LimitedAcceptanceCancellation.lean` applies it to the limited prefix and
bounds accepted first-lane events by the query allowance plus the source acceptance credit,
without an extra collision term. `Proof/Modes/SignerAcceptedFirstLane.lean` instantiates
this sharper bound for every signer-bounded adversary, including those that return fresh
encodings on some executions, and refines the cached-game loss assembly.
`Proof/Direct/FreshVerificationProbability.lean` carries the fresh-encoding acceptance
factor through the winning verification phase and the instrumented source finisher,
including events selected using auxiliary prefix randomness. It also decomposes the
full first lane into accepted prefixes and an explicit fresh contribution; the signer
budget bounds the former for arbitrary adversaries. The latter is bounded by the
fresh-encoding and revealed-value arguments below.
`Proof/Direct/QueriedEncodingAcceptance.lean` proves that moving the final encoding
query into the prefix preserves the structural-query count and creates acceptance only
on fresh inputs. `Proof/Direct/DecidingSecondLaneFresh.lean` removes the always-cached
hypothesis from the second-lane bound: its additional charge is forty times the encoding
acceptance probability times the probability of a fresh final encoding, divided by `2^128`.
`Proof/Direct/FreshPrefixProjection.lean` identifies that freshness probability with the
traced source prefix. `Proof/Direct/FreshFirstLaneContribution.lean` retains the actual
fresh first-lane winning probability in the decomposition. Together with the general
secondary-loss bound, `Proof/Modes/SignerMixedLoss.lean` now bounds the original signer-mode
advantage for arbitrary adversaries, with the remaining fresh contributions explicit.
`Proof/Direct/FreshEncodingCollision.lean` bounds a fresh encoding collision against the
unique signature at the forged leaf by `2^-128`, and requires an accepted encoding in
the prefix. Its budget and source-projection lemmas charge this branch to the source
encoding credit. `Proof/Direct/FreshFirstLaneSplit.lean` consequently reduces the fresh
first lane to its revealed deciding-value event plus that paid encoding collision.
This decomposition isolates the fresh revealed-value probability and the fresh
verification allowance for the subsequent shared-prefix assembly.
`Proof/AcceptedHashSampling.lean` constructs uniform accepted hash outputs and proves
the exact acceptance factor for continuations that reject invalid encodings.
`Proof/Direct/FreshRevealedConditioning.lean` applies that identity to the actual fresh
revealed-value event, preserving the source prefix and all verification randomness.
`Proof/Direct/RevealedEncodingPrefix.lean` moves its deciding-value witness back to
the adversary prefix with the accepted encoding supplied separately, then transfers
that witness to a hidden-value probe hit through the existing prefix coupling.
`Proof/Direct/LimitedEncodingProbe.lean` bounds the supplied-encoding probe experiment
by `(q + 1) / 2^128`. `Proof/Direct/FreshRevealedBound.lean` then bounds the actual
fresh revealed-value contribution by the encoding acceptance probability times that
quantity.
`Proof/Direct/MixedEncodingProbe.lean` combines cached encodings and an independent
fallback in one limited-prefix experiment. Its bound cancels the conditional probe
charge, and `MixedEncodingProbability.lean` averages the fallback over its acceptance
probability. `MixedFirstLane.lean` transfers the actual first-lane event to that
experiment and proves `q / 2^128 + p * (2 * (E + S) + 1) / 2^128`, where `p` is the
encoding acceptance probability, `E` counts expected direct encoding queries, and
`S` counts expected source signer hashes. This avoids charging the prefix separately
for cached and fresh branches.
`Proof/Modes/SignerSharedPrefix.lean` assembles this bound with all remaining losses
and proves the original 127-bit advantage bound for every budget when `E + S ≥ 1/512`.
This permits fresh forged encodings and does not require an always-cached adversary.
The complementary case `E + S < 1/512` uses a saving on the last prefix query.
`Proof/Direct/SourceBudgetExhaustion.lean` proves that exhausting the source budget
freezes its hash cache, and that a last nonencoding hash cannot create an accepted
encoding in a previously rejecting cache. `SourceTerminalRejection.lean` rules out
cached first-lane witnesses on those continuations and preserves the acceptance
factor for their actual verification phase.
`TerminalCutSoundness.lean` transfers this criterion to the public cache and counters.
`TerminalPrunedPrefix.lean` implements the cut and preserves the budget and completed
execution invariants. Its source coupling certifies that each cut rejects cached
first-lane witnesses; `TerminalAcceptedCoupling.lean` retains the joint acceptance
and hit guarantees needed for the probability bound.
`SourceSigningCost.lean` proves that every signing request consumes at least two
source-budget units. The public prefix therefore also stops signing with at most
one unit left and stops all direct hashing at exhaustion. `TerminalQuiescence.lean`
proves that exhausted continuations emit no further monitor actions.
`TerminalActivityBudget.lean` proves a strict saving of one hazard query whenever
the public encoding counters stay zero. `TerminalActivityCoupling.lean` also
preserves that strict saving on early cuts. `SourceEncodingActivity.lean` bounds
the probability of any source encoding or signing activity by `E + S`.
`TerminalActivityCancellation.lean` transfers both terminal and deciding-probe
charges through the same coupling. `TerminalActivityBound.lean` consequently bounds
cached first-lane witnesses by `(q - 1 + 2(E + S)) / 2^128` for positive budgets.
`TerminalMixedFirstLane.lean` averages this saving over the fresh fallback encoding
and includes the fresh encoding-collision contribution. `Proof/Modes/Signer.lean`
combines the result with the secondary loss and proves the general 127-bit bound:
small credit pays the remaining verification allowance from the saved query, while
credit at least `1/512` uses the existing encoding reserve. The root module combines
this theorem with the other five basis results and checks the axioms of the complete
`XmssSufCmaExactStatement` proof.
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

For the attack against 128 bits, `Proof/Attack/EncodingNeighbors.lean` proves that
every valid encoding has at least 392 distinct valid neighboring digests obtained by decreasing
one digit and increasing another. `Proof/Attack/HashSearch.lean` provides
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
than `5/64`. `Proof/Attack/NeighborSeeded.lean` proves exact equality of its reference and
deterministic seeded advantages, using its single signing request and absence of
seed-derivation queries. `Proof/Attack/NeighborBudget.lean` bounds key generation, signing,
the adversary, verification, and the single request by `2^124 + 2^122` in total, whose ratio to
`2^128` is `5/64`. `Proof/Attack/NeighborAccounting.lean` connects these component bounds
to the statement's counted experiment, proves the unchanged everything-counted attack claim,
and completes the attack against 128 bits.

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
