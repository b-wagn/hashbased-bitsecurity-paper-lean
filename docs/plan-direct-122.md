# Direct-mode SUF-CMA at 122 bits: completed proof

Target: `XmssSufCmaDirectStatement` at 122 bits, i.e. for every adversary with at most `D ≥ 1`
direct hash queries, `Pr[win] ≤ D / 2^122 = 64·D / 2^128`.

## Status

`XmssSecurity.xmss_sufCma_direct_122` is proved and imported by the root module. Its axiom guard
permits only `propext`, `Classical.choice`, and `Quot.sound`. The statement layer is unchanged.

The completed route is:

- `DecidingClassification`, `DecidingCache`, `DecidingPrefix`, and `DecidingCollision`: a winning
  forgery without an encoding event or a hidden deciding value has a collision on its deciding path.
- `DecidingSecondLane`: the unconditional bound `(D + 41) / 2^128`.
- `DecidingFirstLaneCoupling`: stop the source/eager coupling before verification, with budget `D`.
- `DecidingProbe`: select the same deciding chain using public reveal queries only at coordinates
  at or above the signed digit, then emit one probe. Selection has zero hazards; the probe has one.
- `DecidingPrefixCoverage`, `DecidingPrefixEvent`, `DecidingPrefixProgram`, and
  `DecidingPrefixBound`: the prefix event has probability at most `(D + 1) / 2^128`.
- `DecidingPrefixProjection`, `DecidingPrefixStability`, and `DecidingFirstLaneBridge`: move the
  full winning event to this prefix after querying the forged encoding, giving `(D + 2) / 2^128`.
- `DecidingSecurity`: combine both lanes, prehits, and seed guessing, then transfer to the
  statement's semantically bounded adversaries.

The first-lane hidden-value branch includes `won = true`. The winning condition provides a valid
signing transcript; dropping it would permit repeated signing requests to reveal values below an
earlier signature's digit without spending a direct query.

The actual final bound is

```
(D + 2) / 2^128 + 2^32 * (D + 1) / 2^192 + (D + 42) / 2^128 + D / 2^256
  ≤ D / 2^122, for D ≥ 1.
```

The extra unit in the second lane comes from applying both lanes to the adversary augmented with
the forged encoding query. That extra query leaves the game's outcome distribution unchanged.

The following sections record the original proof plan; the details above describe the implemented
route. Attack witnesses and the remaining 127-bit counting modes are separate, still-open tasks.

## Where the original proof (119 bits) loses

`Proof/Direct/Assemble.lean` bounds the idealized scheme by four terms:

| term | bound | source |
|---|---|---|
| first lane (encoding event without prehit, or a hidden chain value in the forgery) | `(D + 133 + 42) / 2^128` | eager/probe coupling, fuel = adversary hazards + verifier's 133 hashes + 42 forgery probes |
| encoding prehit | `2^32 · D / 2^192` | potential argument |
| structural collisions (chain, suffix, leaf, merkle) | `(D + 133) / 2^128` | expected number of "moved" queries, verifier charged 133 |
| seed guessing (real scheme) | `D / 2^256` | |

Sum ≈ `(2·D + 308) / 2^128`, so `bits = 119` at `D = 1`. The verifier's 133 queries are charged
in both lanes although a winning verification can only exploit a few of them.

## The deciding path

Fix a winning run: forgery `(idx*, m*, σ*)`, forged encoding `x*`, honest chain values
`c_i^{(k)}` at `idx*`, honest leaf and path nodes. If a signature at `idx*` with encoding `x` was
returned, chain `i` is *trivial* when `x*_i ≥ x_i` and `σ*_i = c_i^{(x*_i)}` (the value the
adversary can compute from the signature). The *deciding chain* `i0` is the smallest non-trivial
chain (every chain is non-trivial if no signature at `idx*` was returned).

Claim: a winning run exhibits one of
1. **encoding event**: forged encoding input ≠ signed input, same digest (needs `i0` undefined,
   i.e. all chains trivial, hence `x* = x`, hence equal digests);
2. **deciding probe**: `x*_{i0} < x_{i0}` (or no signature) and `σ*_{i0} = c_{i0}^{(x*_{i0})}`,
   a hidden value guessed;
3. **deciding collision**: a hash input on the deciding path, i.e. a chain input of chain `i0`
   at `idx*` (≤ 7 positions), the leaf input at `idx*` (1), or a Merkle input on `idx*`'s path
   (32 levels), differs from the honest input at that position but has the same digest.

Proof sketch of 3: walk the verification top-down. Let `ℓ` be the highest level whose Merkle input
differs from the honest one; its output must equal the honest node (root, or the next level's
input agrees), a collision at level `ℓ`. If all Merkle inputs agree, the leaf and path are honest;
if the leaf input differs, a leaf collision; else all chain ends are honest; chain `i0` is
non-trivial, so either it is a hidden-value guess (case 2) or its walk reaches the honest end
from a different value, a collision at the last position where the walks differ.

For every input of case 3 the query that created it was made either by the adversary (charged
to `D`, any position) or fresh by the verifier (charged only if on the deciding path, ≤ 40).
The signer only queries encoding inputs; key generation only honest inputs.

## New accounting

* first lane: encoding event ∧ ¬prehit, or deciding probe: fuel `D + 2`
  (adversary hazards, one encoding query, one probe);
* prehit: unchanged;
* second lane: adversary-phase structural collision ≤ `D / 2^128`, plus verification-phase
  collision on the deciding path ≤ `40 / 2^128`;
* seed: unchanged.

Total `≤ (2·D + 42 + ε) / 2^128 ≤ 64·D / 2^128` for `D ≥ 1`. An attack exceeding `1 / 2^123` at charged budget 1 is still needed to prove exactness.
Choosing a low digit from a signature also needs justification when the encoding hash query is charged.

## Lean architecture

### The adversary with the forged encoding query (`A'`)
Both lanes need the forged encoding `x*` to be known before verification. Replace `A` by
`A' = A; query the encoding input of its own forgery; output`. `A'` has direct bound `D + 1`; the
game's distribution of (outcome, final cache) is unchanged (the verifier's first query is a cache
hit). Everything below is proved for `A'`.

### Second lane (`Proof/Direct/Deciding*.lean`)
Definitions (`Deciding.lean`): `returnedAt`, `signedEncoding`, `forgedEncoding`,
`honestChainValue`, `ChainTrivial`, `decidingChain`, `DecidingChainValueRevealed`,
`IsDecidingInput`, `decidingTargetInput` (= `keygenStructuralTargetInput` on deciding inputs,
identity elsewhere).

Theorems:
* `DecidingOrientation`: for executions of `detailedGameAfterKeygen` split as adversary phase
  (cache `C_k → C_v`) then verification (`C_v → C_f`): `won ∧ ¬encodingEvent ∧
  ¬DecidingChainValueRevealed ∧ ¬AdaptiveFreshDigestCollisionWith C_k C_v structural ⇒
  AdaptiveFreshDigestCollisionWith C_v C_f (decidingTargetInput sk C_k idx* i0)`.
* `DecidingVerifierCount`: `verify` makes at most 40 queries whose input is moved by the deciding
  map (syntactic `IsQueryBoundP`).
* `DecidingSecondLane`: `Pr[won ∧ ¬enc ∧ ¬revealed] ≤ (D + 1 + 40) / 2^128` via
  `mixed_adaptiveFreshDigestCollisionWith_le_expected_moved` (adversary phase, target
  `keygenStructuralTargetInput`) and
  `mixed_adaptiveFreshDigestCollision_after_prefix_le_expectedMovedContinuation` (verification,
  target `decidingTargetInput`).

### First lane (`Proof/Direct/DecidingFirstLane*.lean`)
Keep the whole eager/probe stack for the adversary part. New detailed execution in the eager
world: adversary (`A'`), then emit the single probe
`probe (i0, idx*, x*_{i0}) σ*_{i0}` (computed from the eager state: forgery, signing log, forged
encoding), then the verifier. Couple with the source program (adversary, then verifier) by the
generic `relTriple_simulateQ_bind_bounded_firstLane` with `countLimit = hitLimit = D + 2`:
the post-condition after the adversary step is "good ∨ hit"; the finish step shows
`bad' ⇒ CombinedHit (enforce (D+2) (history ++ [probe]))` from the good state relation alone
(the refined bad event is determined before verification), and `CombinedHit.enforce_append_of_prefix`
carries it over the verifier's actions. Probability: `public_eager_enforcedHit_probability_le`
for the new public program with fuel `D + 2`.

The refined first-lane bad event `bad'` = `(WinningOutcomeBadEventOccurs .encoding ∧ ¬prehit) ∨
(won = true ∧ DecidingChainValueRevealed)`. Its chain branch is the existing
`GlobalWinningChainValueRevealed` restricted to chain `i0` (origin lemma
`chainValueRevealed_afterKeygen_has_origin` applies at `i0`).

### Assembly (`Proof/Direct/Assemble.lean`)
`forgeAdvantage A = forgeAdvantage A' ≤ Pr[bad'] + Pr[prehit] + Pr[won ∧ ¬enc ∧ ¬revealed]`
then the arithmetic `(D+3) + 2^32(D+1)/2^192 + (D+41) + D/2^256 ≤ 64·D/2^128` for `D ≥ 1`
(check: at `D = 1`: `4 + 42 + ε ≤ 64`).
