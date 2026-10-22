import SlhDsaSecurity.Proof.HandlerLenient
import SlhDsaSecurity.Proof.ServingCarrier

/-!
# Availability, read off what the carrier served

`HandlerLenient`'s charge is parametric in a `signedAt`: which FORS positions a state has
disclosed. This file makes the choice, and it makes it at the **served set** rather than at the
cache.

**Why not the cache.** `CacheAvailability.signedAt` reads "some cached input of the signer's own
shape has an answer selecting this position". That is a function of the cache alone, which is
what made it usable before the handler carried anything — but it over-approximates the signing
log, because the adversary can cache a message-class input without ever having had it signed.
The gap is real and it was charged separately, as the coverage event. The carrier closes it:
`HandlerCarrier.State.served` is written by the signing oracle and by nothing else, so
"disclosed" is "served and cached", with no slack to charge for.

**Why the choice is monotone for free.** `CacheAvailability.signedAt_mono` needed
`signerRandomised_mono` — the cache test had to be re-established at the later cache. Here both
halves of `HandlerCarrier.Grows` are used directly: served inputs stay served, cache entries
keep their answers. That is the whole proof, and it is the reason the served reading is the one
the charge wants rather than merely one it tolerates.

**What this file does not decide.** The notion itself is `ServedDisclosure.servedAt` at an
abstract state and `ServingCarrier.disclosedAt` at the carrier; both already existed. What was
missing is the statement at the shape `HandlerLenient` asks for — availability, not the
`Finset`, with `HandlerCarrier.Grows` as the growth — and the two charges instantiated at it so
that no consumer re-makes the choice.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.CarrierAvailability

open Security CanonicalGraph OpenCache RedrawCell HandlerFacts SensitiveQuery ChargedProbe
open HandlerLenient

/-- **The availability a carrier reads**: the honest digit on the WOTS side, and on the FORS
side exactly the positions the carrier's served requests disclosed. -/
noncomputable abbrev availableAt [HasQuery HashSpec Id] (secretSeed publicSeed : Digest)
    (state : HandlerCarrier.State) (node : Node) : Prop :=
  Available (GraphStakes.honestRevealed secretSeed publicSeed)
    (ServingCarrier.disclosedAt state) node

/-- **A released cell stays released**, along the growth the carrier actually performs. This is
the `hmono` every charge in `HandlerLenient` asks for, and it is `ServedDisclosure.available_mono`
with the two halves of `HandlerCarrier.Grows` handed over one each. -/
theorem availableAt_mono [HasQuery HashSpec Id] (secretSeed publicSeed : Digest)
    (left right : HandlerCarrier.State) (hgrow : HandlerCarrier.Grows left right) (node : Node)
    (havailable : availableAt secretSeed publicSeed left node) :
    availableAt secretSeed publicSeed right node :=
  ServedDisclosure.available_mono (GraphStakes.honestRevealed secretSeed publicSeed)
    HandlerCarrier.Served HandlerCarrier.cacheOf left right hgrow.2 hgrow.1 node havailable

/-! ## The two charges at the choice

Restated rather than cited, so that the choice is made once. A consumer that wanted a different
`signedAt` would have to say so by not using these. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The charge at the carrier's own disclosure.** `HandlerLenient.prob_game_sensitive_honest_le`
with the choice made and monotonicity discharged. Capped, so not the form a half sharing its
budget may use. -/
theorem prob_game_sensitive_carrier_le [HasQuery HashSpec Id] {α : Type}
    (publicSeed secretSeed : Digest)
    (lenientImpl strictImpl :
      Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {lenientAllowed : CanonicalGraph.Node → Prop}
    (hlenientFacts : Facts publicSeed (fun _ _ => True) lenientAllowed lenientImpl)
    {allowed : CanonicalGraph.Node → Prop}
    (hstrictFacts : Facts publicSeed
      (fun cache node => CanonicalGraph.Available
        (GraphStakes.honestRevealed secretSeed publicSeed)
        (ServingCarrier.disclosedAt cache) node) allowed strictImpl)
    (hlenient : Lenient publicSeed
      (fun cache node => CanonicalGraph.Available
        (GraphStakes.honestRevealed secretSeed publicSeed)
        (ServingCarrier.disclosedAt cache) node) lenientImpl strictImpl)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : Cells × Padding → OracleComp OracleWorld α)
    (touched : CanonicalGraph.Node → Prop)
    (hcover : ∀ node, ¬ touched node → allowed node)
    (htouched : ∀ left right : Cells × Padding,
      (∀ node, touched node → left.1 node = right.1 node) →
        computation left = computation right)
    (hopen : ∀ node, touched node → node ≠ CanonicalGraph.Node.secretSeed →
      ∀ cache, CanonicalGraph.Available (GraphStakes.honestRevealed secretSeed publicSeed)
        (ServingCarrier.disclosedAt cache) node)
    (inner : HandlerState) (hinner : inner.2.1 = []) (limit : Nat)
    (hlimit : ∀ z ∈ support (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        (simulateQ (withFlag (strictImpl (cells, pad)))
          (computation (cells, pad))).run (inner, false)),
      z.2.1.2.1.length ≤ limit) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cells => pair.1.2.2 = true | (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (sensitiveFlagged publicSeed
          (fun cache node => CanonicalGraph.Available
            (GraphStakes.honestRevealed secretSeed publicSeed)
            (ServingCarrier.disclosedAt cache) node) lenientImpl (cells, pad))
          (computation (cells, pad))).run (inner, false)
        pure (result, cells))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        Pr[fun pair : (α × (HandlerState × Bool)) × Cells =>
            ∃ entry ∈ pair.1.2.1.2.1, RedrawCell.SensitiveAtSeed (GraphStakes.stakes publicSeed)
              (fun cache node => ¬ CanonicalGraph.Available
                (GraphStakes.honestRevealed secretSeed publicSeed)
                (ServingCarrier.disclosedAt cache) node) pair.2 entry.2 entry.1 | (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (withFlag (strictImpl (cells, pad)))
            (computation (cells, pad))).run (inner, false)
          pure (result, cells))] :=
  HandlerLenient.prob_game_sensitive_honest_le publicSeed secretSeed ServingCarrier.disclosedAt
    lenientImpl strictImpl hlenientFacts hstrictFacts hlenient (availableAt_mono secretSeed
      publicSeed) stall computation touched hcover htouched hopen inner hinner limit hlimit

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The same charge, left at its expectation.** This is
`HandlerLenient.prob_game_sensitive_honest_le_canonical`
with the choice made and monotonicity discharged. This is the shape `InputBullet.ClaimsCharged`
is stated at. -/
theorem prob_game_sensitive_carrier_le_canonical [HasQuery HashSpec Id] {α : Type}
    (publicSeed secretSeed : Digest)
    (lenientImpl strictImpl :
      Cells × Padding → QueryImpl OracleWorld (StateT HandlerState ProbComp))
    {lenientAllowed : CanonicalGraph.Node → Prop}
    (hlenientFacts : Facts publicSeed (fun _ _ => True) lenientAllowed lenientImpl)
    {allowed : CanonicalGraph.Node → Prop}
    (hstrictFacts : Facts publicSeed
      (fun cache node => CanonicalGraph.Available
        (GraphStakes.honestRevealed secretSeed publicSeed)
        (ServingCarrier.disclosedAt cache) node) allowed strictImpl)
    (hlenient : Lenient publicSeed
      (fun cache node => CanonicalGraph.Available
        (GraphStakes.honestRevealed secretSeed publicSeed)
        (ServingCarrier.disclosedAt cache) node) lenientImpl strictImpl)
    (stall : (t : OracleWorld.Domain) → OracleWorld.Range t)
    (computation : Cells × Padding → OracleComp OracleWorld α)
    (touched : CanonicalGraph.Node → Prop)
    (hcover : ∀ node, ¬ touched node → allowed node)
    (htouched : ∀ left right : Cells × Padding,
      (∀ node, touched node → left.1 node = right.1 node) →
        computation left = computation right)
    (hopen : ∀ node, touched node → node ≠ CanonicalGraph.Node.secretSeed →
      ∀ cache, CanonicalGraph.Available (GraphStakes.honestRevealed secretSeed publicSeed)
        (ServingCarrier.disclosedAt cache) node)
    (inner : HandlerState) (hinner : inner.2.1 = [])
    (keep : Bytes × HandlerCarrier.State → Bool)
    (hkeep : ∀ entry : Bytes × HandlerCarrier.State,
      RedrawCell.AimsSomewhere publicSeed entry.1 → keep entry = true) :
    Pr[fun pair : (α × (HandlerState × Bool)) × Cells => pair.1.2.2 = true | (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let pad ← ($ᵗ Padding : ProbComp Padding)
        let result ← (simulateQ (sensitiveFlagged publicSeed
          (fun cache node => CanonicalGraph.Available
            (GraphStakes.honestRevealed secretSeed publicSeed)
            (ServingCarrier.disclosedAt cache) node) lenientImpl (cells, pad))
          (computation (cells, pad))).run (inner, false)
        pure (result, cells))] ≤
      (∑' z : α × (HandlerState × Bool),
          Pr[= z | (do
            let cells ← ($ᵗ Cells : ProbComp Cells)
            let pad ← ($ᵗ Padding : ProbComp Padding)
            (simulateQ (withFlag (strictImpl (cells, pad)))
              (computation (cells, pad))).run (inner, false))] *
            (((z.2.1.2.1.dedup.filter keep).length : Nat) : ℝ≥0∞)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) +
        Pr[fun pair : (α × (HandlerState × Bool)) × Cells =>
            ∃ entry ∈ pair.1.2.1.2.1, RedrawCell.SensitiveAtSeed (GraphStakes.stakes publicSeed)
              (fun cache node => ¬ CanonicalGraph.Available
                (GraphStakes.honestRevealed secretSeed publicSeed)
                (ServingCarrier.disclosedAt cache) node) pair.2 entry.2 entry.1 | (do
          let cells ← ($ᵗ Cells : ProbComp Cells)
          let pad ← ($ᵗ Padding : ProbComp Padding)
          let result ← (simulateQ (withFlag (strictImpl (cells, pad)))
            (computation (cells, pad))).run (inner, false)
          pure (result, cells))] :=
  HandlerLenient.prob_game_sensitive_honest_le_canonical publicSeed secretSeed
    ServingCarrier.disclosedAt lenientImpl strictImpl hlenientFacts hstrictFacts hlenient
    (availableAt_mono secretSeed publicSeed) stall computation touched hcover htouched hopen
    inner hinner keep hkeep


end SlhDsaSecurity.CarrierAvailability
