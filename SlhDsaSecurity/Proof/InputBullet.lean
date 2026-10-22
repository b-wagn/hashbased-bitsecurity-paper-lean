import SlhDsaSecurity.Proof.SharedAssembly
import SlhDsaSecurity.Proof.ProbeContainment
import SlhDsaSecurity.Proof.RecordedChain
import SlhDsaSecurity.Proof.ServedBridge

/-!
# The input half's bullet, reduced to one inequality

`SharedAssembly.InputBullet` is what the join takes from this half: an event at the split pair,
bounded by an expected count plus `259`, over `2 ^ 128`. This file does the two steps between
that and the thing the half's chain actually produces, and they are both free:

* **the ordering term is dropped**, because the bound below is proved for the strictly larger
  event without it — so the bullet holds for *any* `ordering`, of any type, and the defect's
  owner may restate it however they like without this half moving;
* **the pair is forgotten**, by `LateProbes.probEvent_forget` at
  `FusedCoverage.forgetsTo` — the transport the split pair was introduced for;
* **the count is slack**, since `RoutedSplit.InputBad` is an existential over the forgery's
  `259` claimed candidates and nothing else, so the half owes a constant and the expected count
  beside it is only ever added to.

What is left is `bullet_of_bound`'s hypothesis, and that is the whole of the half's remaining
work: the forgery's claims, charged at the recorded paired run.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.InputBullet

open Security WarmedGame RoutedSplit Target ClassExpectation SharedJoin RandomiserRecord
  LateProbes SharedAssembly

/-- **The bullet, from the one inequality the half's chain is converging on.** The ordering
predicate is untouched — the bound is proved without its conjunct — so this holds at whatever
shape that defect is eventually stated in. -/
theorem bullet_of_bound (adversary : Adversary) (ordering : SplitPair → Prop)
    (hbound : Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ InputBad (recordedTraceOf pair) |
        recordedPairedRun adversary] ≤
      ((259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    SharedAssembly.InputBullet adversary ordering := by
  classical
  refine le_trans (probEvent_mono (q := fun pair : SplitPair =>
    GoodWalk (forgetRecordings pair).1 ∧ InputBad (recordedTraceOf (forgetRecordings pair)))
    (fun pair _ hpair => ⟨hpair.1, hpair.2.1⟩)) ?_
  rw [probEvent_forget (FusedCoverage.forgetsTo adversary)
    (fun pair => GoodWalk pair.1 ∧ InputBad (recordedTraceOf pair))]
  exact le_trans hbound (ENNReal.div_le_div_right le_add_self _)

/-- The same, as the shape the half still owes: the claims charged at the recorded paired run,
with no walk fixed and no ordering term. -/
def ClaimsCharged (adversary : Adversary) : Prop :=
  Pr[fun pair : RecordedPair => GoodWalk pair.1 ∧ InputBad (recordedTraceOf pair) |
      recordedPairedRun adversary] ≤
    ((259 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)

/-- **The half's bullet, from the half's one remaining obligation.** -/
theorem bullet_of_claimsCharged (adversary : Adversary) (ordering : SplitPair → Prop)
    (hclaims : ClaimsCharged adversary) : SharedAssembly.InputBullet adversary ordering :=
  bullet_of_bound adversary ordering hclaims


/-! ## The agreement this half consumes, named so it can be aimed at

The half's charge reads disclosure from the **carrier** — that is what the handler carries and
what `RedrawCell`'s availability is a predicate of — while `RoutedSplit.InputBad` reads it from
the **log**, through `ServedLog.disclosedByLog`. `ServedBridge` is where the two meet, and what
it asks for is `ServedAgree`: the carrier's served set and the log's are each contained in the
other, at which point `disclosedAt_subset_disclosedByLog` and its converse make the two
disclosure sets one `Finset` and the entries and the event are instantiated at the same object.

**This is stated as a hypothesis rather than proved here on purpose.** It is the only thing
between this half and its bullet that belongs to another owner, and the shape it arrives in has
to be the shape consumed: an unapplied bridge is indistinguishable from a missing one. So it is
written at the run this half's chain ends at — the handler's run of the linked game at a drawn
table, started from the empty carrier — with the key the walk's table determines, the log the
run's own value carries, and the cache the game's, which is the handler's read through
`RedrawCell.unionCache`. If what arrives differs, this is where it fails to elaborate. -/

open WalkTable TableTail in
/-- **The agreement, at the run this half ends at.** -/
def AgreesAtHandler (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : CanonicalGraph.Cells × CanonicalGraph.Padding) : Prop :=
  ∀ (record : List (Bytes × HandlerCarrier.State)) (count : Nat)
    (z : ((((Forgery × Multiplicative RecordedQueries.Tally) ×
      (Bool × RecordedQueries.Tally)) × SigningLog)) × OpenCache.HandlerState),
    z ∈ support (handlerRun adversary prfSeed publicSeed table
      (HandlerCarrier.empty, record, count)) →
      ServedBridge.ServedAgree (keysOf prfSeed publicSeed table).2 z.2.1
        (((LinkedGame.outcomeOf z.1).1, (LinkedGame.outcomeOf z.1).1.counts.work),
          RedrawCell.unionCache publicSeed table z.2.1.cache)

end SlhDsaSecurity.InputBullet
