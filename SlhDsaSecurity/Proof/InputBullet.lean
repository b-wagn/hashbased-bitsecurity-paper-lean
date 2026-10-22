import SlhDsaSecurity.Proof.SharedAssembly
import SlhDsaSecurity.Proof.ProbeContainment
import SlhDsaSecurity.Proof.RecordedChain

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

end SlhDsaSecurity.InputBullet
