import SlhDsaSecurity.Proof.CarrierTail

/-!
# The run the answer side owes a bound at, when the tail is the carrier's

`CarrierTail.answerChargedLate_carrier_of_bound` asks for a bound at
`AnswerShape.forgetRecord <$> CarrierTail.carrierTail rightKeep adversary walk`, and deliberately
leaves that object unnamed, so that the side which has to prove the bound names it once rather
than two shapes drifting apart. This file is that name, and it is the only one.

## It is not `answerRecordedRun`, and there is no map between them

`AnswerJoin.answerRecordedRun` records against `SplitWitness.disclosingKeep`, a test on the
**cache**; the carrier records against `CarriedWitness.disclosingKeep`, which is
`HandlerCarrier.FilesLeft` — a comparison against the **frame in flight**. The two disagree by
construction, and the disagreement *is* the repair: it is what lets the carrier file a served
request whose digest input is already cached, and refuse the signer's own randomiser probe,
neither of which a cache test can do. `AnswerShape.forgetRecord` keeps the whole recorder state,
so the differing records sit inside the mapped value and no map carries one run to the other.

There is a second, independent obstruction: `answerRecordedRun` is one computation under
`RecorderView.recorderOf` from `walk.2`, while the carrier tail is three-stage, bracketed, under
`RecorderView.noticingRecorderOf`, with its count read off the handler. A one-computation run has
no brackets, so no serving, so an empty disclosing record.

## What *does* carry across

Not a map — the interface the charge consumes.
`CoverageCount.prob_bad_or_coverage_le_of_charges` takes the structural clause at its own
expected count, the coverage clause at its own, and the pathwise fact that the two counts share
one budget; it mentions no recorder and no run. Those three propositions at this run are what the
answer side still owes, and the coverage one is the hard half, being the tape factorisation at a
bracketed noticing run.

## And one premise that survives the change of recorder

`RecorderView.noticingRecorderOf` runs `recorderOf` at `CacheView.onQuery state.1 input`, and
`RecorderView.cacheOf_onQuery` says the notice leaves the cache alone. So `appendedOf`'s guard is
still `CacheView.cacheOf state.1 input = none`: the carrier files on a **fresh draw only**,
exactly as the cache recorder does, and `noticingRecorderOf_run_inr_some` shows a cache hit
leaves both recordings untouched. Everything that rests on a filed entry being a fresh uniform
answer — `CoverageCount.rightRecord_length_le_count`, and the per-entry rate the tape
factorisation spends — keeps its premise. What the notice changes is which state the two *tests*
are read at, which is the point of the repair and costs those steps nothing.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.AnswerCarrier

open Security CanonicalGraph WarmedGame Target

/-- The run the answer side owes a bound at, when the tail is the carrier's. -/
noncomputable def answerCarrierRun
    (rightKeep : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → Bytes →
      HandlerCarrier.State → Prop)
    (adversary : Adversary)
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec)) :
    ProbComp ((Outcome × Nat) × SplitPrefix.SplitState) :=
  AnswerShape.forgetRecord <$> CarrierTail.carrierTail rightKeep adversary walk

/-- **It is the run the presentation move asks for**, definitionally, so a bound stated at this
name discharges the obligation through `CarrierTail.answerChargedLate_carrier_of_bound` with no
adapter between them. -/
theorem answerCarrierRun_eq
    (rightKeep : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → Bytes →
      HandlerCarrier.State → Prop)
    (adversary : Adversary)
    (walk : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec)) :
    answerCarrierRun rightKeep adversary walk =
      AnswerShape.forgetRecord <$> CarrierTail.carrierTail rightKeep adversary walk := rfl

/-- **The obligation at the carrier tail, from a bound stated at the named run.** -/
theorem answerChargedLate_of_carrierBound
    (rightKeep : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → Bytes →
      HandlerCarrier.State → Prop)
    (hbound : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → Security.HasTotalBudget adversary q →
      ∀ walk ∈ support WarmedGame.graphWalk, Target.GoodWalk walk →
        Pr[fun result : (Outcome × Nat) × SplitPrefix.SplitState =>
            RoutedSplit.AnswerBad ((walk.1, result.1), result.2.1) ∧
              ¬ SplitWitness.LateDisclosure walk.1.1.2.1
                (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) result |
          answerCarrierRun rightKeep adversary walk] ≤
          (q : ENNReal) / ((2 ^ 128 : Nat) : ENNReal) +
            ((1 : ENNReal) / ((2 ^ 126 : Nat) : ENNReal) +
              (1 : ENNReal) / ((2 ^ 141 : Nat) : ENNReal))) :
    Obligations.AnswerChargedLate (CarrierTail.carrierTail rightKeep)
      FinalAssembly.forgetFused LateProbes.Ordering :=
  CarrierTail.answerChargedLate_carrier_of_bound rightKeep hbound

end SlhDsaSecurity.AnswerCarrier
