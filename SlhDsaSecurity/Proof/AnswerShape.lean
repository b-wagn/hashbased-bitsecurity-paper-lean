import SlhDsaSecurity.Proof.FinalAssembly
import SlhDsaSecurity.Proof.AnswerJoin

/-!
# The answer obligation's presentation, and nothing else

`FinalAssembly.target_of_producers` now asks the answer side for its bound at
`FusedCoverage.fusedTail`. The side proves it at `AnswerJoin.answerRecordedRun` — the same
recorder, over the game without its adversary-and-verifier record. This file is the step
between, and it is the only step between: the two runs are the *same computation* up to a map
on the value, so the bound transports by `probEvent_map` and nothing is lost or assumed.

## What does and does not transport

Both conjuncts of the obligation's event factor through

    forget result = ((result.1.1.1, result.1.2), result.2)

which drops the record and keeps the whole recorder state. `AnswerBad` reads the outcome, the
count and the cache; the ordering defect reads the target recording and the cache, and
`SplitWitness.Served.Late` touches nothing else — so it is the *same proposition* at either
value type, not a transported one.

What does **not** factor is `FinalAssembly.forgetFused`, which drops the recordings too. That
is the whole reason the target had to be restated at a refining tail: the ordering defect is
invisible to the map the target forgets along, and visible to this one. The two maps differ in
exactly the component the defect reads, and `forgetFused` is this file's `forget` followed by
dropping it.

## Why this is a file and not three lines inside the answer side

The answer side's hypotheses are read at the split-counted presentation and bridged to the
recorder once, on its own side. Putting the presentation move here keeps that bridge where its
owner can see it, and means a mismatch between what the final assembly asks and what the answer
side proves surfaces as a failure to elaborate `answerChargedLate_of_recordedBound` rather than
inside a proof that is doing something else.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.AnswerShape

open Security CanonicalGraph WarmedGame RoutedSplit Target

/-- The map the answer side's bound is transported along: drop the record, keep the state. -/
def forgetRecord (result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) :
    (Outcome × Nat) × SplitPrefix.SplitState :=
  ((result.1.1.1, result.1.2), result.2)

/-- **`FinalAssembly.forgetFused` is this file's map, followed by dropping the recordings.** -/
theorem forgetFused_eq (result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState) :
    FinalAssembly.forgetFused result = ((forgetRecord result).1, (forgetRecord result).2.1) :=
  rfl

/-- **The recorder is natural in the computation's value.** Mapping the computation and mapping
the run's value are the same thing, because the recorder never reads the value. -/
theorem recordedRun_map {α β : Type} (leftKeep rightKeep : Bytes → QueryCache HashSpec → Prop)
    (f : α → β) (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    BlockViews.recordedRun leftKeep rightKeep (f <$> computation) cache =
      (fun z : α × SplitPrefix.SplitState => (f z.1, z.2)) <$>
        BlockViews.recordedRun leftKeep rightKeep computation cache := by
  rw [BlockViews.recordedRun, BlockViews.recordedRun, simulateQ_map, StateT.run_map]

/-- **The fused tail is the answer side's recorded run, with the record carried along.** An
equality of computations: the recorder answers both runs identically and the only difference is
what the game returns. -/
theorem map_fusedTail (adversary : Adversary)
    (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) :
    forgetRecord <$> FusedCoverage.fusedTail adversary walk =
      AnswerJoin.answerRecordedRun adversary walk := by
  rw [AnswerJoin.answerRecordedRun, ← RecordedTail.map_recordedAfterSeeds,
    RecordedTail.countAllHashes_map, recordedRun_map]
  rfl

/-- **An event that reads no record is the same event at either run.** -/
theorem probEvent_fusedTail (adversary : Adversary)
    (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec)
    (event : (Outcome × Nat) × SplitPrefix.SplitState → Prop) :
    Pr[fun result => event (forgetRecord result) | FusedCoverage.fusedTail adversary walk] =
      Pr[event | AnswerJoin.answerRecordedRun adversary walk] := by
  rw [← map_fusedTail, probEvent_map]
  rfl

/-- **The answer obligation, from the bound at the answer side's own run.** The hypothesis is
the side's conclusion with the ordering defect ruled out pointwise rather than assumed of the
support, and with the walk's key — both already its conventions. -/
theorem answerChargedLate_of_recordedBound
    (hbound : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      ∀ walk ∈ support graphWalk, GoodWalk walk →
        Pr[fun result : (Outcome × Nat) × SplitPrefix.SplitState =>
            AnswerBad ((walk.1, result.1), result.2.1) ∧
              ¬ SplitWitness.LateDisclosure walk.1.1.2.1
                (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) result |
          AnswerJoin.answerRecordedRun adversary walk] ≤
          (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
            ((1 : ℝ≥0∞) / ((2 ^ 126 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 141 : Nat) : ℝ≥0∞))) :
    Obligations.AnswerChargedLate FusedCoverage.fusedTail FinalAssembly.forgetFused
      LateProbes.Ordering := by
  intro q adversary hq hbudget walk hwalk hgood
  calc Pr[fun result : ((Outcome × Multiset Bytes) × Nat) × SplitPrefix.SplitState =>
          AnswerBad ((walk.1, (FinalAssembly.forgetFused result).1),
              (FinalAssembly.forgetFused result).2) ∧
            ¬ LateProbes.Ordering (walk, result) | FusedCoverage.fusedTail adversary walk]
      = Pr[fun result : (Outcome × Nat) × SplitPrefix.SplitState =>
            AnswerBad ((walk.1, result.1), result.2.1) ∧
              ¬ SplitWitness.LateDisclosure walk.1.1.2.1
                (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) result |
          AnswerJoin.answerRecordedRun adversary walk] := by
        rw [← map_fusedTail, probEvent_map]
        rfl
    _ ≤ _ := hbound q adversary hq hbudget walk hwalk hgood

end SlhDsaSecurity.AnswerShape
