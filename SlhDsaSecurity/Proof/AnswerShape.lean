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
    RecordedTail.countAllHashes_map, recordedRun_map, BlockViews.recordedRun,
    RecorderView.recorderOf_cache]
  rfl

/-- **An event that reads no record is the same event at either run.** -/
theorem probEvent_fusedTail (adversary : Adversary)
    (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec)
    (event : (Outcome × Nat) × SplitPrefix.SplitState → Prop) :
    Pr[fun result => event (forgetRecord result) | FusedCoverage.fusedTail adversary walk] =
      Pr[event | AnswerJoin.answerRecordedRun adversary walk] := by
  rw [← map_fusedTail, probEvent_map]
  rfl

/-! ## The obligation, discharged down to three named hypotheses

`AnswerJoin.answerRecordedBound_of_parts` proves the bound above from the three things the
answer side does not own, so composing the two leaves exactly those three in the open. Two are
facts about the game — the disclosing recording is short, and the recorder's disclosing test
agrees with the signing log — and the third is the narrowing's leftover, which the module
docstring of `AnswerJoin` explains cannot be answered where it is asked and will be retired by
the weakened cover rather than paid.

Composing them here rather than leaving it to the assembly is the point of this file: if the
answer side's statement ever drifts from what `answerChargedLate_of_recordedBound` consumes,
this definition stops elaborating, and it stops elaborating here. -/

/-! ## The same move at the defect the target now instantiates

`FinalAssembly.lateOrSeed` is `LateProbes.Ordering ∨ AnswerCoverage.ForgerySeedRandomised`, so
`AnswerChargedLate`'s `¬ late` is two conjuncts by `not_or` — exactly the two the answer side
carries. Nothing about the presentation changes: the same `map_fusedTail` equality moves the
event, and the only work is reordering a conjunction.

What this buys is that **`hseed` leaves the obligation entirely.** The answer half no longer
owes a probability bound at a fixed walk, where it has none; the complement is charged on the
shared side, at `seedUnits`, where the seed is still random.

And the conclusion is `Obligations.AnswerChargedAt Target.answerDefectProved`, not the six-unit
`AnswerChargedLate`: this side proves `q / 2 ^ 128 + 1 / 2 ^ 141` and now says so, which is what
frees the four units of `2 ^ -128` the ledger was holding for a `2 ^ -126` nothing spends. -/

set_option maxHeartbeats 1000000 in
/-- **The answer obligation at `lateOrSeed`, from the bound at the answer side's own run.** -/
theorem answerChargedLateSeed_of_recordedBound
    (hbound : ∀ (q : Nat) (adversary : Adversary), 1 ≤ q → HasTotalBudget adversary q →
      ∀ walk ∈ support graphWalk, GoodWalk walk →
        Pr[fun result : (Outcome × Nat) × SplitPrefix.SplitState =>
            AnswerBad ((walk.1, result.1), result.2.1) ∧
              ¬ AnswerCoverage.ForgerySeedRandomised walk.1.1.2.1
                (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
                (result.1, result.2.1) ∧
              ¬ SplitWitness.LateDisclosure walk.1.1.2.1
                (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2) result |
          AnswerJoin.answerRecordedRun adversary walk] ≤
          (q : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + Target.answerDefectProved) :
    Obligations.AnswerChargedAt Target.answerDefectProved FusedCoverage.fusedTail
      FinalAssembly.forgetFused FinalAssembly.lateOrSeed := by
  intro q adversary hq hbudget walk hwalk hgood
  refine le_trans (le_of_eq ?_) (hbound q adversary hq hbudget walk hwalk hgood)
  rw [← map_fusedTail, probEvent_map]
  refine probEvent_congr' (fun result _ => ?_) rfl
  simp only [Function.comp_def, FinalAssembly.lateOrSeed, not_or]
  constructor
  · rintro ⟨hbad, hlate, hseed⟩; exact ⟨hbad, hseed, hlate⟩
  · rintro ⟨hbad, hseed, hlate⟩; exact ⟨hbad, hlate, hseed⟩

set_option maxHeartbeats 1000000 in
/-- **The answer obligation from two parts, with no `hseed`.** Both are facts about the game that
the carrier proves: the disclosing recording is one entry per served request, and the recorder's
disclosing test is the signing log. The narrowed class demand rides in `hjoinNarrow`, which the
weakening of `SplitWitness.Served.mem_records_of_covered` discharges.

Compare `answerChargedLate_of_parts` above, which still owes `hseed`; this is that with the
leftover moved into the event, where `FinalAssembly.lateOrSeed` collects it. -/
theorem answerChargedLateSeed_of_parts {inside outside : QueryKind} (hne : inside ≠ outside)
    (hjoinNarrow : ∀ (adversary : Adversary)
      (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec),
      walk ∈ support graphWalk → GoodWalk walk →
      ∀ result ∈ support (BlockViews.recordedRun
        (SplitWitness.disclosingKeep walk.1.1.2.1
          (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
        (SplitWitness.targetKeep walk.1.1.2.1
          (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
        (countQueries (ClassGrowth.splitCost (CombinedCharge.IsMessageInput
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2))
          inside outside) (afterSeeds adversary walk.1.1)) walk.2),
        SplitWitness.CoveredAtKeep walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            ((result.1.1, result.1.2 inside + result.1.2 outside), result.2.1) →
          ¬ AnswerCoverage.ForgerySeedRandomised walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            ((result.1.1, result.1.2 inside + result.1.2 outside), result.2.1) →
          ¬ SplitWitness.LateDisclosure walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            ((result.1.1, result.1.2 inside + result.1.2 outside), result.2) →
          BlockViews.TargetCovered result)
    (hleftBound : ∀ (adversary : Adversary)
      (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec),
      walk ∈ support graphWalk → GoodWalk walk →
      ∀ result ∈ support (AnswerJoin.answerRecordedRun adversary walk),
        result.2.2.1.length ≤ signingLimit)
    (hdisclosing : ∀ (adversary : Adversary)
      (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec),
      walk ∈ support graphWalk → GoodWalk walk →
      ∀ result ∈ support (AnswerJoin.answerRecordedRun adversary walk), ∀ input : Bytes,
        ServedLog.servedLog
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            (result.1, result.2.1) input ↔
          SplitWitness.disclosingKeep walk.1.1.2.1
            (SplitCharged.generatedKey walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2)
            input result.2.1) :
    Obligations.AnswerChargedAt Target.answerDefectProved FusedCoverage.fusedTail
      FinalAssembly.forgetFused FinalAssembly.lateOrSeed :=
  answerChargedLateSeed_of_recordedBound
    (AnswerJoin.answerRecordedBound_narrow_of_parts hne hjoinNarrow hleftBound hdisclosing)

end SlhDsaSecurity.AnswerShape
