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

end SlhDsaSecurity.AnswerShape
