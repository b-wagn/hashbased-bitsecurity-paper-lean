import SlhDsaSecurity.Proof.RecordedStripping
import SlhDsaSecurity.Proof.RecordedWalkTable
import SlhDsaSecurity.Proof.ProbeContainment
import SlhDsaSecurity.Proof.TableTail

/-!
# The recorded tail, carried to the handler

`TableTail` walks `WarmedGame.tail` down to the handler's own run. The input half's bound is
owed at the **recorded** tail, because the count it is paid from is the record's aiming part, so
the same walk has to be taken one presentation along, with the record kept at every step.

The steps are the same ones and each is an equality:

* the outer count is dropped — `RecordedTail.recordedTail` counts every hash call, and neither
  the event nor the count reads that total;
* the honest phase is stripped, which is `RecordedStripping.evalDist_run_recordedAfterSeeds` and
  is the step the containment cannot do without;
* the keys are handed in and the game becomes one computation, which `KeygenValue` and
  `LinkedGame` already state as equalities of runs;
* the handler starts from nothing, which is `RedrawCell.probEvent_rom_eq_lazy`.

**Both the probability and the count have to cross.** The join's bullet is a probability on the
left and an expectation on the right, so every step here is stated twice — once for `probEvent`
and once for `ClassExpectation.expected` — and a step that moved one without the other would
leave the two reading different runs, which is the mismatch this file exists to avoid.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.RecordedChain

open Security WarmedGame ClassExpectation

/-! ## The outer count, which nothing reads

`Security.countAllHashes` wraps the whole tail, and the record is inside it. Forgetting the
total is a projection, so the tail is the uncounted run read through it. -/

/-- **The uncounted recorded game is the recorded tail with its total forgotten.** -/
theorem run_recordedAfterSeeds_eq_map (adversary : Adversary)
    (start : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) :
    (simulateQ KeygenUniform.rom
        (RecordedTail.recordedAfterSeeds adversary start.1.1)).run start.2 =
      (fun result : ((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec =>
        (result.1.1, result.2)) <$> RecordedTail.recordedTail adversary start := by
  conv_lhs => rw [← RecordedBudget.map_countAllHashes
    (RecordedTail.recordedAfterSeeds adversary start.1.1)]
  rw [simulateQ_map, StateT.run_map, RecordedTail.recordedTail]

/-- **An event that does not read the total reads the uncounted run.** -/
theorem probEvent_recordedTail_uncounted (adversary : Adversary)
    (start : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec)
    (event : (Outcome × Multiset Bytes) × QueryCache HashSpec → Prop) :
    Pr[fun result => event (result.1.1, result.2) | RecordedTail.recordedTail adversary start] =
      Pr[event | (simulateQ KeygenUniform.rom
        (RecordedTail.recordedAfterSeeds adversary start.1.1)).run start.2] := by
  rw [run_recordedAfterSeeds_eq_map adversary start, probEvent_map]
  rfl

/-- **A count that does not read the total counts the uncounted run.** -/
theorem expected_recordedTail_uncounted (adversary : Adversary)
    (start : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec)
    (count : (Outcome × Multiset Bytes) × QueryCache HashSpec → Nat) :
    expected (RecordedTail.recordedTail adversary start)
        (fun result => count (result.1.1, result.2)) =
      expected ((simulateQ KeygenUniform.rom
        (RecordedTail.recordedAfterSeeds adversary start.1.1)).run start.2) count := by
  haveI : DecidableEq ((Outcome × Multiset Bytes) × QueryCache HashSpec) := Classical.decEq _
  rw [run_recordedAfterSeeds_eq_map adversary start, expected_map]

/-! ## The honest phase, stripped

The law is `RecordedStripping.evalDist_run_recordedAfterSeeds`, read at the walk's own cache,
where `StrippedGame.Extends` is reflexivity. -/

/-- **The recorded tail is the stripped recorded game, uncounted.** -/
theorem probEvent_recordedTail_stripped (adversary : Adversary)
    (start : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec)
    (event : (Outcome × Multiset Bytes) × QueryCache HashSpec → Prop) :
    Pr[fun result => event (result.1.1, result.2) | RecordedTail.recordedTail adversary start] =
      Pr[event | (simulateQ KeygenUniform.rom
        (RecordedQueries.recordedAfterSeeds adversary start.1.1 start.2)).run start.2] := by
  rw [probEvent_recordedTail_uncounted adversary start event]
  exact (probEvent_congr' (fun _ _ => Iff.rfl)
    (RecordedStripping.evalDist_run_recordedAfterSeeds adversary start.1.1 start.2 start.2
      (StrippedGame.Extends.refl start.2))).symm

/-- **And the count crosses with it.** -/
theorem expected_recordedTail_stripped (adversary : Adversary)
    (start : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec)
    (count : (Outcome × Multiset Bytes) × QueryCache HashSpec → Nat) :
    expected (RecordedTail.recordedTail adversary start)
        (fun result => count (result.1.1, result.2)) =
      expected ((simulateQ KeygenUniform.rom
        (RecordedQueries.recordedAfterSeeds adversary start.1.1 start.2)).run start.2) count := by
  rw [expected_recordedTail_uncounted adversary start count]
  exact (RecordedWalkTable.expected_congr
    (RecordedStripping.evalDist_run_recordedAfterSeeds adversary start.1.1 start.2 start.2
      (StrippedGame.Extends.refl start.2)) count).symm


/-! ## The keys handed in, the game linked, the handler started from nothing

The three remaining steps are already equalities of runs, so the record crosses them with
everything else: `KeygenValue.run_recordedAfterSeeds` replaces key generation by the value the
walk's cache determines, `LinkedGame.recordedAfterSeedsAt_eq` writes the game as one computation
under one handler, and `RedrawCell.probEvent_rom_eq_lazy` starts that handler from nothing. -/

open WalkTable TableTail in
/-- **The stripped recorded game at a drawn table is the linked game under the uncharged
handler.** -/
theorem run_recordedAfterSeeds_eq_linked (adversary : Adversary)
    (prfSeed publicSeed : Digest)
    (table : CanonicalGraph.Cells × CanonicalGraph.Padding) :
    (simulateQ KeygenUniform.rom (RecordedQueries.recordedAfterSeeds adversary
        ((walkOfTable prfSeed publicSeed table).1.1)
        (walkOfTable prfSeed publicSeed table).2)).run
          (walkOfTable prfSeed publicSeed table).2 =
      (fun z => (LinkedGame.outcomeOf z.1, z.2)) <$>
        linkedRun adversary prfSeed publicSeed table := by
  rw [show (simulateQ KeygenUniform.rom (RecordedQueries.recordedAfterSeeds adversary
      ((walkOfTable prfSeed publicSeed table).1.1)
      (walkOfTable prfSeed publicSeed table).2)).run
        (walkOfTable prfSeed publicSeed table).2 =
    (simulateQ KeygenUniform.rom (KeygenValue.recordedAfterSeedsAt adversary
      (keysOf prfSeed publicSeed table)
      (walkOfTable prfSeed publicSeed table).2)).run
        (walkOfTable prfSeed publicSeed table).2 from by
      rw [walkOfTable_cache prfSeed publicSeed table]
      exact KeygenValue.run_recordedAfterSeeds adversary
        (table.1 CanonicalGraph.Node.secretSeed, prfSeed, publicSeed)
        (CanonicalGraph.fullOutput table.1 table.2),
    LinkedGame.recordedAfterSeedsAt_eq, simulateQ_map, StateT.run_map, linkedRun]

open WalkTable TableTail in
/-- **The recorded tail at a drawn table, as the linked game's run.** -/
theorem probEvent_recordedTail_linked (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : CanonicalGraph.Cells × CanonicalGraph.Padding)
    (event : (Outcome × Multiset Bytes) × QueryCache HashSpec → Prop) :
    Pr[fun result => event (result.1.1, result.2) |
        RecordedTail.recordedTail adversary (walkOfTable prfSeed publicSeed table)] =
      Pr[fun z => event (LinkedGame.outcomeOf z.1, z.2) |
        linkedRun adversary prfSeed publicSeed table] := by
  rw [probEvent_recordedTail_stripped adversary (walkOfTable prfSeed publicSeed table) event,
    run_recordedAfterSeeds_eq_linked adversary prfSeed publicSeed table, probEvent_map]
  rfl

open WalkTable TableTail in
/-- **And the count crosses with it.** -/
theorem expected_recordedTail_linked (adversary : Adversary) (prfSeed publicSeed : Digest)
    (table : CanonicalGraph.Cells × CanonicalGraph.Padding)
    (count : (Outcome × Multiset Bytes) × QueryCache HashSpec → Nat) :
    expected (RecordedTail.recordedTail adversary (walkOfTable prfSeed publicSeed table))
        (fun result => count (result.1.1, result.2)) =
      expected (linkedRun adversary prfSeed publicSeed table)
        (fun z => count (LinkedGame.outcomeOf z.1, z.2)) := by
  haveI : DecidableEq ((Outcome × Multiset Bytes) × QueryCache HashSpec) := Classical.decEq _
  rw [expected_recordedTail_stripped adversary (walkOfTable prfSeed publicSeed table) count,
    run_recordedAfterSeeds_eq_linked adversary prfSeed publicSeed table, expected_map]

end SlhDsaSecurity.RecordedChain
