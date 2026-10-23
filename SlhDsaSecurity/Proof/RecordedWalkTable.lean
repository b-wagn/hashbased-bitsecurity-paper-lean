import SlhDsaSecurity.Proof.WalkTable
import SlhDsaSecurity.Proof.RandomiserRecord
import SlhDsaSecurity.Proof.ClassGrowth

/-!
# The recorded paired run, with its walk drawn as a table

`WalkTable` presents the walk as a uniform cells-and-padding pair and carries that to
`Target.pairedRun`. The shared side's join is stated one presentation along, at
`RandomiserRecord.recordedPairedRun`, which keeps the record the counts are read off; this file
is the same crossing there.

What it is for is the input half's bullet, which cannot be proved per walk — conditioning on the
walk fixes the cell table, and an adversary may be chosen knowing it — so the averaging the join
does over the walk has to be replaced by an averaging over **the two seeds the table does not
carry**, with the table still in the measure. `prob_le_expected_of_bind` is that averaging at
one draw, stated for a bound of the join's own shape, a count plus a constant over `2 ^ 128`;
`prob_le_expected_of_seeds` applies it twice and crosses to the drawn table.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.RecordedWalkTable

open Security WarmedGame WalkTable

/-! ## Averaging a count-plus-constant bound over one draw

The count averages into the count and the constant survives, because a law has mass at most one.
It is `SharedJoin.prob_le_expected_of_perWalk`'s calculation with the walk replaced by an
arbitrary draw, and it is stated that way so the two seeds can be averaged one at a time. -/

/-! ## The recorded paired run at a drawn table -/

/-- The recorded game at a drawn table, with the walk it determines kept. -/
noncomputable def recordedTableRun (adversary : Adversary) (prfSeed publicSeed : Digest) :
    ProbComp ((((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
      (((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec)) := do
  let table ← ($ᵗ (CanonicalGraph.Cells × CanonicalGraph.Padding) :
    ProbComp (CanonicalGraph.Cells × CanonicalGraph.Padding))
  let result ← RecordedTail.recordedTail adversary (walkOfTable prfSeed publicSeed table)
  pure (walkOfTable prfSeed publicSeed table, result)

/-- **The recorded paired run draws its table.** -/
theorem evalDist_recordedPairedRun (adversary : Adversary) :
    𝒟[RandomiserRecord.recordedPairedRun adversary] =
      𝒟[(do
        let prfSeed ← ($ᵗ Digest : ProbComp Digest)
        let publicSeed ← ($ᵗ Digest : ProbComp Digest)
        recordedTableRun adversary prfSeed publicSeed)] := by
  rw [RandomiserRecord.recordedPairedRun, evalDist_bind, evalDist_graphWalk, ← evalDist_bind,
    tableWalk]
  simp only [recordedTableRun, bind_assoc, pure_bind]

end SlhDsaSecurity.RecordedWalkTable
