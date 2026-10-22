import SlhDsaSecurity.Proof.WalkTable
import SlhDsaSecurity.Proof.RandomiserRecord
import SlhDsaSecurity.Proof.ClassExpectation

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

open Security WarmedGame WalkTable ClassExpectation

/-! ## Averaging a count-plus-constant bound over one draw

The count averages into the count and the constant survives, because a law has mass at most one.
It is `SharedJoin.prob_le_expected_of_perWalk`'s calculation with the walk replaced by an
arbitrary draw, and it is stated that way so the two seeds can be averaged one at a time. -/

open scoped Classical in
/-- **A count-plus-constant bound that holds after every draw holds over the bind.** -/
theorem prob_le_expected_of_bind {α β : Type} (first : ProbComp α) (rest : α → ProbComp β)
    (event : β → Prop) (count : β → Nat) (extra : ℝ≥0∞)
    (hrest : ∀ value, Pr[event | rest value] ≤
      (expected (rest value) count + extra) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Pr[event | first >>= rest] ≤
      (expected (first >>= rest) count + extra) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [probEvent_bind_eq_tsum, expected_bind]
  calc ∑' value, Pr[= value | first] * Pr[event | rest value]
      ≤ ∑' value, Pr[= value | first] *
          ((expected (rest value) count + extra) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
        ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (hrest value)
    _ = ∑' value, (Pr[= value | first] * expected (rest value) count +
          Pr[= value | first] * extra) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine tsum_congr fun value => ?_
        simp only [div_eq_mul_inv]
        ring
    _ = ((∑' value, Pr[= value | first] * expected (rest value) count) +
          (∑' value, Pr[= value | first]) * extra) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ ((∑' value, Pr[= value | first] * expected (rest value) count) + extra) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine ENNReal.div_le_div_right (add_le_add le_rfl ?_) _
        exact le_of_le_of_eq (mul_le_mul' tsum_probOutput_le_one le_rfl) (one_mul extra)

/-- **Equal laws have equal expectations.** -/
theorem expected_congr {β : Type} {left right : ProbComp β} (hlaw : 𝒟[left] = 𝒟[right])
    (count : β → Nat) : expected left count = expected right count := by
  rw [expected, expected]
  exact tsum_congr fun value => by rw [probOutput_def, probOutput_def, hlaw]

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

/-- **A bound at each pair of drawn seeds is a bound at the recorded paired run**, with the
count averaging into the count and the constant surviving. The two seeds the table does not
carry are the only things fixed; the cell table and the secret seed it holds stay in the
measure, which is what the input half cannot do without. -/
theorem prob_le_expected_of_seeds (adversary : Adversary)
    (event : ((((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
      (((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec)) → Prop)
    (count : ((((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) ×
      (((Outcome × Multiset Bytes) × Nat) × QueryCache HashSpec)) → Nat) (extra : ℝ≥0∞)
    (hseeds : ∀ prfSeed publicSeed,
      Pr[event | recordedTableRun adversary prfSeed publicSeed] ≤
        (expected (recordedTableRun adversary prfSeed publicSeed) count + extra) /
          ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Pr[event | RandomiserRecord.recordedPairedRun adversary] ≤
      (expected (RandomiserRecord.recordedPairedRun adversary) count + extra) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_recordedPairedRun adversary),
    expected_congr (evalDist_recordedPairedRun adversary) count]
  refine prob_le_expected_of_bind _ _ event count extra fun prfSeed => ?_
  exact prob_le_expected_of_bind _ _ event count extra fun publicSeed => hseeds prfSeed publicSeed

end SlhDsaSecurity.RecordedWalkTable
