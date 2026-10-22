import SlhDsaSecurity.Proof.ClassExpectation
import SlhDsaSecurity.Proof.WarmedGame

/-!
# Pairing a walk with a tail, and averaging over the walk

The obligations are read at a run that draws a walk and then plays a tail from it, and three
statements about such a run are used everywhere: its events decompose over the walk, its counts
decompose over the walk, and a charge proved walk by walk is a charge on the whole.

**None of the three looks at the tail.** They were first written at the recorded tail, because
that is where they were needed, and then wanted again at a tail carrying the recorder's two
recordings — the same proofs, at a different type. So they are stated here once, with the tail a
parameter and its result type free, and the readings at particular tails are instantiations.

The constant beside the count survives the averaging because the walk's law has mass at most
one, which is the only inequality in the file.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.PairedAverage

open Security WarmedGame ClassExpectation

/-- The walk, and then a tail played from it. -/
noncomputable def pairedWith {β : Type}
    (tail : (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) →
      ProbComp β) :
    ProbComp (((((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec)) ×
      β) := do
  let walk ← graphWalk
  let result ← tail walk
  pure (walk, result)

/-- **The paired run is the walk and then the tail**, read at an event. -/
theorem probEvent_pairedWith {β : Type}
    (tail : (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) →
      ProbComp β)
    (event : ((((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) × β) →
      Prop) :
    Pr[event | pairedWith tail] =
      ∑' walk, Pr[= walk | graphWalk] *
        Pr[fun result => event (walk, result) | tail walk] := by
  rw [pairedWith, probEvent_bind_eq_tsum]
  refine tsum_congr fun walk => congrArg _ ?_
  rw [bind_pure_comp, probEvent_map]
  rfl

open scoped Classical in
/-- **The same, read at a count.** -/
theorem expected_pairedWith {β : Type}
    (tail : (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) →
      ProbComp β)
    (count : ((((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) × β) →
      Nat) :
    expected (pairedWith tail) count =
      ∑' walk, Pr[= walk | graphWalk] *
        expected (tail walk) (fun result => count (walk, result)) := by
  classical
  haveI : DecidableEq (((((Digest × Digest × Digest) × CanonicalGraph.Cells) ×
    QueryCache HashSpec)) × β) := Classical.decEq _
  rw [pairedWith, expected_bind]
  refine tsum_congr fun walk => congrArg _ ?_
  rw [bind_pure_comp, expected_map]

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **A charge proved walk by walk is a charge on the paired run.** The constant beside the
count survives the averaging because the walk's law has mass at most one. -/
theorem prob_le_expected_of_perWalk {β : Type}
    (tail : (((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) →
      ProbComp β)
    (event : ((((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) × β) →
      Prop)
    (count : ((((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec) × β) →
      Nat) (extra : ℝ≥0∞)
    (hwalkwise : ∀ walk ∈ support graphWalk,
      Pr[fun result => event (walk, result) | tail walk] ≤
        (expected (tail walk) (fun result => count (walk, result)) + extra) /
          ((2 ^ 128 : Nat) : ℝ≥0∞)) :
    Pr[event | pairedWith tail] ≤
      (expected (pairedWith tail) count + extra) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [probEvent_pairedWith, expected_pairedWith]
  calc ∑' walk, Pr[= walk | graphWalk] * Pr[fun result => event (walk, result) | tail walk]
      ≤ ∑' walk, Pr[= walk | graphWalk] *
          ((expected (tail walk) (fun result => count (walk, result)) + extra) /
            ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        refine ENNReal.tsum_le_tsum fun walk => ?_
        by_cases hmem : walk ∈ support graphWalk
        · exact mul_le_mul' le_rfl (hwalkwise walk hmem)
        · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]
    _ = ∑' walk, (Pr[= walk | graphWalk] *
            expected (tail walk) (fun result => count (walk, result)) +
          Pr[= walk | graphWalk] * extra) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine tsum_congr fun walk => ?_
        simp only [div_eq_mul_inv]
        ring
    _ = ((∑' walk, Pr[= walk | graphWalk] *
            expected (tail walk) (fun result => count (walk, result))) +
          (∑' walk, Pr[= walk | graphWalk]) * extra) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ ((∑' walk, Pr[= walk | graphWalk] *
            expected (tail walk) (fun result => count (walk, result))) + extra) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine ENNReal.div_le_div_right (add_le_add le_rfl ?_) _
        exact le_of_le_of_eq (mul_le_mul' tsum_probOutput_le_one le_rfl) (one_mul extra)

end SlhDsaSecurity.PairedAverage
