import XmssSecurity.Proof.TargetSum.FirstLaneChainExpected
import XmssSecurity.Proof.TargetSum.FirstLaneHazardEnforcement

/-! Expected hazard counts are observable trace quantities, and enforcement only removes
hazards. These identities let the expected first-lane bound pass through existing couplings. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

omit [Fintype Index] [DecidableEq Index] in
theorem hazardCount_traceFragment (input : (World Index).Domain)
    (output : (World Index).Range input) :
    hazardCount (traceFragment input output) = if IsHazardQuery input then 1 else 0 := by
  cases input <;> simp [traceFragment, hazardCount, IsHazardQuery]

omit [Fintype Index] [DecidableEq Index] in
theorem expectedHazardQueries_eq_trace (table : Index → Digest)
    (computation : OracleComp (World Index) α) :
    expectedSimulatedQueryCount (eagerUnitImpl table) IsHazardQuery computation () =
      ∑' result, Pr[= result | (simulateQ (eagerTraceImpl table) computation).run] *
        (hazardCount result.2 : ℝ≥0∞) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [hazardCount, simulateQ_pure]
  | query_bind input next ih =>
      rw [expected_eagerUnit_query_bind, eagerTrace_query_bind_run, tsum_probOutput_bind_mul]
      simp only [bind_pure_comp, tsum_probOutput_map_mul, hazardCount_append,
        hazardCount_traceFragment, Nat.cast_add]
      have htail (output : (World Index).Range input) :
          (∑' result, Pr[= result | (simulateQ (eagerTraceImpl table) (next output)).run] *
            (((if IsHazardQuery input then 1 else 0 : ℕ) : ℝ≥0∞) +
              (hazardCount result.2 : ℝ≥0∞))) =
            (if IsHazardQuery input then 1 else 0) +
              expectedSimulatedQueryCount (eagerUnitImpl table) IsHazardQuery (next output) () := by
        simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
        simpa only [one_mul, ih] using expected_affine
          ((simulateQ (eagerTraceImpl table) (next output)).run)
          (if IsHazardQuery input then 1 else 0) 1 (fun result => (hazardCount result.2 : ℝ≥0∞))
      simp_rw [htail]
      symm
      simpa only [one_mul] using (expected_affine (eagerImpl table input)
        (if IsHazardQuery input then 1 else 0) 1
        (fun output => expectedSimulatedQueryCount (eagerUnitImpl table) IsHazardQuery (next output) ()))

theorem expectedEagerHazardQueries_eq_trace (computation : OracleComp (World Index) α) :
    expectedEagerQueryCount IsHazardQuery computation =
      ∑' result, Pr[= result | eagerExperiment computation] * (hazardCount result.2.2 : ℝ≥0∞) := by
  simp only [eagerExperiment, tsum_probOutput_bind_mul, bind_pure_comp,
    tsum_probOutput_map_mul, expectedEagerQueryCount, expectedHazardQueries_eq_trace]

omit [Fintype Index] [DecidableEq Index] in
theorem hazardCount_enforceHazardTrace (fuel : ℕ) (trace : ActionTrace Index) :
    hazardCount (enforceHazardTrace fuel trace) = min fuel (hazardCount trace) := by
  induction trace generalizing fuel with
  | nil => simp [hazardCount, enforceHazardTrace]
  | cons action trace ih =>
      cases action with
      | encoding action =>
          cases action <;> cases fuel <;>
            simp [hazardCount, enforceHazardTrace, ih, Nat.succ_min_succ]
      | chain action =>
          cases action <;> cases fuel <;>
            simp [hazardCount, enforceHazardTrace, ih, Nat.succ_min_succ]

theorem expectedEagerHazardQueries_enforce_eq (fuel : ℕ)
    (computation : OracleComp (World Index) α) :
    expectedEagerQueryCount IsHazardQuery (enforceHazardBound fuel computation) =
      ∑' result, Pr[= result | eagerExperiment computation] *
        ((min fuel (hazardCount result.2.2) : ℕ) : ℝ≥0∞) := by
  rw [expectedEagerHazardQueries_eq_trace, eagerExperiment_enforceHazardBound_eq_map,
    tsum_probOutput_map_mul]
  simp only [enforceEagerResult, hazardCount_enforceHazardTrace]

theorem expectedEagerHazardQueries_enforce_le (fuel : ℕ)
    (computation : OracleComp (World Index) α) :
    expectedEagerQueryCount IsHazardQuery (enforceHazardBound fuel computation) ≤
      expectedEagerQueryCount IsHazardQuery computation := by
  rw [expectedEagerHazardQueries_enforce_eq, expectedEagerHazardQueries_eq_trace]
  apply ENNReal.tsum_le_tsum
  intro result
  gcongr
  exact min_le_right _ _

/-- info: 'XmssSecurity.TargetSum.FirstLaneOracleSimulation.expectedEagerHazardQueries_eq_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedEagerHazardQueries_eq_trace

end XmssSecurity.TargetSum.FirstLaneOracleSimulation
