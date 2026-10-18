import XmssSecurity.Proof.TargetSum.FirstLaneChainExpected
import XmssSecurity.Proof.Generic.FirstLaneHazardEnforcement
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Expected hazard counts are observable trace quantities, and enforcement only removes
hazards. These identities let the expected first-lane bound pass through existing couplings. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

omit [Fintype Index] [DecidableEq Index] in
theorem hazardCount_traceFragment (input : (FirstLaneOracleSimulation.World Index).Domain)
    (output : (FirstLaneOracleSimulation.World Index).Range input) :
    FirstLaneOracleSimulation.hazardCount (FirstLaneOracleSimulation.traceFragment input output) = if FirstLaneOracleSimulation.IsHazardQuery input then 1 else 0 := by
  cases input <;> simp [FirstLaneOracleSimulation.traceFragment, FirstLaneOracleSimulation.hazardCount, FirstLaneOracleSimulation.IsHazardQuery]

omit [Fintype Index] [DecidableEq Index] in
theorem expectedHazardQueries_eq_trace (table : Index → Digest)
    (computation : OracleComp (FirstLaneOracleSimulation.World Index) α) :
    expectedSimulatedQueryCount (eagerUnitImpl table) FirstLaneOracleSimulation.IsHazardQuery computation () =
      ∑' result, Pr[= result | (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) computation).run] *
        (FirstLaneOracleSimulation.hazardCount result.2 : ℝ≥0∞) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [FirstLaneOracleSimulation.hazardCount, simulateQ_pure]
  | query_bind input next ih =>
      rw [expected_eagerUnit_query_bind, FirstLaneOracleSimulation.eagerTrace_query_bind_run, tsum_probOutput_bind_mul]
      simp only [bind_pure_comp, tsum_probOutput_map_mul, FirstLaneOracleSimulation.hazardCount_append,
        hazardCount_traceFragment, Nat.cast_add]
      have htail (output : (FirstLaneOracleSimulation.World Index).Range input) :
          (∑' result, Pr[= result | (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) (next output)).run] *
            (((if FirstLaneOracleSimulation.IsHazardQuery input then 1 else 0 : ℕ) : ℝ≥0∞) +
              (FirstLaneOracleSimulation.hazardCount result.2 : ℝ≥0∞))) =
            (if FirstLaneOracleSimulation.IsHazardQuery input then 1 else 0) +
              expectedSimulatedQueryCount (eagerUnitImpl table) FirstLaneOracleSimulation.IsHazardQuery (next output) () := by
        simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
        simpa only [one_mul, ih] using expected_affine
          ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) (next output)).run)
          (if FirstLaneOracleSimulation.IsHazardQuery input then 1 else 0) 1 (fun result => (FirstLaneOracleSimulation.hazardCount result.2 : ℝ≥0∞))
      simp_rw [htail]
      symm
      simpa only [one_mul] using (expected_affine (FirstLaneOracleSimulation.eagerImpl table input)
        (if FirstLaneOracleSimulation.IsHazardQuery input then 1 else 0) 1
        (fun output => expectedSimulatedQueryCount (eagerUnitImpl table) FirstLaneOracleSimulation.IsHazardQuery (next output) ()))

theorem expectedEagerHazardQueries_eq_trace (computation : OracleComp (FirstLaneOracleSimulation.World Index) α) :
    expectedEagerQueryCount FirstLaneOracleSimulation.IsHazardQuery computation =
      ∑' result, Pr[= result | FirstLaneOracleSimulation.eagerExperiment computation] * (FirstLaneOracleSimulation.hazardCount result.2.2 : ℝ≥0∞) := by
  simp only [FirstLaneOracleSimulation.eagerExperiment, tsum_probOutput_bind_mul, bind_pure_comp,
    tsum_probOutput_map_mul, expectedEagerQueryCount, expectedHazardQueries_eq_trace]

omit [Fintype Index] [DecidableEq Index] in
theorem hazardCount_enforceHazardTrace (fuel : ℕ) (trace : FirstLaneOracleSimulation.ActionTrace Index) :
    FirstLaneOracleSimulation.hazardCount (FirstLaneOracleSimulation.enforceHazardTrace fuel trace) = min fuel (FirstLaneOracleSimulation.hazardCount trace) := by
  induction trace generalizing fuel with
  | nil => simp [FirstLaneOracleSimulation.hazardCount, FirstLaneOracleSimulation.enforceHazardTrace]
  | cons action trace ih =>
      cases action with
      | encoding action =>
          cases action <;> cases fuel <;>
            simp [FirstLaneOracleSimulation.hazardCount, FirstLaneOracleSimulation.enforceHazardTrace, ih, Nat.succ_min_succ]
      | chain action =>
          cases action <;> cases fuel <;>
            simp [FirstLaneOracleSimulation.hazardCount, FirstLaneOracleSimulation.enforceHazardTrace, ih, Nat.succ_min_succ]

theorem expectedEagerHazardQueries_enforce_eq (fuel : ℕ)
    (computation : OracleComp (FirstLaneOracleSimulation.World Index) α) :
    expectedEagerQueryCount FirstLaneOracleSimulation.IsHazardQuery (FirstLaneOracleSimulation.enforceHazardBound fuel computation) =
      ∑' result, Pr[= result | FirstLaneOracleSimulation.eagerExperiment computation] *
        ((min fuel (FirstLaneOracleSimulation.hazardCount result.2.2) : ℕ) : ℝ≥0∞) := by
  rw [expectedEagerHazardQueries_eq_trace, FirstLaneOracleSimulation.eagerExperiment_enforceHazardBound_eq_map,
    tsum_probOutput_map_mul]
  simp only [FirstLaneOracleSimulation.enforceEagerResult, hazardCount_enforceHazardTrace]

/-- info: 'XmssSecurity.TargetSum.FirstLaneOracleSimulation.expectedEagerHazardQueries_eq_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedEagerHazardQueries_eq_trace

end XmssSecurity.TargetSum.FirstLaneOracleSimulation
