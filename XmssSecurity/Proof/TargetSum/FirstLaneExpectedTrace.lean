import XmssSecurity.Proof.TargetSum.FirstLaneChainExpected
import XmssSecurity.Proof.Generic.FirstLaneHazardEnforcement
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Expected hazard counts are observable trace quantities, and enforcement only removes
hazards. These identities let the expected first-lane bound pass through existing couplings. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.FirstLaneOracleSimulation

variable {Index : Type} [Fintype Index] [DecidableEq Index]

omit [Fintype Index] [DecidableEq Index] in
theorem hazardCount_traceFragment (input : (Generic.FirstLaneOracleSimulation.World Index).Domain)
    (output : (Generic.FirstLaneOracleSimulation.World Index).Range input) :
    Generic.FirstLaneOracleSimulation.hazardCount (Generic.FirstLaneOracleSimulation.traceFragment input output) = if Generic.FirstLaneOracleSimulation.IsHazardQuery input then 1 else 0 := by
  cases input <;> simp [Generic.FirstLaneOracleSimulation.traceFragment, Generic.FirstLaneOracleSimulation.hazardCount, Generic.FirstLaneOracleSimulation.IsHazardQuery]

omit [Fintype Index] [DecidableEq Index] in
theorem expectedHazardQueries_eq_trace (table : Index → Digest)
    (computation : OracleComp (Generic.FirstLaneOracleSimulation.World Index) α) :
    expectedSimulatedQueryCount (eagerUnitImpl table) Generic.FirstLaneOracleSimulation.IsHazardQuery computation () =
      ∑' result, Pr[= result | (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table) computation).run] *
        (Generic.FirstLaneOracleSimulation.hazardCount result.2 : ℝ≥0∞) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [Generic.FirstLaneOracleSimulation.hazardCount, simulateQ_pure]
  | query_bind input next ih =>
      rw [expected_eagerUnit_query_bind, Generic.FirstLaneOracleSimulation.eagerTrace_query_bind_run, tsum_probOutput_bind_mul]
      simp only [bind_pure_comp, tsum_probOutput_map_mul, Generic.FirstLaneOracleSimulation.hazardCount_append,
        hazardCount_traceFragment, Nat.cast_add]
      have htail (output : (Generic.FirstLaneOracleSimulation.World Index).Range input) :
          (∑' result, Pr[= result | (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table) (next output)).run] *
            (((if Generic.FirstLaneOracleSimulation.IsHazardQuery input then 1 else 0 : ℕ) : ℝ≥0∞) +
              (Generic.FirstLaneOracleSimulation.hazardCount result.2 : ℝ≥0∞))) =
            (if Generic.FirstLaneOracleSimulation.IsHazardQuery input then 1 else 0) +
              expectedSimulatedQueryCount (eagerUnitImpl table) Generic.FirstLaneOracleSimulation.IsHazardQuery (next output) () := by
        simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
        simpa only [one_mul, ih] using expected_affine
          ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table) (next output)).run)
          (if Generic.FirstLaneOracleSimulation.IsHazardQuery input then 1 else 0) 1 (fun result => (Generic.FirstLaneOracleSimulation.hazardCount result.2 : ℝ≥0∞))
      simp_rw [htail]
      symm
      simpa only [one_mul] using (expected_affine (Generic.FirstLaneOracleSimulation.eagerImpl table input)
        (if Generic.FirstLaneOracleSimulation.IsHazardQuery input then 1 else 0) 1
        (fun output => expectedSimulatedQueryCount (eagerUnitImpl table) Generic.FirstLaneOracleSimulation.IsHazardQuery (next output) ()))

theorem expectedEagerHazardQueries_eq_trace (computation : OracleComp (Generic.FirstLaneOracleSimulation.World Index) α) :
    expectedEagerQueryCount Generic.FirstLaneOracleSimulation.IsHazardQuery computation =
      ∑' result, Pr[= result | Generic.FirstLaneOracleSimulation.eagerExperiment computation] * (Generic.FirstLaneOracleSimulation.hazardCount result.2.2 : ℝ≥0∞) := by
  simp only [Generic.FirstLaneOracleSimulation.eagerExperiment, tsum_probOutput_bind_mul, bind_pure_comp,
    tsum_probOutput_map_mul, expectedEagerQueryCount, expectedHazardQueries_eq_trace]

omit [Fintype Index] [DecidableEq Index] in
theorem hazardCount_enforceHazardTrace (fuel : ℕ) (trace : Generic.FirstLaneOracleSimulation.ActionTrace Index) :
    Generic.FirstLaneOracleSimulation.hazardCount (Generic.FirstLaneOracleSimulation.enforceHazardTrace fuel trace) = min fuel (Generic.FirstLaneOracleSimulation.hazardCount trace) := by
  induction trace generalizing fuel with
  | nil => simp [Generic.FirstLaneOracleSimulation.hazardCount, Generic.FirstLaneOracleSimulation.enforceHazardTrace]
  | cons action trace ih =>
      cases action with
      | encoding action =>
          cases action <;> cases fuel <;>
            simp [Generic.FirstLaneOracleSimulation.hazardCount, Generic.FirstLaneOracleSimulation.enforceHazardTrace, ih, Nat.succ_min_succ]
      | chain action =>
          cases action <;> cases fuel <;>
            simp [Generic.FirstLaneOracleSimulation.hazardCount, Generic.FirstLaneOracleSimulation.enforceHazardTrace, ih, Nat.succ_min_succ]

theorem expectedEagerHazardQueries_enforce_eq (fuel : ℕ)
    (computation : OracleComp (Generic.FirstLaneOracleSimulation.World Index) α) :
    expectedEagerQueryCount Generic.FirstLaneOracleSimulation.IsHazardQuery (Generic.FirstLaneOracleSimulation.enforceHazardBound fuel computation) =
      ∑' result, Pr[= result | Generic.FirstLaneOracleSimulation.eagerExperiment computation] *
        ((min fuel (Generic.FirstLaneOracleSimulation.hazardCount result.2.2) : ℕ) : ℝ≥0∞) := by
  rw [expectedEagerHazardQueries_eq_trace, Generic.FirstLaneOracleSimulation.eagerExperiment_enforceHazardBound_eq_map,
    tsum_probOutput_map_mul]
  simp only [Generic.FirstLaneOracleSimulation.enforceEagerResult, hazardCount_enforceHazardTrace]

/-- info: 'XmssSecurity.TargetSum.FirstLaneOracleSimulation.expectedEagerHazardQueries_eq_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedEagerHazardQueries_eq_trace

end XmssSecurity.TargetSum.FirstLaneOracleSimulation
