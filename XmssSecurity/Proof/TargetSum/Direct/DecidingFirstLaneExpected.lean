import XmssSecurity.Proof.TargetSum.FirstLaneExpectedTrace
import XmssSecurity.Proof.Generic.Direct.DecidingFirstLaneBridge
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Carry the expected first-lane estimate through the existing key-generation and prefix
couplings, up to the original winning event in the reference game. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.Deciding

open Generic.CappedChain FirstLaneOracleSimulation

noncomputable def expectedCoupledHazards (fuel : ℕ)
    (body : Generic.CappedChain.ProgrammedGlobalChainKeygenView → (Generic.CappedChain.GlobalChainEdgeIndex → Digest) →
      OracleComp Generic.CappedChain.GlobalFirstLaneWorld α) : ℝ≥0∞ :=
  ∑' result, Pr[= result | Generic.Deciding.coupledFirstLaneProgram body] *
    ((min fuel (Generic.FirstLaneOracleSimulation.hazardCount result.2.2) : ℕ) : ℝ≥0∞)

theorem eager_enforcedHit_probability_le_expected (fuel : ℕ)
    (computation : OracleComp Generic.CappedChain.GlobalFirstLaneWorld α) :
    Pr[fun result => Generic.FirstLaneOracleSimulation.CombinedHit result.1 (Generic.FirstLaneOracleSimulation.enforceHazardTrace fuel result.2.2) |
      Generic.FirstLaneOracleSimulation.eagerExperiment computation] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        expectedEagerQueryCount Generic.FirstLaneOracleSimulation.IsHazardQuery (Generic.FirstLaneOracleSimulation.enforceHazardBound fuel computation) := by
  calc
    _ = Pr[Generic.FirstLaneOracleSimulation.ExperimentHit | Generic.FirstLaneOracleSimulation.enforceEagerResult fuel <$> Generic.FirstLaneOracleSimulation.eagerExperiment computation] := by
      rw [probEvent_map]
      rfl
    _ = Pr[Generic.FirstLaneOracleSimulation.ExperimentHit | Generic.FirstLaneOracleSimulation.eagerExperiment (Generic.FirstLaneOracleSimulation.enforceHazardBound fuel computation)] := by
      rw [Generic.FirstLaneOracleSimulation.eagerExperiment_enforceHazardBound_eq_map]
    _ ≤ _ := combinedHit_eager_probability_le_expected fuel
      (Generic.FirstLaneOracleSimulation.enforceHazardBound fuel computation) (Generic.FirstLaneOracleSimulation.enforceHazardBound_isHazardQueryBoundP fuel computation)

theorem expectedCoupledHazards_eq_public (fuel : ℕ)
    (body : Generic.CappedChain.ProgrammedGlobalChainKeygenView → (Generic.CappedChain.GlobalChainEdgeIndex → Digest) →
      OracleComp Generic.CappedChain.GlobalFirstLaneWorld α) :
    expectedCoupledHazards fuel body =
      expectedEagerQueryCount Generic.FirstLaneOracleSimulation.IsHazardQuery (Generic.FirstLaneOracleSimulation.enforceHazardBound fuel (Generic.Deciding.publicFirstLaneProgram body)) := by
  rw [expectedEagerHazardQueries_enforce_eq]
  calc
    _ = ∑' result, Pr[= result |
          Generic.Deciding.coupledFirstLaneProjection <$> Generic.Deciding.coupledFirstLaneProgram body] *
        ((min fuel (Generic.FirstLaneOracleSimulation.hazardCount result.2.2) : ℕ) : ℝ≥0∞) := by
      rw [tsum_probOutput_map_mul]
      rfl
    _ = _ := by
      apply tsum_congr
      intro result
      rw [probOutput_congr rfl (Generic.Deciding.evalDist_coupledFirstLaneProgram_projection body)]

theorem expectedCoupledHazards_le (fuel : ℕ)
    (body : Generic.CappedChain.ProgrammedGlobalChainKeygenView → (Generic.CappedChain.GlobalChainEdgeIndex → Digest) →
      OracleComp Generic.CappedChain.GlobalFirstLaneWorld α) : expectedCoupledHazards fuel body ≤ fuel := by
  unfold expectedCoupledHazards
  calc
    _ ≤ ∑' result, Pr[= result | Generic.Deciding.coupledFirstLaneProgram body] * (fuel : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro result
      gcongr
      exact min_le_left _ _
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one le_rfl).trans_eq (one_mul _)

theorem coupled_enforcedHit_probability_le_expected (fuel : ℕ)
    (body : Generic.CappedChain.ProgrammedGlobalChainKeygenView → (Generic.CappedChain.GlobalChainEdgeIndex → Digest) →
      OracleComp Generic.CappedChain.GlobalFirstLaneWorld α) :
    Pr[fun result => Generic.FirstLaneOracleSimulation.CombinedHit result.1.1.2 (Generic.FirstLaneOracleSimulation.enforceHazardTrace fuel result.2.2) |
      Generic.Deciding.coupledFirstLaneProgram body] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ * expectedCoupledHazards fuel body := by
  rw [expectedCoupledHazards_eq_public]
  calc
    _ = Pr[fun result => Generic.FirstLaneOracleSimulation.CombinedHit result.1 (Generic.FirstLaneOracleSimulation.enforceHazardTrace fuel result.2.2) |
        Generic.Deciding.coupledFirstLaneProjection <$> Generic.Deciding.coupledFirstLaneProgram body] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun result => Generic.FirstLaneOracleSimulation.CombinedHit result.1 (Generic.FirstLaneOracleSimulation.enforceHazardTrace fuel result.2.2) |
        Generic.FirstLaneOracleSimulation.eagerExperiment (Generic.Deciding.publicFirstLaneProgram body)] :=
      Generic.CappedChain.probEvent_eq_of_evalDist_eq _ (Generic.Deciding.evalDist_coupledFirstLaneProgram_projection body)
    _ ≤ _ := eager_enforcedHit_probability_le_expected fuel (Generic.Deciding.publicFirstLaneProgram body)

end XmssSecurity.TargetSum.Deciding
