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

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

noncomputable def expectedCoupledHazards (fuel : ℕ)
    (body : CappedChain.ProgrammedGlobalChainKeygenView → (CappedChain.GlobalChainEdgeIndex → Digest) →
      OracleComp CappedChain.GlobalFirstLaneWorld α) : ℝ≥0∞ :=
  ∑' result, Pr[= result | Deciding.coupledFirstLaneProgram body] *
    ((min fuel (FirstLaneOracleSimulation.hazardCount result.2.2) : ℕ) : ℝ≥0∞)

theorem eager_enforcedHit_probability_le_expected (fuel : ℕ)
    (computation : OracleComp CappedChain.GlobalFirstLaneWorld α) :
    Pr[fun result => FirstLaneOracleSimulation.CombinedHit result.1 (FirstLaneOracleSimulation.enforceHazardTrace fuel result.2.2) |
      FirstLaneOracleSimulation.eagerExperiment computation] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        expectedEagerQueryCount FirstLaneOracleSimulation.IsHazardQuery (FirstLaneOracleSimulation.enforceHazardBound fuel computation) := by
  calc
    _ = Pr[FirstLaneOracleSimulation.ExperimentHit | FirstLaneOracleSimulation.enforceEagerResult fuel <$> FirstLaneOracleSimulation.eagerExperiment computation] := by
      rw [probEvent_map]
      rfl
    _ = Pr[FirstLaneOracleSimulation.ExperimentHit | FirstLaneOracleSimulation.eagerExperiment (FirstLaneOracleSimulation.enforceHazardBound fuel computation)] := by
      rw [FirstLaneOracleSimulation.eagerExperiment_enforceHazardBound_eq_map]
    _ ≤ _ := combinedHit_eager_probability_le_expected fuel
      (FirstLaneOracleSimulation.enforceHazardBound fuel computation) (FirstLaneOracleSimulation.enforceHazardBound_isHazardQueryBoundP fuel computation)

theorem expectedCoupledHazards_eq_public (fuel : ℕ)
    (body : CappedChain.ProgrammedGlobalChainKeygenView → (CappedChain.GlobalChainEdgeIndex → Digest) →
      OracleComp CappedChain.GlobalFirstLaneWorld α) :
    expectedCoupledHazards fuel body =
      expectedEagerQueryCount FirstLaneOracleSimulation.IsHazardQuery (FirstLaneOracleSimulation.enforceHazardBound fuel (Deciding.publicFirstLaneProgram body)) := by
  rw [expectedEagerHazardQueries_enforce_eq]
  calc
    _ = ∑' result, Pr[= result |
          Deciding.coupledFirstLaneProjection <$> Deciding.coupledFirstLaneProgram body] *
        ((min fuel (FirstLaneOracleSimulation.hazardCount result.2.2) : ℕ) : ℝ≥0∞) := by
      rw [tsum_probOutput_map_mul]
      rfl
    _ = _ := by
      apply tsum_congr
      intro result
      rw [probOutput_congr rfl (Deciding.evalDist_coupledFirstLaneProgram_projection body)]

theorem expectedCoupledHazards_le (fuel : ℕ)
    (body : CappedChain.ProgrammedGlobalChainKeygenView → (CappedChain.GlobalChainEdgeIndex → Digest) →
      OracleComp CappedChain.GlobalFirstLaneWorld α) : expectedCoupledHazards fuel body ≤ fuel := by
  unfold expectedCoupledHazards
  calc
    _ ≤ ∑' result, Pr[= result | Deciding.coupledFirstLaneProgram body] * (fuel : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro result
      gcongr
      exact min_le_left _ _
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one le_rfl).trans_eq (one_mul _)

theorem coupled_enforcedHit_probability_le_expected (fuel : ℕ)
    (body : CappedChain.ProgrammedGlobalChainKeygenView → (CappedChain.GlobalChainEdgeIndex → Digest) →
      OracleComp CappedChain.GlobalFirstLaneWorld α) :
    Pr[fun result => FirstLaneOracleSimulation.CombinedHit result.1.1.2 (FirstLaneOracleSimulation.enforceHazardTrace fuel result.2.2) |
      Deciding.coupledFirstLaneProgram body] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ * expectedCoupledHazards fuel body := by
  rw [expectedCoupledHazards_eq_public]
  calc
    _ = Pr[fun result => FirstLaneOracleSimulation.CombinedHit result.1 (FirstLaneOracleSimulation.enforceHazardTrace fuel result.2.2) |
        Deciding.coupledFirstLaneProjection <$> Deciding.coupledFirstLaneProgram body] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun result => FirstLaneOracleSimulation.CombinedHit result.1 (FirstLaneOracleSimulation.enforceHazardTrace fuel result.2.2) |
        FirstLaneOracleSimulation.eagerExperiment (Deciding.publicFirstLaneProgram body)] :=
      CappedChain.probEvent_eq_of_evalDist_eq _ (Deciding.evalDist_coupledFirstLaneProgram_projection body)
    _ ≤ _ := eager_enforcedHit_probability_le_expected fuel (Deciding.publicFirstLaneProgram body)

end XmssSecurity.TargetSum.Deciding
