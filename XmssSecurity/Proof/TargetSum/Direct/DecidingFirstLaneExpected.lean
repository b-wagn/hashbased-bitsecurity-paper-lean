import XmssSecurity.Proof.TargetSum.FirstLaneExpectedTrace
import XmssSecurity.Proof.TargetSum.Direct.DecidingFirstLaneBridge

/-! Carry the expected first-lane estimate through the existing key-generation and prefix
couplings, up to the original winning event in the reference game. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

noncomputable def expectedCoupledHazards (fuel : ℕ)
    (body : ProgrammedGlobalChainKeygenView → (GlobalChainEdgeIndex → Digest) →
      OracleComp GlobalFirstLaneWorld α) : ℝ≥0∞ :=
  ∑' result, Pr[= result | coupledFirstLaneProgram body] *
    ((min fuel (hazardCount result.2.2) : ℕ) : ℝ≥0∞)

theorem eager_enforcedHit_probability_le_expected (fuel : ℕ)
    (computation : OracleComp GlobalFirstLaneWorld α) :
    Pr[fun result => CombinedHit result.1 (enforceHazardTrace fuel result.2.2) |
      eagerExperiment computation] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        expectedEagerQueryCount IsHazardQuery (enforceHazardBound fuel computation) := by
  calc
    _ = Pr[ExperimentHit | enforceEagerResult fuel <$> eagerExperiment computation] := by
      rw [probEvent_map]
      rfl
    _ = Pr[ExperimentHit | eagerExperiment (enforceHazardBound fuel computation)] := by
      rw [eagerExperiment_enforceHazardBound_eq_map]
    _ ≤ _ := combinedHit_eager_probability_le_expected fuel
      (enforceHazardBound fuel computation) (enforceHazardBound_isHazardQueryBoundP fuel computation)

theorem expectedCoupledHazards_eq_public (fuel : ℕ)
    (body : ProgrammedGlobalChainKeygenView → (GlobalChainEdgeIndex → Digest) →
      OracleComp GlobalFirstLaneWorld α) :
    expectedCoupledHazards fuel body =
      expectedEagerQueryCount IsHazardQuery (enforceHazardBound fuel (publicFirstLaneProgram body)) := by
  rw [expectedEagerHazardQueries_enforce_eq]
  calc
    _ = ∑' result, Pr[= result |
          coupledFirstLaneProjection <$> coupledFirstLaneProgram body] *
        ((min fuel (hazardCount result.2.2) : ℕ) : ℝ≥0∞) := by
      rw [tsum_probOutput_map_mul]
      rfl
    _ = _ := by
      apply tsum_congr
      intro result
      rw [probOutput_congr rfl (evalDist_coupledFirstLaneProgram_projection body)]

theorem expectedCoupledHazards_le (fuel : ℕ)
    (body : ProgrammedGlobalChainKeygenView → (GlobalChainEdgeIndex → Digest) →
      OracleComp GlobalFirstLaneWorld α) : expectedCoupledHazards fuel body ≤ fuel := by
  unfold expectedCoupledHazards
  calc
    _ ≤ ∑' result, Pr[= result | coupledFirstLaneProgram body] * (fuel : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro result
      gcongr
      exact min_le_left _ _
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one le_rfl).trans_eq (one_mul _)

theorem coupled_enforcedHit_probability_le_expected (fuel : ℕ)
    (body : ProgrammedGlobalChainKeygenView → (GlobalChainEdgeIndex → Digest) →
      OracleComp GlobalFirstLaneWorld α) :
    Pr[fun result => CombinedHit result.1.1.2 (enforceHazardTrace fuel result.2.2) |
      coupledFirstLaneProgram body] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ * expectedCoupledHazards fuel body := by
  rw [expectedCoupledHazards_eq_public]
  calc
    _ = Pr[fun result => CombinedHit result.1 (enforceHazardTrace fuel result.2.2) |
        coupledFirstLaneProjection <$> coupledFirstLaneProgram body] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun result => CombinedHit result.1 (enforceHazardTrace fuel result.2.2) |
        eagerExperiment (publicFirstLaneProgram body)] :=
      probEvent_eq_of_evalDist_eq _ (evalDist_coupledFirstLaneProgram_projection body)
    _ ≤ _ := eager_enforcedHit_probability_le_expected fuel (publicFirstLaneProgram body)

end XmssSecurity.TargetSum.Deciding
