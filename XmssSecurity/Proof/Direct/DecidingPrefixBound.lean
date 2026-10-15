import XmssSecurity.Proof.Direct.DecidingPrefixProgram

/-! The sharper first-lane bound for events at the adversary prefix. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.Deciding

open CappedChain FirstLaneOracleSimulation

theorem eager_enforcedHit_probability_le (fuel : ℕ)
    (computation : OracleComp GlobalFirstLaneWorld α) :
    Pr[fun result => CombinedHit result.1 (enforceHazardTrace fuel result.2.2) |
      eagerExperiment computation] ≤ (fuel : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  calc
    _ = Pr[ExperimentHit | enforceEagerResult fuel <$> eagerExperiment computation] := by
      rw [probEvent_map]
      rfl
    _ = Pr[ExperimentHit | eagerExperiment (enforceHazardBound fuel computation)] := by
      rw [eagerExperiment_enforceHazardBound_eq_map]
    _ = Pr[fun hit : Bool => hit = true | structuralExperiment
        (some EncodingMonitor.State.empty) AdaptiveRevealMonitor.State.empty fuel
          (enforceHazardBound fuel computation)] :=
      combinedHit_probability_eq_structuralExperiment fuel (enforceHazardBound fuel computation)
        (enforceHazardBound_isHazardQueryBoundP fuel computation)
    _ ≤ _ := structuralExperiment_empty_true_probability_le fuel (enforceHazardBound fuel computation)

theorem coupled_enforcedHit_probability_le (fuel : ℕ)
    (body : ProgrammedGlobalChainKeygenView → (GlobalChainEdgeIndex → Digest) →
      OracleComp GlobalFirstLaneWorld α) :
    Pr[fun result => CombinedHit result.1.1.2 (enforceHazardTrace fuel result.2.2) |
      coupledFirstLaneProgram body] ≤ (fuel : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  calc
    _ = Pr[fun result => CombinedHit result.1 (enforceHazardTrace fuel result.2.2) |
        coupledFirstLaneProjection <$> coupledFirstLaneProgram body] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun result => CombinedHit result.1 (enforceHazardTrace fuel result.2.2) |
        eagerExperiment (publicFirstLaneProgram body)] :=
      probEvent_eq_of_evalDist_eq _ (evalDist_coupledFirstLaneProgram_projection body)
    _ ≤ _ := eager_enforcedHit_probability_le fuel (publicFirstLaneProgram body)

theorem sourcePrefixProgram_coupling (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    RelTriple (sourcePrefixProgram adversary)
      (coupledFirstLaneProgram (publicPrefixProbeExecution adversary))
      (fun left right => PrefixFirstLaneEvent left.1 left.2 →
        CombinedHit right.1.1.2 (enforceHazardTrace (D + 1) right.2.2)) := by
  unfold sourcePrefixProgram coupledFirstLaneProgram
  apply relTriple_bind (relTriple_with_support
    relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeys
  obtain ⟨hkey, hleftSupport, hrightSupport⟩ := hkeys
  apply relTriple_bind (prefixFirstLaneEvent_probability_le_enforcedHit_afterKeygen
    adversary D hD left right hkey hleftSupport
      (coupledGlobalChainKeygenWithBaseHighFull_support_keyView right hrightSupport))
  intro leftResult rightResult hresult
  exact relTriple_pure_pure hresult

/-- Adversary hazards plus a single deciding probe suffice for the prefix event. -/
theorem prefixFirstLane_probability_le (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    Pr[fun result => PrefixFirstLaneEvent result.1 result.2 | sourcePrefixProgram adversary] ≤
      ((D + 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  calc
    _ ≤ Pr[fun result => CombinedHit result.1.1.2 (enforceHazardTrace (D + 1) result.2.2) |
        coupledFirstLaneProgram (publicPrefixProbeExecution adversary)] := by
      apply probEvent_le_of_relTriple (sourcePrefixProgram_coupling adversary D hD)
      intro left right hrel hevent
      exact hrel hevent
    _ ≤ _ := coupled_enforcedHit_probability_le (D + 1) (publicPrefixProbeExecution adversary)

end XmssSecurity.Deciding
