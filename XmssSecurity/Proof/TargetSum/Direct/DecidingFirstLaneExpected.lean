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

theorem prefixFirstLane_probability_le_expected (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    Pr[fun result => PrefixFirstLaneEvent result.1 result.2 | sourcePrefixProgram adversary] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        expectedCoupledHazards (D + 1) (publicPrefixProbeExecution adversary) := by
  calc
    _ ≤ Pr[fun result => CombinedHit result.1.1.2 (enforceHazardTrace (D + 1) result.2.2) |
        coupledFirstLaneProgram (publicPrefixProbeExecution adversary)] := by
      apply probEvent_le_of_relTriple (sourcePrefixProgram_coupling adversary D hD)
      intro left right hrel hevent
      exact hrel hevent
    _ ≤ _ := coupled_enforcedHit_probability_le_expected (D + 1) (publicPrefixProbeExecution adversary)

theorem decidingFirstLane_probability_le_prefix_of_cached (adversary : Adversary)
    (hcached : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      ∀ prefixResult ∈ support (sourcePrefixExecution adversary key),
        prefixResult.2.1.1.1 (Concrete.CacheView.encodingInput key.secretKey.parameter
          prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none) :
    Pr[WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      Pr[fun result => PrefixFirstLaneEvent result.1 result.2 | sourcePrefixProgram adversary] := by
  rw [decidingFirstLane_probability_eq_source, sourceProgram_eq_prefix_finish]
  apply probEvent_bind_le_probEvent
  intro prefixPair hprefixPair hnone
  unfold sourcePrefixProgram at hprefixPair
  rw [mem_support_bind_iff] at hprefixPair
  obtain ⟨key, hkey, hprefixPair⟩ := hprefixPair
  rw [mem_support_bind_iff] at hprefixPair
  obtain ⟨prefixResult, hprefix, hpure⟩ := hprefixPair
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst prefixPair
  apply probEvent_eq_zero
  intro finalResult hfinal hevent
  rw [mem_support_bind_iff] at hfinal
  obtain ⟨execution, hfinish, hpure⟩ := hfinal
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst finalResult
  exact hnone (sourceFirstLaneEvent_implies_prefixEvent adversary key hkey prefixResult hprefix
    (hcached key hkey prefixResult hprefix) execution hfinish hevent)

theorem decidingFirstLane_probability_le_expected_of_cached (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D)
    (hcached : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      ∀ prefixResult ∈ support (sourcePrefixExecution adversary key),
        prefixResult.2.1.1.1 (Concrete.CacheView.encodingInput key.secretKey.parameter
          prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none) :
    Pr[WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        expectedCoupledHazards (D + 1) (publicPrefixProbeExecution adversary) :=
  (decidingFirstLane_probability_le_prefix_of_cached adversary hcached).trans
    (prefixFirstLane_probability_le_expected adversary D hD)

theorem decidingFirstLane_withForgedEncodingQuery_probability_le_expected
    (adversary : Adversary) (D : ℕ) (hD : Direct.IsDirectQueryBound adversary D) :
    Pr[WinningDecidingFirstLaneBadEventOccurs |
      cappedDetailedGameWithEncodingTrace (Direct.withForgedEncodingQuery adversary)] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ * expectedCoupledHazards (D + 2)
        (publicPrefixProbeExecution (Direct.withForgedEncodingQuery adversary)) :=
  decidingFirstLane_probability_le_expected_of_cached (Direct.withForgedEncodingQuery adversary)
    (D + 1) (Direct.withForgedEncodingQuery_isDirectQueryBound adversary D hD)
    (sourcePrefixExecution_withForgedEncodingQuery_cached adversary)

/-- info: 'XmssSecurity.TargetSum.Deciding.decidingFirstLane_withForgedEncodingQuery_probability_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decidingFirstLane_withForgedEncodingQuery_probability_le_expected

end XmssSecurity.TargetSum.Deciding
