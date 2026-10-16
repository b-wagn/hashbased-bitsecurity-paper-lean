import XmssSecurity.Proof.Direct.MixedEncodingProbe

/-! Cancel the conditional probe charge in the joint cached-or-fresh experiment.
The source prefix is charged once, regardless of which encoding supplies the probe. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Deciding

open CappedChain FirstLaneOracleSimulation

def SourceCountedMixedPrefixEvent (fallback : Option Encoding)
    (result : ProgrammedGlobalChainKeygenView × (Forgery × CountedSourceState)) : Prop :=
  MixedEncodingPrefixEvent result.1 (result.2.1, result.2.2.toSource) fallback

def SourceCountedMixedPrefixAccepted (fallback : Option Encoding)
    (result : ProgrammedGlobalChainKeygenView × (Forgery × CountedSourceState)) : Prop :=
  SourceCountedPrefixAccepted result ∨ fallback.isSome

def CoupledLimitedMixedProbeEligible (fallback : Option Encoding) (result : CoupledLimitedPrefixResult) : Prop :=
  LimitedMixedEncodingProbeEligible result.1.1.1 fallback result.2

def CoupledLimitedMixedProbedHit (fallback : Option Encoding) (result : CoupledLimitedPrefixResult) : Prop :=
  CombinedHit result.1.1.2 (appendLimitedMixedEncodingProbe result.1.1.2 result.1.1.1 fallback result.2).2

noncomputable def publicLimitedMixedEncodingProbeExecution (limit : Nat) (adversary : Adversary)
    (fallback : Option Encoding) (key : ProgrammedGlobalChainKeygenView) (edgeHigh : GlobalChainEdgeIndex → Digest) :
    OracleComp GlobalFirstLaneWorld LimitedPrefixResult :=
  limitedMixedEncodingProbeExecution limit key edgeHigh (adversary.main key.publicKey) fallback

theorem coupledLimitedMixedEncodingProbe_eq_map (limit : Nat) (adversary : Adversary) (fallback : Option Encoding) :
    coupledFirstLaneProgram (publicLimitedMixedEncodingProbeExecution limit adversary fallback) =
      (fun result : CoupledLimitedPrefixResult =>
        (result.1, appendLimitedMixedEncodingProbe result.1.1.2 result.1.1.1 fallback result.2)) <$>
          coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary) := by
  unfold coupledFirstLaneProgram publicLimitedMixedEncodingProbeExecution publicLimitedPrefixExecution
  simp only [map_bind, map_pure, limitedMixedEncodingProbeExecution_eager, bind_map_left]

theorem coupledLimitedMixedEncodingProbe_trace_bound (limit : Nat) (adversary : Adversary)
    (fallback : Option Encoding) (result : CoupledLimitedPrefixResult)
    (hresult : result ∈ support
      (coupledFirstLaneProgram (publicLimitedMixedEncodingProbeExecution limit adversary fallback))) :
    hazardCount result.2.2 ≤ limit + 1 := by
  rw [coupledLimitedMixedEncodingProbe_eq_map, support_map] at hresult
  obtain ⟨prefixResult, hprefix, rfl⟩ := hresult
  have hcount := coupledLimitedPrefix_trace_bound limit adversary prefixResult hprefix
  rw [hazardCount_appendLimitedMixedEncodingProbe]
  split_ifs <;> omega

theorem expectedCoupledLimitedMixedProbe_hazards_le (limit : Nat) (adversary : Adversary)
    (fallback : Option Encoding) :
    expectedCoupledHazards (limit + 1) (publicLimitedMixedEncodingProbeExecution limit adversary fallback) ≤
      (limit : ℝ≥0∞) + Pr[CoupledLimitedMixedProbeEligible fallback |
        coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary)] := by
  unfold expectedCoupledHazards
  rw [coupledLimitedMixedEncodingProbe_eq_map, tsum_probOutput_map_mul, probEvent_eq_tsum_ite]
  calc
    _ ≤ ∑' result, Pr[= result | coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary)] *
        ((limit : ℝ≥0∞) + if CoupledLimitedMixedProbeEligible fallback result then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support (coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary))
      · apply mul_le_mul' le_rfl
        have hcount := coupledLimitedPrefix_trace_bound limit adversary result hresult
        rw [hazardCount_appendLimitedMixedEncodingProbe]
        change ((min (limit + 1) (hazardCount result.2.2 +
          if CoupledLimitedMixedProbeEligible fallback result then 1 else 0) : Nat) : ℝ≥0∞) ≤ _
        split_ifs <;> exact_mod_cast (by omega : min (limit + 1) (hazardCount result.2.2 + _) ≤ limit + _)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ = _ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]
      congr 1
      apply tsum_congr
      intro result
      split_ifs <;> simp

theorem coupledLimitedMixedProbedHit_probability_le (adversary : Adversary) (limit : Nat)
    (fallback : Option Encoding) :
    Pr[CoupledLimitedMixedProbedHit fallback |
      coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary)] ≤
      (limit : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ * Pr[CoupledLimitedMixedProbeEligible fallback |
          coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary)] := by
  have hevent : Pr[CoupledLimitedMixedProbedHit fallback |
      coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary)] =
      Pr[fun result => CombinedHit result.1.1.2 (enforceHazardTrace (limit + 1) result.2.2) |
        coupledFirstLaneProgram (publicLimitedMixedEncodingProbeExecution limit adversary fallback)] := by
    calc
      _ = Pr[fun result => CombinedHit result.1.1.2 result.2.2 |
          coupledFirstLaneProgram (publicLimitedMixedEncodingProbeExecution limit adversary fallback)] := by
        rw [coupledLimitedMixedEncodingProbe_eq_map, probEvent_map]
        rfl
      _ = _ := by
        apply probEvent_congr' (fun result hresult => ?_) rfl
        rw [enforceHazardTrace_eq_self_of_count_le _ _
          (coupledLimitedMixedEncodingProbe_trace_bound limit adversary fallback result hresult)]
  rw [hevent]
  apply (coupled_enforcedHit_probability_le_expected (limit + 1) _).trans
  simpa only [mul_add, div_eq_mul_inv, mul_comm] using
    mul_le_mul' (le_refl (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹))
      (expectedCoupledLimitedMixedProbe_hazards_le limit adversary fallback)

theorem limitedMixedEncoding_cancellation_coupling (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) (fallback : Option Encoding) :
    RelTriple (sourceCountedPrefixProgram adversary)
      (coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary))
      (fun source target =>
        (SourceCountedMixedPrefixEvent fallback source →
          SourceCountedMixedPrefixAccepted fallback source ∧ CoupledLimitedMixedProbedHit fallback target) ∧
        (CoupledLimitedMixedProbeEligible fallback target →
          SourceCountedMixedPrefixAccepted fallback source ∨ CoupledLimitedMixedProbedHit fallback target)) := by
  unfold sourceCountedPrefixProgram coupledFirstLaneProgram
  apply relTriple_bind (relTriple_with_support relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable)
  intro left right hkeys
  obtain ⟨hrel, hleft, hright⟩ := hkeys
  apply relTriple_bind (limitedMixedEncoding_cancellation_coupling_afterKeygen adversary limit left right hrel hleft
    (coupledGlobalChainKeygenWithBaseHighFull_support_keyView right hright) (hbudget left hleft) fallback)
  intro source target hresult
  exact relTriple_pure_pure hresult

theorem sourceCountedMixedPrefixEvent_probability_le (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) (fallback : Option Encoding) :
    Pr[SourceCountedMixedPrefixEvent fallback | sourceCountedPrefixProgram adversary] ≤
      (limit : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ *
          Pr[SourceCountedMixedPrefixAccepted fallback | sourceCountedPrefixProgram adversary] :=
  accepted_event_probability_le_of_relTriple (SourceCountedMixedPrefixEvent fallback)
    (SourceCountedMixedPrefixAccepted fallback) (CoupledLimitedMixedProbeEligible fallback)
    (CoupledLimitedMixedProbedHit fallback) _ _ (by norm_num [digestBits])
    (limitedMixedEncoding_cancellation_coupling adversary limit hbudget fallback)
    (coupledLimitedMixedProbedHit_probability_le adversary limit fallback)

theorem mixedEncodingPrefixEvent_probability_le (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) (fallback : Option Encoding) :
    Pr[fun result => MixedEncodingPrefixEvent result.1 result.2 fallback | sourcePrefixProgram adversary] ≤
      (limit : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ * Pr[fun result =>
          HasAcceptedEncoding result.1.secretKey.parameter result.2.2.1.1.1 ∨ fallback.isSome |
          sourcePrefixProgram adversary] := by
  rw [← sourceCountedPrefixProgram_source_projection]
  simp only [probEvent_map]
  exact sourceCountedMixedPrefixEvent_probability_le adversary limit hbudget fallback

theorem mixedEncodingPrefixEvent_probability_le_source_credit (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) (fallback : Option Encoding) :
    Pr[fun result => MixedEncodingPrefixEvent result.1 result.2 fallback | sourcePrefixProgram adversary] ≤
      (limit : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ *
          (Checksum.acceptanceProbability *
            (Direct.expectedDirectEncodingQueries adversary + Direct.expectedSourceSignerHashes adversary) +
              if fallback.isSome then 1 else 0) := by
  apply (mixedEncodingPrefixEvent_probability_le adversary limit hbudget fallback).trans
  apply add_le_add le_rfl
  apply mul_le_mul' le_rfl
  apply (probEvent_or_le _ _ _).trans
  apply add_le_add (sourcePrefix_accepted_probability_le adversary)
  cases fallback <;> simp

/-- info: 'XmssSecurity.Deciding.mixedEncodingPrefixEvent_probability_le_source_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mixedEncodingPrefixEvent_probability_le_source_credit

end XmssSecurity.Deciding
