import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsSigningActivity
import XmssSecurity.Proof.TargetSum.Direct.FreshFirstLaneSplit

/-! A fresh verifier encoding can collide only with an existing signed target.
Charge this loss to signing requests instead of the signer's internal hash calls. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA.Requests
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding

theorem sourcePrefixFinish_encoding_requires_request (adversary : XmssSecurity.TargetSum.Adversary)
    (key : ProgrammedGlobalChainKeygenView)
    (prefixResult : Forgery × SourceExactTracedState)
    (hprefix : prefixResult ∈ support (sourcePrefixExecution adversary key))
    (result : (Forgery × Bool) × SourceExactTracedState)
    (hresult : result ∈ support (sourcePrefixFinish key prefixResult))
    (hevent : SourceWinningEncodingEvent (key, result)) :
    0 < prefixResult.2.2.toSigningLog.length := by
  have hlogs := cappedBothTracedMappedAdversaryImpl_logs_eq key.publicKey
    (materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey)
    ((((key.cache, []), []), [])) prefixResult rfl hprefix
  rw [sourcePrefixFinish, support_map] at hresult
  obtain ⟨verified, _, rfl⟩ := hresult
  obtain ⟨request, signature, htarget, _⟩ := winning_encoding_event_signed_target _ _ hevent
  simp only [cappedBothEncodingProjection, sourceGlobalExactProgramResult,
    sourceGlobalExactExecutionResult, hlogs] at htarget
  by_contra hzero
  have hempty : prefixResult.2.2.toSigningLog = [] := List.length_eq_zero_iff.mp (by omega)
  simp [hempty, returnedAt] at htarget

theorem sourcePrefixFinish_fresh_encoding_probability_le_request (adversary : XmssSecurity.TargetSum.Adversary)
    (key : ProgrammedGlobalChainKeygenView) (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Forgery × SourceExactTracedState)
    (hprefix : prefixResult ∈ support (sourcePrefixExecution adversary key))
    (hfresh : SourcePrefixForgedEncodingFresh (key, prefixResult)) :
    Pr[fun result => SourceWinningEncodingEvent (key, result) | sourcePrefixFinish key prefixResult] ≤
      if 0 < prefixResult.2.2.toSigningLog.length
        then ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  by_cases hactive : 0 < prefixResult.2.2.toSigningLog.length
  · rw [if_pos hactive]
    apply (sourcePrefixFinish_fresh_encoding_probability_le adversary key hkey prefixResult hprefix hfresh).trans
    split_ifs <;> simp
  · rw [if_neg hactive]
    apply le_of_eq
    apply probEvent_eq_zero
    intro result hresult hevent
    exact hactive (sourcePrefixFinish_encoding_requires_request adversary key prefixResult hprefix result hresult hevent)

theorem freshSourceEncodingProbability_le_requests (adversary : XmssSecurity.TargetSum.Adversary) :
    freshSourceEncodingProbability adversary ≤
      expectedSigningRequests adversary / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  let rate := ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹
  unfold freshSourceEncodingProbability
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' pair, Pr[= pair | sourcePrefixProgram adversary] *
        (if 0 < pair.2.2.2.toSigningLog.length then rate else 0) := by
      apply ENNReal.tsum_le_tsum
      intro pair
      by_cases hpair : pair ∈ support (sourcePrefixProgram adversary)
      · apply mul_le_mul' le_rfl
        simp only [bind_pure_comp, probEvent_map, Function.comp_def]
        by_cases hfresh : SourcePrefixForgedEncodingFresh pair
        · simp only [hfresh, true_and]
          unfold sourcePrefixProgram at hpair
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hpair
          obtain ⟨key, hkey, prefixResult, hprefix, rfl⟩ := hpair
          exact sourcePrefixFinish_fresh_encoding_probability_le_request adversary key hkey prefixResult hprefix hfresh
        · simp only [hfresh, false_and, probEvent_False]
          exact zero_le
      · rw [probOutput_eq_zero_of_not_mem_support hpair, zero_mul, zero_mul]
    _ = Pr[fun result => 0 < result.2.2.2.toSigningLog.length |
        sourcePrefixProgram adversary] * rate := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro pair
      split_ifs <;> simp only [mul_zero, zero_mul]
    _ ≤ _ := by
      simpa only [rate, div_eq_mul_inv] using
        mul_le_mul' (sourcePrefixProgram_signingActivity_probability_le adversary) (le_refl rate)

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.freshSourceEncodingProbability_le_requests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshSourceEncodingProbability_le_requests

end XmssSecurity.TargetSum.EUFCMA.Requests
