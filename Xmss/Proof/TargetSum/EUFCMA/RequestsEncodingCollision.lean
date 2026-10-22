import Xmss.Proof.TargetSum.EUFCMA.RequestsSigningActivity
import Xmss.Proof.TargetSum.Direct.FreshFirstLaneSplit
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! A fresh verifier encoding can collide only with an existing signed target.
Charge this loss to signing requests instead of the signer's internal hash calls. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.EUFCMA.Requests
open Xmss.EUFCMA

open Hashing Wots Merkle Verify Keygen Signing CappedExecution Deciding

theorem sourcePrefixFinish_encoding_requires_request (adversary : Adversary)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (prefixResult : Forgery × CappedExecution.SourceExactTracedState)
    (hprefix : prefixResult ∈ support (Deciding.sourcePrefixExecution adversary key))
    (result : (Forgery × Bool) × CappedExecution.SourceExactTracedState)
    (hresult : result ∈ support (Deciding.sourcePrefixFinish key prefixResult))
    (hevent : SourceWinningEncodingEvent (key, result)) :
    0 < prefixResult.2.2.toSigningLog.length := by
  have hlogs := CappedExecution.cappedBothTracedMappedAdversaryImpl_logs_eq key.publicKey
    (Keygen.materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey)
    ((((key.cache, []), []), [])) prefixResult rfl hprefix
  rw [Deciding.sourcePrefixFinish, support_map] at hresult
  obtain ⟨verified, _, rfl⟩ := hresult
  obtain ⟨request, signature, htarget, _⟩ := winning_encoding_event_signed_target _ _ hevent
  simp only [CappedExecution.cappedBothEncodingProjection, CappedExecution.sourceGlobalExactProgramResult,
    CappedExecution.sourceGlobalExactExecutionResult, hlogs] at htarget
  by_contra hzero
  have hempty : prefixResult.2.2.toSigningLog = [] := List.length_eq_zero_iff.mp (by omega)
  simp [hempty, Deciding.returnedAt] at htarget

theorem sourcePrefixFinish_fresh_encoding_probability_le_request (adversary : Adversary)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (hkey : key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (prefixResult : Forgery × CappedExecution.SourceExactTracedState)
    (hprefix : prefixResult ∈ support (Deciding.sourcePrefixExecution adversary key))
    (hfresh : SourcePrefixForgedEncodingFresh (key, prefixResult)) :
    Pr[fun result => SourceWinningEncodingEvent (key, result) | Deciding.sourcePrefixFinish key prefixResult] ≤
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

theorem freshSourceEncodingProbability_le_requests (adversary : Adversary) :
    freshSourceEncodingProbability adversary ≤
      expectedSigningRequests adversary / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  let rate := ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹
  unfold freshSourceEncodingProbability
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' pair, Pr[= pair | Deciding.sourcePrefixProgram adversary] *
        (if 0 < pair.2.2.2.toSigningLog.length then rate else 0) := by
      apply ENNReal.tsum_le_tsum
      intro pair
      by_cases hpair : pair ∈ support (Deciding.sourcePrefixProgram adversary)
      · apply mul_le_mul' le_rfl
        simp only [bind_pure_comp, probEvent_map, Function.comp_def]
        by_cases hfresh : SourcePrefixForgedEncodingFresh pair
        · simp only [hfresh, true_and]
          unfold Deciding.sourcePrefixProgram at hpair
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hpair
          obtain ⟨key, hkey, prefixResult, hprefix, rfl⟩ := hpair
          exact sourcePrefixFinish_fresh_encoding_probability_le_request adversary key hkey prefixResult hprefix hfresh
        · simp only [hfresh, false_and, probEvent_False]
          exact zero_le
      · rw [probOutput_eq_zero_of_not_mem_support hpair, zero_mul, zero_mul]
    _ = Pr[fun result => 0 < result.2.2.2.toSigningLog.length |
        Deciding.sourcePrefixProgram adversary] * rate := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro pair
      split_ifs <;> simp only [mul_zero, zero_mul]
    _ ≤ _ := by
      simpa only [rate, div_eq_mul_inv] using
        mul_le_mul' (sourcePrefixProgram_signingActivity_probability_le adversary) (le_refl rate)

/-- info: 'Xmss.TargetSum.EUFCMA.Requests.freshSourceEncodingProbability_le_requests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshSourceEncodingProbability_le_requests

end Xmss.TargetSum.EUFCMA.Requests
