import Xmss.Proof.Checksum.HiddenSibling.FreshSigned
import Xmss.Proof.Checksum.HiddenSibling.ZeroHashEncoding
import Xmss.Proof.Generic.Direct.ReusedEncodingProbability

/-! A hash-free adversary's signed executions have the full 124-bit verification coefficient,
weighted by the probability of making a signing request. -/

open OracleComp OracleSpec ENNReal
open Xmss.Generic

set_option backward.isDefEq.respectTransparency false

namespace Xmss.Checksum.HiddenSibling

open Generic.Deciding Generic.CappedExecution

def CachedSourcePrefix (before : SourcePrefixResult) : Prop :=
  before.2.2.1.1.1 (CacheView.encodingInput before.1.secretKey.parameter before.2.1.epoch
    (before.2.1.message, before.2.1.signature.randomness)) ≠ none ∧
    before.2.2.2.toSigningLog ≠ [] ∧ SigningTranscript.Valid before.2.2.2.toSigningLog

theorem source_prefix_branches_le_signed (adversary : Generic.Adversary) :
    Pr[CachedSourcePrefix | sourcePrefixProgram adversary] +
      Pr[FreshSourcePrefix | sourcePrefixProgram adversary] ≤
        Pr[fun before : SourcePrefixResult => before.2.2.2.toSigningLog ≠ [] |
          sourcePrefixProgram adversary] := by
  classical
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro before
  by_cases hcached : CachedSourcePrefix before
  · have hnotFresh : ¬ FreshSourcePrefix before := fun h => hcached.1 h.1
    simp only [if_pos hcached, if_neg hnotFresh, if_pos hcached.2.1, add_zero, le_refl]
  · by_cases hfresh : FreshSourcePrefix before
    · simp only [if_neg hcached, if_pos hfresh, if_pos hfresh.2.1, zero_add, le_refl]
    · simp only [if_neg hcached, if_neg hfresh, zero_add]
      exact zero_le

open Classical in
theorem source_signed_verification_le_branches (adversary : Generic.Adversary)
    (hzero : Direct.IsDirectQueryBound adversary 0) (before : SourcePrefixResult)
    (hbefore : before ∈ support (sourcePrefixProgram adversary)) :
    Pr[fun result : GameOutcome × QueryCache HashSpec =>
        result.1.won = true ∧ result.1.signingLog ≠ [] | sourcePrefixVerification before] ≤
      (48 : ℝ≥0∞) * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        (if CachedSourcePrefix before then 1 else 0) +
      (if FreshSourcePrefix before then
        Pr[fun result : GameOutcome × QueryCache HashSpec => result.1.won = true |
          sourcePrefixVerification before] else 0) := by
  by_cases hgood : before.2.2.2.toSigningLog ≠ [] ∧
      SigningTranscript.Valid before.2.2.2.toSigningLog
  · by_cases hfresh : before.2.2.1.1.1 (CacheView.encodingInput before.1.secretKey.parameter
        before.2.1.epoch (before.2.1.message, before.2.1.signature.randomness)) = none
    · have hbranch : FreshSourcePrefix before := ⟨hfresh, hgood⟩
      rw [if_pos hbranch]
      exact (probEvent_mono fun _ _ h => h.1).trans le_add_self
    · have hbranch : CachedSourcePrefix before := ⟨hfresh, hgood⟩
      rw [if_pos hbranch, mul_one]
      apply le_add_right
      obtain ⟨hkey, hprefix⟩ := sourcePrefixProgram_support adversary before hbefore
      let keyResult := Keygen.materializeCachedKeyResult before.1.keyResult
      have hkeygen : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅) :=
        Keygen.oldKeygen_support_materializedPrecomputedKeygen before.1.keyResult
          (trajectoryProgrammedGlobalChainKeygen_support_keyResult before.1 hkey)
      have hphase := sourcePrefixExecution_phase_support adversary before.1 before.2 hprefix
      have hparameter : keyResult.1.2.parameter = before.1.secretKey.parameter :=
        Keygen.materializePrecomputation_parameter before.1.cache before.1.secretKey
      have hcached : before.2.2.1.1.1 (CacheView.encodingInput keyResult.1.2.parameter
          before.2.1.epoch (before.2.1.message, before.2.1.signature.randomness)) ≠ none := by
        rw [hparameter]
        exact hfresh
      have hreuses := zeroHash_cached_encoding_reuses adversary hzero keyResult hkeygen
        ((before.2.1, before.2.2.2.toSigningLog), before.2.2.1.1.1) hphase hgood.2 hcached
      have hcollision := zeroHash_prefix_no_structural_collision adversary hzero keyResult.1.1
        keyResult.1.2 keyResult.2 ((before.2.1, before.2.2.2.toSigningLog), before.2.2.1.1.1) hphase
      refine (probEvent_mono fun _ _ h => h.1).trans ?_
      change Pr[fun result : GameOutcome × QueryCache HashSpec => result.1.won = true |
        (simulateQ romImpl (verificationPhase keyResult.1.1 keyResult.1.2
          (before.2.1, before.2.2.2.toSigningLog))).run before.2.2.1.1.1] ≤ _
      simpa only [div_eq_mul_inv] using reused_verification_probability_le adversary keyResult
        hkeygen ((before.2.1, before.2.2.2.toSigningLog), before.2.2.1.1.1) hphase
        hreuses.2 hreuses.1 hcached hcollision
  · have hzeroProb : Pr[fun result : GameOutcome × QueryCache HashSpec =>
        result.1.won = true ∧ result.1.signingLog ≠ [] | sourcePrefixVerification before] = 0 := by
      apply probEvent_eq_zero
      intro result hresult hwin
      have hfields := verificationPhase_support before.1.publicKey
        (Keygen.materializePrecomputation before.1.cache before.1.secretKey)
        (before.2.1, before.2.2.2.toSigningLog) before.2.2.1.1.1 result hresult
      apply hgood
      have hlog : result.1.signingLog = before.2.2.2.toSigningLog := hfields.2.2.2.1
      rw [← hlog]
      exact ⟨hwin.2, (result.1.won_eq_true_iff.mp hwin.1).1⟩
    rw [hzeroProb]
    exact zero_le

theorem hashFree_signed_probability_le (adversary : Generic.Adversary)
    (hzero : Direct.IsDirectQueryBound adversary 0) :
    Pr[fun result : GameOutcome × QueryCache HashSpec =>
        result.1.won = true ∧ result.1.signingLog ≠ [] |
      detailedGameWithCache precomputedScheme adversary] ≤
      (48 : ℝ≥0∞) * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        Pr[fun result : GameOutcome × QueryCache HashSpec => result.1.signingLog ≠ [] |
          detailedGameWithCache precomputedScheme adversary] := by
  classical
  let cost : ℝ≥0∞ := 48 * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹
  rw [probEvent_game_eq_source_prefix,
    probEvent_game_log_eq_source adversary (fun log => log ≠ [])]
  calc
    _ ≤ ∑' before, Pr[= before | sourcePrefixProgram adversary] *
        (cost * (if CachedSourcePrefix before then 1 else 0) +
          (if FreshSourcePrefix before then
            Pr[fun result : GameOutcome × QueryCache HashSpec => result.1.won = true |
              sourcePrefixVerification before] else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro before
      by_cases hbefore : before ∈ support (sourcePrefixProgram adversary)
      · exact mul_le_mul' le_rfl (source_signed_verification_le_branches adversary hzero before hbefore)
      · rw [probOutput_eq_zero_of_not_mem_support hbefore, zero_mul, zero_mul]
    _ = cost * Pr[CachedSourcePrefix | sourcePrefixProgram adversary] +
        ∑' before, Pr[= before | sourcePrefixProgram adversary] *
          (if FreshSourcePrefix before then
            Pr[fun result : GameOutcome × QueryCache HashSpec => result.1.won = true |
              sourcePrefixVerification before] else 0) := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add]
      congr 1
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro before
      split_ifs <;> simp [mul_comm]
    _ ≤ cost * Pr[CachedSourcePrefix | sourcePrefixProgram adversary] +
        cost * Pr[FreshSourcePrefix | sourcePrefixProgram adversary] := by
      apply add_le_add le_rfl
      refine (fresh_signed_verification_probability_le adversary hzero).trans ?_
      apply mul_le_mul' _ le_rfl
      apply mul_le_mul' _ le_rfl
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_div]
    _ = cost * (Pr[CachedSourcePrefix | sourcePrefixProgram adversary] +
        Pr[FreshSourcePrefix | sourcePrefixProgram adversary]) := (mul_add _ _ _).symm
    _ ≤ _ := mul_le_mul' le_rfl (source_prefix_branches_le_signed adversary)

end Xmss.Checksum.HiddenSibling
