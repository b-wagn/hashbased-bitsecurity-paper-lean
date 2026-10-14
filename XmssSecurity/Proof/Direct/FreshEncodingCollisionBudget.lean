import XmssSecurity.Proof.Direct.FreshEncodingCollision
import XmssSecurity.Proof.Direct.SourceSignerQueries

/-! Average fresh encoding collisions over the actual reference prefix. The signed
target's acceptance is charged to source encoding queries and signer hashes. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Deciding

open Concrete Direct

abbrev PrefixVerificationResult := ((Forgery × QueryLog SigningSpec) × QueryCache HashSpec) ×
  (GameOutcome × QueryCache HashSpec)

noncomputable def freshEncodingCollisionAfterKeygen (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) : ProbComp PrefixVerificationResult := do
  let prefixResult ← (simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2
  let result ← (simulateQ romImpl (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2
  pure (prefixResult, result)

def FreshEncodingCollisionEvent (publicKey : PublicKey) (result : PrefixVerificationResult) : Prop :=
  result.1.2 (forgeryEncodingInput publicKey result.1.1.1) = none ∧
    WinningOutcomeBadEventOccurs result.2.2 result.2.1 .encoding

theorem freshEncodingCollision_afterKeygen_probability_le (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    Pr[FreshEncodingCollisionEvent keyResult.1.1 | freshEncodingCollisionAfterKeygen adversary keyResult] ≤
      (TargetSum.acceptanceProbability * expectedSimulatedQueryCount romImpl
        (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
        (adversaryPhase adversary keyResult.1.1 keyResult.1.2) keyResult.2) /
          ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  let head := (simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2
  let rate := ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
  unfold freshEncodingCollisionAfterKeygen
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' prefixResult, Pr[= prefixResult | head] *
        (if HasAcceptedEncoding keyResult.1.2.parameter prefixResult.2 then rate else 0) := by
      apply ENNReal.tsum_le_tsum
      intro prefixResult
      by_cases hprefix : prefixResult ∈ support head
      · apply mul_le_mul' le_rfl
        simp only [bind_pure_comp, probEvent_map, Function.comp_def, FreshEncodingCollisionEvent]
        by_cases hfresh : prefixResult.2 (forgeryEncodingInput keyResult.1.1 prefixResult.1.1) = none
        · simp only [hfresh, true_and]
          exact verificationPhase_fresh_encoding_probability_le _ _ _ _
            (keygen_publicKey_parameter_eq keyResult hkey)
            (adversaryPhase_signingLog_consistent adversary keyResult hkey prefixResult hprefix) hfresh
        · simp only [hfresh, false_and, probEvent_False]
          exact zero_le
      · change Pr[= prefixResult | head] * _ ≤ _
        rw [probOutput_eq_zero_of_not_mem_support hprefix, zero_mul, zero_mul]
    _ = Pr[fun result => HasAcceptedEncoding keyResult.1.2.parameter result.2 | head] * rate := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro prefixResult
      split_ifs <;> simp only [mul_zero, zero_mul]
    _ ≤ _ := by
      simpa only [rate, div_eq_mul_inv] using
        mul_le_mul' (probEvent_hasAcceptedEncoding_le_expectedQueries _ _ _
          (precomputedKeygen_no_acceptedEncoding keyResult hkey)) (le_refl rate)

noncomputable def freshEncodingCollisionProbability (adversary : Adversary) : ℝ≥0∞ :=
  ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
    Pr[FreshEncodingCollisionEvent keyResult.1.1 | freshEncodingCollisionAfterKeygen adversary keyResult]

theorem freshEncodingCollisionProbability_le_expectedEncoding (adversary : Adversary) :
    freshEncodingCollisionProbability adversary ≤
      (TargetSum.acceptanceProbability * expectedPrefixEncodingQueries adversary) /
        ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  unfold freshEncodingCollisionProbability
  let encoding := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    expectedSimulatedQueryCount romImpl (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
      (adversaryPhase adversary keyResult.1.1 keyResult.1.2) keyResult.2
  calc
    _ ≤ ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
        (encoding keyResult * (TargetSum.acceptanceProbability / ((2 ^ digestBits : Nat) : ℝ≥0∞))) := by
      apply ENNReal.tsum_le_tsum
      intro keyResult
      by_cases hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)
      · apply mul_le_mul' le_rfl
        apply (freshEncodingCollision_afterKeygen_probability_le adversary keyResult hkey).trans_eq
        dsimp only [encoding]
        simp only [div_eq_mul_inv]
        ring
      · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]
    _ = _ := by
      simp_rw [← mul_assoc]
      rw [ENNReal.tsum_mul_right]
      change expectedPrefixEncodingQueries adversary * _ = _
      simp only [div_eq_mul_inv]
      ring

theorem freshEncodingCollisionProbability_le_source_credit (adversary : Adversary) :
    freshEncodingCollisionProbability adversary ≤
      (TargetSum.acceptanceProbability *
        (expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary)) /
          ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
  (freshEncodingCollisionProbability_le_expectedEncoding adversary).trans
    (ENNReal.div_le_div (mul_le_mul' le_rfl (expectedPrefixEncodingQueries_le adversary)) le_rfl)

/-- info: 'XmssSecurity.Deciding.freshEncodingCollisionProbability_le_source_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshEncodingCollisionProbability_le_source_credit

end XmssSecurity.Deciding
