import XmssSecurity.Proof.Generic.EncodingRejectionProbability
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! A sharper signing-success estimate for the one-query standard-forgery
analysis. This includes collisions among the signer's randomizers. -/

open OracleComp OracleSpec ENNReal

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

theorem capped_rejection_bound_lt_one_over_131072 :
    (1 - TargetSum.acceptanceProbability) ^ signingAttemptLimit +
      (signingAttemptLimit : ℝ≥0∞) * signingAttemptLimit *
        ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹ < 1 / 131072 := by
  have hpow : (1 - TargetSum.acceptanceProbability) ^ signingAttemptLimit ≤
      1 / (1 + (signingAttemptLimit : ℝ≥0∞) * (1 / ((2 ^ 15 : ℕ) : ℝ≥0∞))) :=
    (pow_le_pow_left' (tsub_le_tsub_left TargetSum.acceptanceProbability_lower.le 1) signingAttemptLimit).trans
      (Code.rejection_power_le _ (by norm_num) _)
  apply lt_of_le_of_lt (add_le_add hpow le_rfl)
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [signingAttemptLimit, randomnessBits, ENNReal.toReal_div, ENNReal.toReal_mul]

theorem signing_failure_lt_one_over_131072
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (message : Message) :
    Pr[fun result : Option Generic.Signature × QueryCache HashSpec => result.1 = none |
      (simulateQ romImpl (Concrete.precomputedCappedSign keyResult.1.2 leafIndex message)).run
        keyResult.2] < 1 / 131072 := by
  rw [Concrete.precomputedCappedSign]
  have hbound := Concrete.precomputedSignBoundedAttempts_failure_le
    Code.signingAttemptLimit keyResult.1.2
    leafIndex message keyResult.2 0 (by
      rw [Concrete.keygen_cachedEncodingInputCount_eq_zero keyResult hkey]
      simp)
  simp only [Nat.cast_zero, zero_add] at hbound
  rw [code_acceptanceProbability] at hbound
  exact hbound.trans_lt capped_rejection_bound_lt_one_over_131072

theorem signing_success_gt_131071_over_131072
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (message : Message) :
    131071 / 131072 < Pr[fun result : Option Generic.Signature × QueryCache HashSpec => result.1 ≠ none |
      (simulateQ romImpl (Concrete.precomputedCappedSign keyResult.1.2 leafIndex message)).run
        keyResult.2] := by
  let computation := (simulateQ romImpl
    (Concrete.precomputedCappedSign keyResult.1.2 leafIndex message)).run keyResult.2
  have hfailure := signing_failure_lt_one_over_131072 keyResult hkey leafIndex message
  have hsum : Pr[fun result => result.1 = none | computation] +
      Pr[fun result => result.1 ≠ none | computation] = 1 := by
    simpa only [probFailure_of_liftM_PMF, tsub_zero] using
      probEvent_compl computation (fun result => result.1 = none)
  have hsumReal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top, ENNReal.toReal_one] at hsumReal
  have hfailureReal := (ENNReal.toReal_lt_toReal probEvent_ne_top (by finiteness)).mpr hfailure
  apply (ENNReal.toReal_lt_toReal (by finiteness) probEvent_ne_top).mp
  norm_num [ENNReal.toReal_div] at hfailureReal ⊢
  change (Pr[fun result => result.1 = none | computation]).toReal < 1 / 131072 at hfailureReal
  change 131071 / 131072 < (Pr[fun result => result.1 ≠ none | computation]).toReal
  linarith

/-- info: 'XmssSecurity.TargetSum.EUFCMA.signing_success_gt_131071_over_131072' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signing_success_gt_131071_over_131072

end XmssSecurity.TargetSum.EUFCMA
