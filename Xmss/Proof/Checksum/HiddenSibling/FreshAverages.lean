import Xmss.Proof.Checksum.HiddenSibling.FreshProbe
import Xmss.Proof.Generic.Direct.PathVerificationProbability

/-! Average path cost and the exceptional equal-digest case for a fresh encoding query. -/

open OracleComp OracleSpec ENNReal
open scoped BigOperators
open Xmss.Generic

set_option backward.isDefEq.respectTransparency false

namespace Xmss.Checksum.HiddenSibling

open Generic.Deciding

theorem expected_freshChain_path_le (signed : Digest) :
    (∑' digest : Digest, Pr[= digest | ($ᵗ Digest)] *
      ((decidingQueryBound - (encode digest (freshChain signed digest)).val : ℕ) : ℝ≥0∞)) ≤
      (663 : ℝ≥0∞) / 16 := by
  have hsum := sum_firstMessageDifference_path_le (messageDigit signed)
  have hcast : (∑ digest : Digest,
      ((48 - (messageDigit digest
        (firstMessageDifference (messageDigit signed) (messageDigit digest))).val : ℕ) : ℝ≥0∞)) ≤
      ((663 * 2 ^ 124 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hsum
  simp only [probOutput_uniformSample, card_bitVec, decidingQueryBound_eq,
    freshChain, Checksum.encode_messageChain]
  rw [tsum_fintype, ← Finset.mul_sum]
  refine (mul_le_mul' le_rfl hcast).trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [digestBits, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div]

private theorem uniform_guard_target {α : Type} (head : ProbComp α)
    (guard : α → Prop) (target : α → Digest) :
    Pr[fun result : α × Digest => guard result.1 ∧ result.2 = target result.1 |
      (do let value ← head; let digest ← $ᵗ Digest; pure (value, digest))] =
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ * Pr[guard | head] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite head guard, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro value
  rw [bind_pure_comp, probEvent_map]
  by_cases hguard : guard value
  · simp only [Function.comp_def, hguard, true_and, if_true, RandomOracle.uniform_eq_probability]
    exact mul_comm (Pr[= value | head]) (((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹)
  · simp [hguard]

private theorem uniform_guard_marginal {α : Type} (head : ProbComp α) (guard : α → Prop) :
    Pr[fun result : α × Digest => guard result.1 |
      (do let value ← head; let digest ← $ᵗ Digest; pure (value, digest))] = Pr[guard | head] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite head guard]
  apply tsum_congr
  intro value
  rw [bind_pure_comp, probEvent_map]
  by_cases hguard : guard value <;> simp [hguard, ENNReal.div_self]

theorem sourceFresh_equal_digest_probability (adversary : Generic.Adversary) :
    Pr[fun sample => SourceFreshSigned sample ∧ sample.2 =
        referenceDigest sample.1.2.2.1.1.1 sample.1.1.secretKey.parameter
          sample.1.2.2.2.toSigningLog sample.1.2.1.epoch |
      sourceSampledPrefixProgram adversary] =
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        Pr[SourceFreshSigned | sourceSampledPrefixProgram adversary] := by
  let guard : SourcePrefixResult → Prop := fun result =>
    FreshSigned result.2.2.1.1.1 result.1.secretKey.parameter
      result.2.2.2.toSigningLog result.2.1
  let target : SourcePrefixResult → Digest := fun result =>
    referenceDigest result.2.2.1.1.1 result.1.secretKey.parameter result.2.2.2.toSigningLog
      result.2.1.epoch
  have heq := uniform_guard_target (sourcePrefixProgram adversary) guard target
  have hmarginal := uniform_guard_marginal (sourcePrefixProgram adversary) guard
  exact heq.trans (congrArg (((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ * ·) hmarginal.symm)

theorem sourceFreshSigned_marginal (adversary : Generic.Adversary) :
    Pr[SourceFreshSigned | sourceSampledPrefixProgram adversary] =
      Pr[FreshSourcePrefix | sourcePrefixProgram adversary] :=
  uniform_guard_marginal (sourcePrefixProgram adversary) FreshSourcePrefix

end Xmss.Checksum.HiddenSibling
