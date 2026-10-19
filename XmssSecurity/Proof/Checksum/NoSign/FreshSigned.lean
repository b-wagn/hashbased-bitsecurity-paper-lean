import XmssSecurity.Proof.Checksum.NoSign.FreshVerification
import XmssSecurity.Proof.Generic.Direct.SourcePrefixProbability

/-! The fresh, signed branch costs at most `695 / (16 * 2^128)`, with its own probability weight. -/

open OracleComp OracleSpec ENNReal
open XmssSecurity.Generic

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Checksum.NoSign

open Generic.Deciding Generic.CappedChain

def FreshHonestGuess (sample : SourcePrefixResult × Digest) : Prop :=
  let signed := referenceDigest sample.1.2.2.1.1.1 sample.1.1.secretKey.parameter
    sample.1.2.2.2.toSigningLog sample.1.2.1.epoch
  let chain := freshChain signed sample.2
  SourceFreshSigned sample ∧
    sample.1.1.table (chain, sample.1.2.1.epoch, encode sample.2 chain) =
      sample.1.2.1.signature.chainValue chain

theorem freshHonestGuess_probability_le (adversary : Generic.Adversary)
    (hzero : Direct.IsDirectQueryBound adversary 0) :
    Pr[FreshHonestGuess | sourceSampledPrefixProgram adversary] ≤
      2 * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        Pr[FreshSourcePrefix | sourcePrefixProgram adversary] := by
  let equalDigest : SourcePrefixResult × Digest → Prop := fun sample =>
    SourceFreshSigned sample ∧ sample.2 = referenceDigest sample.1.2.2.1.1.1
      sample.1.1.secretKey.parameter sample.1.2.2.2.toSigningLog sample.1.2.1.epoch
  calc
    _ ≤ Pr[fun sample => equalDigest sample ∨ SourceFreshGuess sample |
        sourceSampledPrefixProgram adversary] := by
      apply probEvent_mono
      intro sample _ hguess
      by_cases heq : sample.2 = referenceDigest sample.1.2.2.1.1.1 sample.1.1.secretKey.parameter
          sample.1.2.2.2.toSigningLog sample.1.2.1.epoch
      · exact Or.inl ⟨hguess.1, heq⟩
      · exact Or.inr ⟨hguess.1, heq, hguess.2⟩
    _ ≤ Pr[equalDigest | sourceSampledPrefixProgram adversary] +
        Pr[SourceFreshGuess | sourceSampledPrefixProgram adversary] := probEvent_or_le _ _ _
    _ ≤ ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
          Pr[SourceFreshSigned | sourceSampledPrefixProgram adversary] +
        ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
          Pr[SourceFreshSigned | sourceSampledPrefixProgram adversary] :=
      add_le_add (sourceFresh_equal_digest_probability adversary).le
        (sourceFreshGuess_probability_le adversary hzero)
    _ = _ := by rw [sourceFreshSigned_marginal]; ring

open Classical in
theorem fresh_signed_verification_probability_le (adversary : Generic.Adversary)
    (hzero : Direct.IsDirectQueryBound adversary 0) :
    (∑' before, Pr[= before | sourcePrefixProgram adversary] *
      (if FreshSourcePrefix before then
        Pr[fun result : GameOutcome × QueryCache HashSpec => result.1.won = true |
          sourcePrefixVerification before] else 0)) ≤
      ((695 : ℝ≥0∞) / 16) * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        Pr[FreshSourcePrefix | sourcePrefixProgram adversary] := by
  let pathCost : ℝ≥0∞ := ((663 : ℝ≥0∞) / 16) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)
  have hpointwise (before : SourcePrefixResult)
      (hbefore : before ∈ support (sourcePrefixProgram adversary)) :
      (if FreshSourcePrefix before then
        Pr[fun result : GameOutcome × QueryCache HashSpec => result.1.won = true |
          sourcePrefixVerification before] else 0) ≤
      Pr[FreshHonestGuess | (fun digest : Digest => (before, digest)) <$> ($ᵗ Digest)] +
        pathCost * (if FreshSourcePrefix before then 1 else 0) := by
    by_cases hfresh : FreshSourcePrefix before
    · simp only [if_pos hfresh, mul_one]
      obtain ⟨hkey, hprefix⟩ := sourcePrefixProgram_support adversary before hbefore
      let keyResult := Concrete.materializeCachedKeyResult before.1.keyResult
      have hkeygen : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅) :=
        Concrete.oldKeygen_support_materializedPrecomputedKeygen before.1.keyResult
          (trajectoryProgrammedGlobalChainKeygen_support_keyResult before.1 hkey)
      have hphase := sourcePrefixExecution_phase_support adversary before.1 before.2 hprefix
      have hparameter := keygen_publicKey_parameter_eq keyResult hkeygen
      let signed := referenceDigest before.2.2.1.1.1 before.1.secretKey.parameter
        before.2.2.2.toSigningLog before.2.1.epoch
      have hbound := fresh_verification_probability_le adversary hzero keyResult hkeygen
        ((before.2.1, before.2.2.2.toSigningLog), before.2.2.1.1.1) hphase
        (by
          change before.2.2.1.1.1 (Direct.forgeryEncodingInput keyResult.1.1 before.2.1) = none
          unfold Direct.forgeryEncodingInput
          rw [hparameter]
          exact hfresh.1) signed
      refine hbound.trans (le_of_eq ?_)
      congr 1
      rw [probEvent_map]
      apply probEvent_congr' _ rfl
      intro digest _
      have hle : before.1.cache ≤ before.2.2.1.1.1 :=
        xmssRom_cache_le _ before.1.cache _ hphase
      change before.2.1.signature.chainValue (freshChain signed digest) =
          honestChainValue before.2.2.1.1.1
            (Concrete.materializePrecomputation before.1.cache before.1.secretKey)
            before.2.1.epoch (freshChain signed digest) (encode digest (freshChain signed digest)) ↔
        FreshHonestGuess (before, digest)
      rw [keyView_honestChainValue_eq_table before.1 hkey _ hle]
      change (_ = _) ↔ FreshSourcePrefix before ∧ _ = _
      simp only [hfresh, true_and, eq_comm]
      rfl
    · rw [if_neg hfresh]
      exact zero_le
  calc
    _ ≤ ∑' before, Pr[= before | sourcePrefixProgram adversary] *
        (Pr[FreshHonestGuess | (fun digest : Digest => (before, digest)) <$> ($ᵗ Digest)] +
          pathCost * (if FreshSourcePrefix before then 1 else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro before
      by_cases hbefore : before ∈ support (sourcePrefixProgram adversary)
      · exact mul_le_mul' le_rfl (hpointwise before hbefore)
      · rw [probOutput_eq_zero_of_not_mem_support hbefore, zero_mul, zero_mul]
    _ = Pr[FreshHonestGuess | sourceSampledPrefixProgram adversary] +
        pathCost * Pr[FreshSourcePrefix | sourcePrefixProgram adversary] := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add]
      congr 1
      · rw [sourceSampledPrefixProgram, probEvent_bind_eq_tsum]
        apply tsum_congr
        intro before
        rw [bind_pure_comp]
      · rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro before
        split_ifs <;> simp [mul_comm, mul_left_comm]
    _ ≤ 2 * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
          Pr[FreshSourcePrefix | sourcePrefixProgram adversary] +
        pathCost * Pr[FreshSourcePrefix | sourcePrefixProgram adversary] :=
      add_le_add (freshHonestGuess_probability_le adversary hzero) le_rfl
    _ = _ := by
      unfold pathCost
      rw [div_eq_mul_inv]
      have hconstant : (2 : ℝ≥0∞) + 663 / 16 = 695 / 16 := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
        norm_num [ENNReal.toReal_add, ENNReal.toReal_div]
      calc
        _ = (2 + 663 / 16) * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
            Pr[FreshSourcePrefix | sourcePrefixProgram adversary] := by ring
        _ = _ := by rw [hconstant]

end XmssSecurity.Checksum.NoSign
