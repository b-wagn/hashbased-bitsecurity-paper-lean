import Xmss.Proof.Checksum.HiddenSibling.FreshAverages
import Xmss.Proof.Generic.Direct.FreshVerificationPrefix

/-! Conditional verification for a fresh checksum digest: either its selected initial value is
honest, or the remaining path collides. -/

open OracleComp OracleSpec ENNReal
open Xmss.Generic

set_option backward.isDefEq.respectTransparency false

namespace Xmss.Checksum.HiddenSibling

open Generic.Deciding Generic.Direct

theorem fresh_verification_probability_le (adversary : Generic.Adversary)
    (hzero : IsDirectQueryBound adversary 0)
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅))
    (before : (Generic.Forgery × QueryLog SigningSpec) × QueryCache HashSpec)
    (hbefore : before ∈ support ((simulateQ romImpl
      (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (hfresh : before.2 (forgeryEncodingInput keyResult.1.1 before.1.1) = none)
    (signed : Digest) :
    Pr[fun result : GameOutcome × QueryCache HashSpec => result.1.won = true |
      (simulateQ romImpl (verificationPhase keyResult.1.1 keyResult.1.2 before.1)).run before.2] ≤
      Pr[fun digest => before.1.1.signature.chainValue (freshChain signed digest) =
          honestChainValue before.2 keyResult.1.2 before.1.1.epoch (freshChain signed digest)
            (encode digest (freshChain signed digest)) | ($ᵗ Digest)] +
        ((663 : ℝ≥0∞) / 16) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  classical
  let input := forgeryEncodingInput keyResult.1.1 before.1.1
  let guess : Digest → Prop := fun digest =>
    before.1.1.signature.chainValue (freshChain signed digest) =
      honestChainValue before.2 keyResult.1.2 before.1.1.epoch (freshChain signed digest)
        (encode digest (freshChain signed digest))
  have hparam := keygen_publicKey_parameter_eq keyResult hkey
  have hinput : input = CacheView.encodingInput keyResult.1.2.parameter
      before.1.1.epoch (before.1.1.message, before.1.1.signature.randomness) :=
    congrArg (fun parameter => CacheView.encodingInput parameter before.1.1.epoch
      (before.1.1.message, before.1.1.signature.randomness)) hparam
  have hle := xmssRom_cache_le _ keyResult.2 before hbefore
  have hcollision := zeroHash_prefix_no_structural_collision adversary hzero keyResult.1.1
    keyResult.1.2 keyResult.2 before hbefore
  have hpointwise (digest : Digest) :
      Pr[fun result : GameOutcome × QueryCache HashSpec => result.1.won = true |
        (simulateQ romImpl (verificationPhase keyResult.1.1 keyResult.1.2 before.1)).run
          (before.2.cacheQuery input digest)] ≤
        (if guess digest then 1 else 0) +
          ((decidingQueryBound - (encode digest (freshChain signed digest)).val : ℕ) : ℝ≥0∞) /
            ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
    by_cases hguess : guess digest
    · rw [if_pos hguess]
      exact le_add_right probEvent_le_one
    · rw [if_neg hguess, zero_add]
      have hprefix := fresh_encoding_prefix_support adversary keyResult.1.1 keyResult.1.2
        keyResult.2 before hbefore hfresh digest
      have hcacheLe : before.2 ≤ before.2.cacheQuery input digest :=
        QueryCache.le_cacheQuery before.2 hfresh
      have hdecode : forgedEncoding (before.2.cacheQuery input digest) keyResult.1.2.parameter
          before.1.1 = some (encode digest) := by
        unfold forgedEncoding CacheView.decodedEncoding
        rw [← hparam]
        rw [QueryCache.cacheQuery_self]
        rfl
      have hvalue : before.1.1.signature.chainValue (freshChain signed digest) ≠
          honestChainValue (before.2.cacheQuery input digest) keyResult.1.2 before.1.1.epoch
            (freshChain signed digest) (encode digest (freshChain signed digest)) := by
        rw [← honestChainValue_eq_of_keygen_cache_le keyResult hkey before.2
          (before.2.cacheQuery input digest) hle (hle.trans hcacheLe)]
        exact hguess
      have hnone : ¬ RandomOracle.AdaptiveFreshDigestCollisionWith keyResult.2
          (before.2.cacheQuery input digest) (keygenStructuralTargetInput keyResult.1.2 keyResult.2) := by
        rw [hinput]
        exact no_structural_collision_cacheQuery_encoding keyResult.1.2 keyResult.2 before.2
          hle before.1.1.epoch before.1.1.message before.1.1.signature.randomness digest
          (by rw [← hinput]; exact hfresh) hcollision
      refine (probEvent_mono fun result _ hwon => (result.1.won_eq_true_iff.mp hwon).2.2).trans ?_
      exact path_verification_probability_le (withForgedEncodingQuery adversary) keyResult hkey
        (before.1, before.2.cacheQuery input digest) hprefix (encode digest)
        (freshChain signed digest) hdecode hvalue hnone
  rw [verificationPhase_run_fresh_cached _ _ _ _ hfresh, probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' digest, Pr[= digest | ($ᵗ Digest)] *
        ((if guess digest then 1 else 0) +
          ((decidingQueryBound - (encode digest (freshChain signed digest)).val : ℕ) : ℝ≥0∞) /
            ((2 ^ digestBits : ℕ) : ℝ≥0∞)) := by
      exact ENNReal.tsum_le_tsum fun digest => mul_le_mul' le_rfl (hpointwise digest)
    _ = Pr[guess | ($ᵗ Digest)] +
        (∑' digest, Pr[= digest | ($ᵗ Digest)] *
          ((decidingQueryBound - (encode digest (freshChain signed digest)).val : ℕ) : ℝ≥0∞)) /
            ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
      simp_rw [mul_add, div_eq_mul_inv, ← mul_assoc]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, probEvent_eq_tsum_ite]
      congr 1
      apply tsum_congr
      intro digest
      split_ifs <;> simp
    _ ≤ _ := add_le_add le_rfl (ENNReal.div_le_div (expected_freshChain_path_le signed) le_rfl)

end Xmss.Checksum.HiddenSibling
