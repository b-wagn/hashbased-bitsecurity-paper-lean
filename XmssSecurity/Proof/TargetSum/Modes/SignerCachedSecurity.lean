import XmssSecurity.Proof.TargetSum.Modes.SignerCachedLoss
import XmssSecurity.Proof.TargetSum.Direct.SourceEncodingReserve
import XmssSecurity.Proof.TargetSum.Direct.CachedEncodingCost
import XmssSecurity.Proof.TargetSum.Direct.LimitedAcceptanceTransfer

/-! The complete signer-counted 127-bit bound when the memoized adversary always
caches its forged encoding. The general case is completed in `Modes/Signer.lean`. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open Seeded Direct Deciding

theorem signer_cached_hazards_le_reserve (adversary : Security.StatementAdversary)
    (q : Nat) (hsmall : q < 2 ^ 127)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (hcached : HasCachedForgedEncoding (memoAdversary (Security.embed adversary))) :
    expectedCoupledHazards (q + 1)
        (publicLimitedAcceptedPrefixProbeExecution q (memoAdversary (Security.embed adversary))) ≤
      (q : ℝ≥0∞) + sourceEncodingReserve (memoAdversary (Security.embed adversary)) := by
  have hseed : q < 2 ^ 256 := hsmall.trans (by norm_num)
  apply (expectedCoupledLimitedProbe_hazards_le_source_credit _ q
    (signer_countedSourceBudget_after_trajectory adversary q hseed hbound)).trans
  apply add_le_add le_rfl
  apply (add_le_add le_rfl (query_ratio_le_half q hsmall)).trans
  exact acceptance_credit_add_half_le_reserve _ (one_le_expectedDirectEncoding_add_signer_of_cached _ hcached)

theorem signer_sourceSecondaryLoss_add_encodingReserve_le (adversary : Security.StatementAdversary)
    (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q) :
    sourceSecondaryLoss (memoAdversary (Security.embed adversary)) +
      sourceEncodingReserve (memoAdversary (Security.embed adversary)) /
        ((2 ^ digestBits : Nat) : ℝ≥0∞) ≤ (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
  (sourceSecondaryLoss_add_encodingReserve_le _).trans
    (ENNReal.div_le_div (signer_expectedClassBudget adversary q hsmall hbound) le_rfl)

theorem signer_cached_seeded_127 (adversary : Security.StatementAdversary)
    (q : Nat) (hsmall : q < 2 ^ 127)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (hcached : HasCachedForgedEncoding (memoAdversary (Security.embed adversary))) :
    forgeAdvantage Seeded.scheme (Security.embed adversary) ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  have hseed : q < 2 ^ 256 := hsmall.trans (by norm_num)
  apply (signer_cached_seeded_loss_le adversary q hseed hbound hcached).trans
  apply (add_le_add (mul_le_mul' (le_refl (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹))
    (signer_cached_hazards_le_reserve adversary q hsmall hbound hcached)) le_rfl).trans
  calc
    _ = (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (sourceSecondaryLoss (memoAdversary (Security.embed adversary)) +
          sourceEncodingReserve (memoAdversary (Security.embed adversary)) /
            ((2 ^ digestBits : Nat) : ℝ≥0∞)) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
      add_le_add le_rfl (signer_sourceSecondaryLoss_add_encodingReserve_le adversary q hseed hbound)
    _ = _ := by
      simp only [div_eq_mul_inv]
      rw [← mul_add]
      congr 1
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp (disch := finiteness) only [ENNReal.toReal_add]
      norm_num [ENNReal.toReal_inv, digestBits]

theorem signer_cached_advantage_127 (adversary : Security.StatementAdversary) (q : Nat)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (hcached : HasCachedForgedEncoding (memoAdversary (Security.embed adversary))) :
    (SUFCMA.notion ⟨false, true, false, false⟩).advantage xmss adversary ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  by_cases hlarge : 2 ^ 127 ≤ q
  · calc
      _ ≤ 1 := probEvent_le_one
      _ = ((2 ^ 127 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
        (ENNReal.div_self (by norm_num) (ENNReal.natCast_ne_top _)).symm
      _ ≤ _ := ENNReal.div_le_div (by exact_mod_cast hlarge) le_rfl
  · rw [advantage_eq_of_mode _ SUFCMA.CountingMode.direct,
      notion_direct_advantage_eq, Security.notionDirect_advantage_eq]
    exact signer_cached_seeded_127 adversary q (Nat.lt_of_not_ge hlarge) hbound hcached

/-- info: 'XmssSecurity.TargetSum.Modes.signer_cached_advantage_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_cached_advantage_127

end XmssSecurity.TargetSum.Modes
