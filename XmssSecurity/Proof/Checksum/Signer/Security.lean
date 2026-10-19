import XmssSecurity.Proof.Checksum.Modes.Keygen
import XmssSecurity.Proof.Generic.Modes.Projection
import XmssSecurity.Proof.Checksum.NoSign.ExactThreeBudget
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability

/-!
# Security when the signer's hash calls are charged

The checksum scheme has 123 bits when signer hashes are charged, and 124 when requests are
also charged. Large budgets use the shared deciding-path bound; small budgets use the unsigned
bound or the exact three-query argument in `NoSign/ExactThreeBudget.lean`.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.Checksum.Modes
open XmssSecurity.Modes

open SUFCMA

/-- Charging the signer charges at least the adversary's own hash queries. -/
theorem signer_direct_hasQueryBound (requests : Bool) (adversary : Security.StatementAdversary)
    (q : ℕ) (hbound : (SUFCMA.notion ⟨false, true, false, requests⟩).HasQueryBound Generic.xmss adversary q) :
    SUFCMA.notionDirect.HasQueryBound Generic.xmss adversary q :=
  (notion_direct_hasQueryBound_iff Generic.xmss adversary q).1
    (hasQueryBound_of_le (by simp [CountingMode.Le, CountingMode.direct]) Generic.xmss adversary q hbound)

/-- The direct-query loss with `q` direct queries, `(2q + 51) / 2^128 + q / 2^256`, is below
`q / 2^bits` when `2q + 52 ≤ 2^(128 - bits) q` and `q ≤ 2^128`; stated for the two levels used. -/
theorem sharedDecidingLoss_le_123 (q : ℕ) (hlarge : 2 ≤ q) (hq : q ≤ 2 ^ 128) :
    Direct.sharedDecidingLoss q ≤ (q : ℝ≥0∞) / ((2 ^ 123 : ℕ) : ℝ≥0∞) := by
  have hlarge' : (2 : ℝ) ≤ q := by exact_mod_cast hlarge
  have hq' : (q : ℝ) ≤ 2 ^ 128 := by exact_mod_cast hq
  unfold Direct.sharedDecidingLoss
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_mul]
  simp only [digestBits]
  push_cast
  linarith

theorem sharedDecidingLoss_le_124 (q : ℕ) (hlarge : 4 ≤ q) (hq : q ≤ 2 ^ 128) :
    Direct.sharedDecidingLoss q ≤ (q : ℝ≥0∞) / ((2 ^ 124 : ℕ) : ℝ≥0∞) := by
  have hlarge' : (4 : ℝ) ≤ q := by exact_mod_cast hlarge
  have hq' : (q : ℝ) ≤ 2 ^ 128 := by exact_mod_cast hq
  unfold Direct.sharedDecidingLoss
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_mul]
  simp only [digestBits]
  push_cast
  linarith

theorem signer_advantage_le_of_loss (requests : Bool) (bits : ℕ) (hbits : bits ≤ 128)
    (adversary : Security.StatementAdversary) (q : ℕ)
    (hbound : (SUFCMA.notion ⟨false, true, false, requests⟩).HasQueryBound Generic.xmss adversary q)
    (hloss : q ≤ 2 ^ 128 → Direct.sharedDecidingLoss q ≤ (q : ℝ≥0∞) / ((2 ^ bits : ℕ) : ℝ≥0∞)) :
    (SUFCMA.notion ⟨false, true, false, requests⟩).advantage Generic.xmss adversary ≤
      (q : ℝ≥0∞) / ((2 ^ bits : ℕ) : ℝ≥0∞) := by
  by_cases hhuge : 2 ^ bits ≤ q
  · calc
      _ ≤ 1 := probEvent_le_one
      _ = ((2 ^ bits : ℕ) : ℝ≥0∞) / ((2 ^ bits : ℕ) : ℝ≥0∞) :=
        (ENNReal.div_self (by positivity) (ENNReal.natCast_ne_top _)).symm
      _ ≤ _ := by gcongr
  have hq : q ≤ 2 ^ 128 :=
    (Nat.lt_of_not_ge hhuge).le.trans (Nat.pow_le_pow_right (by norm_num) hbits)
  have hdirect := signer_direct_hasQueryBound requests adversary q hbound
  rw [advantage_eq_of_mode _ SUFCMA.CountingMode.direct,
    notion_direct_advantage_eq, Security.notionDirect_advantage_eq,
    Security.forgeAdvantage_prune_eq adversary q hdirect]
  exact (Direct.seeded_forgeAdvantage_le_sharedDecidingLoss _ _
    (Direct.pruneAdversary_isDirectQueryBound _ (Security.embed adversary))).trans (hloss hq)

/-- The no-signature loss `(2q + 2) / 2^128 + q / 2^256` is below `q / 2^bits` when
`2q + 3 ≤ 2^(128 - bits) q`; stated for the two levels used. -/
theorem noSignLoss_le (q bits : ℕ) (hq : 1 ≤ q) (hbits : bits ≤ 124) :
    ((2 * q + 2 : ℕ) : ℝ≥0∞) * NoSign.digestInverse + q / ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤
      (q : ℝ≥0∞) / ((2 ^ bits : ℕ) : ℝ≥0∞) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpow : (2 : ℝ) ^ bits ≤ 2 ^ 124 := pow_le_pow_right₀ (by norm_num) hbits
  unfold NoSign.digestInverse
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  push_cast
  simp only [digestBits]
  have hsmall : (q : ℝ) / 2 ^ 256 ≤ q / 2 ^ 128 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by norm_num)
  have hlevel : (q : ℝ) / 2 ^ 124 ≤ q / 2 ^ bits :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
  have hsum : ((2 : ℝ) * (q : ℝ) + 2) / (2 : ℝ) ^ 128 + (q : ℝ) / (2 : ℝ) ^ 128 =
      (3 * (q : ℝ) + 2) / (2 : ℝ) ^ 128 := by ring
  have hmain : (3 * (q : ℝ) + 2) / (2 : ℝ) ^ 128 ≤ (q : ℝ) / (2 : ℝ) ^ 124 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [← div_eq_mul_inv]
  linarith

theorem sufCmaSigner_123 :
    (SUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits Generic.xmss 123 := by
  intro q hq adversary hbound
  by_cases hsmall : q = 1
  · exact (NoSign.signer_small_advantage_le false adversary q (by simp [hsmall]) hbound).trans
      (noSignLoss_le q 123 hq (by norm_num))
  · exact signer_advantage_le_of_loss false 123 (by norm_num) adversary q hbound
      (sharedDecidingLoss_le_123 q (by omega))

/-- The 124-bit bound already holds at every positive budget except `3`. -/
theorem signerRequests_advantage_le_124_of_ne_three
    (q : ℕ) (hq : 1 ≤ q) (hthree : q ≠ 3) (adversary : Security.StatementAdversary)
    (hbound : (SUFCMA.notion ⟨false, true, false, true⟩).HasQueryBound
      Generic.xmss adversary q) :
    (SUFCMA.notion ⟨false, true, false, true⟩).advantage Generic.xmss adversary ≤
      (q : ℝ≥0∞) / ((2 ^ 124 : ℕ) : ℝ≥0∞) := by
  by_cases hsmall : q ≤ 2
  · exact (NoSign.signer_small_advantage_le true adversary q (by simp; omega) hbound).trans
      (noSignLoss_le q 124 hq le_rfl)
  · exact signer_advantage_le_of_loss true 124 (by norm_num) adversary q hbound
      (sharedDecidingLoss_le_124 q (by omega))

/-- Every other positive budget is already covered, so budget `3` suffices for 124 bits. -/
theorem sufCmaSignerRequests_124_iff_three :
    (SUFCMA.notion ⟨false, true, false, true⟩).HasClassicalSecurityBits Generic.xmss 124 ↔
      ∀ adversary : Security.StatementAdversary,
        (SUFCMA.notion ⟨false, true, false, true⟩).HasQueryBound Generic.xmss adversary 3 →
          (SUFCMA.notion ⟨false, true, false, true⟩).advantage Generic.xmss adversary ≤
            48 * NoSign.digestInverse := by
  have hthreshold : ((3 : ℕ) : ℝ≥0∞) / ((2 ^ 124 : ℕ) : ℝ≥0∞) =
      48 * NoSign.digestInverse := by
    unfold NoSign.digestInverse
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [digestBits, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv]
  constructor
  · intro h adversary hbound
    simpa only [hthreshold] using h 3 (by norm_num) adversary hbound
  · intro h q hq adversary hbound
    by_cases hthree : q = 3
    · subst q
      simpa only [hthreshold] using h adversary hbound
    · exact signerRequests_advantage_le_124_of_ne_three q hq hthree adversary hbound

/-- Charging signer hashes and requests gives 124 bits for every positive budget. -/
theorem sufCmaSignerRequests_124 :
    (SUFCMA.notion ⟨false, true, false, true⟩).HasClassicalSecurityBits Generic.xmss 124 :=
  sufCmaSignerRequests_124_iff_three.mpr NoSign.signerRequests_three_advantage_le

end XmssSecurity.Checksum.Modes
