import XmssSecurity.Proof.Modes.SignerSharedPrefix
import XmssSecurity.Proof.Direct.TerminalMixedFirstLane

/-! Complete signer-counted 127-bit security. A terminal-query saving handles small
expected encoding credit; the shared-prefix reserve handles the complementary case. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Modes

open Seeded Direct Deciding

theorem signer_seeded_loss_le_terminal_credit (adversary : Security.StatementAdversary)
    (q : Nat) (hpositive : 0 < q) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q) :
    forgeAdvantage Seeded.scheme (Security.embed adversary) ≤
      ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        sourceSecondaryLoss (memoAdversary (Security.embed adversary)) +
        ((2 + Checksum.acceptanceProbability) *
          (expectedDirectEncodingQueries (memoAdversary (Security.embed adversary)) +
            expectedSourceSignerHashes (memoAdversary (Security.embed adversary))) +
          2 * Checksum.acceptanceProbability + 40 * Checksum.acceptanceProbability *
            forgedEncodingFreshProbability (memoAdversary (Security.embed adversary))) /
              ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  have hfirst := decidingFirstLane_probability_le_terminal_credit
    (memoAdversary (Security.embed adversary)) q hpositive
    (signer_countedSourceBudget_after_trajectory adversary q hsmall hbound)
  apply (forgeAdvantage_deterministic_le_reference_expectedDirectSeed (Security.embed adversary)).trans
  apply (add_le_add (forgeAdvantage_le_deciding_lanes _) le_rfl).trans
  rw [add_assoc]
  apply (add_le_add hfirst
    (prehit_add_secondLane_add_seed_le_sourceSecondaryLoss_add_fresh _)).trans_eq
  simp only [div_eq_mul_inv]
  ring

theorem signer_advantage_le_terminal_credit (adversary : Security.StatementAdversary)
    (q : Nat) (hpositive : 0 < q) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q) :
    (SUFCMA.notion ⟨false, true, false, false⟩).advantage xmss adversary ≤
      ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        sourceSecondaryLoss (memoAdversary (Security.embed adversary)) +
        ((2 + Checksum.acceptanceProbability) *
          (expectedDirectEncodingQueries (memoAdversary (Security.embed adversary)) +
            expectedSourceSignerHashes (memoAdversary (Security.embed adversary))) +
          2 * Checksum.acceptanceProbability + 40 * Checksum.acceptanceProbability *
            forgedEncodingFreshProbability (memoAdversary (Security.embed adversary))) /
              ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  rw [advantage_eq_of_mode _ SUFCMA.CountingMode.direct,
    notion_direct_advantage_eq, Security.notionDirect_advantage_eq]
  exact signer_seeded_loss_le_terminal_credit adversary q hpositive hsmall hbound

theorem terminal_allowance_le_one (adversary : Adversary)
    (hcredit : expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary ≤
      (1 / 512 : ℝ≥0∞)) :
    (2 + Checksum.acceptanceProbability) *
        (expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary) +
      2 * Checksum.acceptanceProbability + 40 * Checksum.acceptanceProbability *
        forgedEncodingFreshProbability adversary ≤ 1 := by
  calc
    _ ≤ (2 + Checksum.acceptanceProbability) * (1 / 512 : ℝ≥0∞) +
        2 * Checksum.acceptanceProbability + 40 * Checksum.acceptanceProbability * 1 :=
      add_le_add (add_le_add (mul_le_mul' le_rfl hcredit) le_rfl)
        (mul_le_mul' le_rfl (forgedEncodingFreshProbability_le_one adversary))
    _ ≤ _ := by
      unfold Checksum.acceptanceProbability
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul]
      norm_num [ENNReal.toReal_div, ENNReal.toReal_inv, digestBits]

theorem signer_advantage_127_of_small_encoding_credit
    (adversary : Security.StatementAdversary) (q : Nat) (hpositive : 0 < q)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (hcredit : expectedDirectEncodingQueries (memoAdversary (Security.embed adversary)) +
      expectedSourceSignerHashes (memoAdversary (Security.embed adversary)) ≤ (1 / 512 : ℝ≥0∞)) :
    (SUFCMA.notion ⟨false, true, false, false⟩).advantage xmss adversary ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  by_cases hlarge : 2 ^ 127 ≤ q
  · calc
      _ ≤ 1 := probEvent_le_one
      _ = ((2 ^ 127 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
        (ENNReal.div_self (by norm_num) (ENNReal.natCast_ne_top _)).symm
      _ ≤ _ := ENNReal.div_le_div (by exact_mod_cast hlarge) le_rfl
  · have hsmall : q < 2 ^ 256 := (Nat.lt_of_not_ge hlarge).trans (by norm_num)
    have hsecondary : sourceSecondaryLoss (memoAdversary (Security.embed adversary)) ≤
        (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
      (le_add_right le_rfl).trans (signer_sourceSecondaryLoss_add_encodingReserve_le adversary q hsmall hbound)
    have hq : ((q - 1 : Nat) : ℝ≥0∞) + 1 = (q : ℝ≥0∞) := by
      exact_mod_cast Nat.sub_add_cancel hpositive
    apply (signer_advantage_le_terminal_credit adversary q hpositive hsmall hbound).trans
    apply (add_le_add (add_le_add le_rfl hsecondary)
      (ENNReal.div_le_div (terminal_allowance_le_one _ hcredit) le_rfl)).trans_eq
    calc
      _ = (((q - 1 : Nat) : ℝ≥0∞) + 1) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
          (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
        simp only [div_eq_mul_inv]
        ring
      _ = (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
          (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by rw [hq]
      _ = _ := by
        simp only [div_eq_mul_inv]
        rw [← mul_add]
        congr 1
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add]
        norm_num [ENNReal.toReal_inv, digestBits]

theorem sufCmaSigner_127 :
    (SUFCMA.notion ⟨false, true, false, false⟩).HasClassicalSecurityBits xmss 127 := by
  intro q hpositive adversary hbound
  by_cases hcredit : (1 / 512 : ℝ≥0∞) ≤
      expectedDirectEncodingQueries (memoAdversary (Security.embed adversary)) +
        expectedSourceSignerHashes (memoAdversary (Security.embed adversary))
  · exact signer_advantage_127_of_encoding_credit adversary q hbound hcredit
  · exact signer_advantage_127_of_small_encoding_credit adversary q hpositive hbound
      (le_of_not_ge hcredit)

/-- info: 'XmssSecurity.Modes.sufCmaSigner_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sufCmaSigner_127

end XmssSecurity.Modes

