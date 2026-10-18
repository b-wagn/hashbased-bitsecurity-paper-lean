import XmssSecurity.Proof.TargetSum.Direct.LimitedAcceptanceCancellation
import XmssSecurity.Proof.TargetSum.Direct.FreshVerificationProbability
import XmssSecurity.Proof.TargetSum.Modes.SignerClassBudget
import XmssSecurity.Proof.TargetSum.Direct.SourceLossBudget
import XmssSecurity.Proof.TargetSum.Modes.SignerSourceBudget
import XmssSecurity.Proof.TargetSum.Direct.LimitedPrefixCoupling
import XmssSecurity.Proof.TargetSum.Direct.LimitedAcceptedProbe
import XmssSecurity.Proof.TargetSum.Modes.SignerPrehit
import XmssSecurity.Proof.TargetSum.Direct.DecidingSecondLaneFresh
import XmssSecurity.Proof.TargetSum.Direct.SourceLossBudgetFresh
import XmssSecurity.Proof.TargetSum.Direct.FreshFirstLaneSplit
import XmssSecurity.Proof.TargetSum.Modes.SignerCachedSecurity
import XmssSecurity.Proof.TargetSum.Direct.MixedFirstLane
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The signer-mode assembly with one shared first-lane prefix budget. Its remaining
fresh-verification allowance fits the encoding reserve once that expected credit is at least 1/128. -/

open OracleComp OracleSpec ENNReal

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open Seeded Direct Deciding

theorem signer_seeded_loss_le_shared_prefix (adversary : Security.StatementAdversary)
    (q : Nat) (hsmall : q < 2 ^ 256) (hq : q + 1 ≤ 2 ^ 127)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q) :
    forgeAdvantage Seeded.scheme (Security.embed adversary) ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        sourceSecondaryLoss (Seeded.memoAdversary (Security.embed adversary)) +
        (TargetSum.acceptanceProbability *
          (2 * (Direct.expectedDirectEncodingQueries (Seeded.memoAdversary (Security.embed adversary)) +
              expectedSourceSignerHashes (Seeded.memoAdversary (Security.embed adversary))) + 1 +
            40 * forgedEncodingFreshProbability (Seeded.memoAdversary (Security.embed adversary)))) /
              ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  have hfirst := decidingFirstLane_probability_le_shared_prefix
    (Seeded.memoAdversary (Security.embed adversary)) q
    (signer_countedSourceBudget_after_trajectory adversary q hsmall hbound)
  apply (forgeAdvantage_deterministic_le_reference_expectedDirectSeed (Security.embed adversary)).trans
  apply (add_le_add (Deciding.forgeAdvantage_le_deciding_lanes _) le_rfl).trans
  rw [add_assoc]
  apply (add_le_add hfirst
    (prehit_add_secondLane_add_seed_le_sourceSecondaryLoss_add_fresh _
      (signer_prehit_le adversary q hq hbound))).trans_eq
  simp only [div_eq_mul_inv]
  ring

theorem signer_advantage_le_shared_prefix (adversary : Security.StatementAdversary)
    (q : Nat) (hsmall : q < 2 ^ 256) (hq : q + 1 ≤ 2 ^ 127)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q) :
    (SUFCMA.notion ⟨false, true, false, false⟩).advantage Generic.xmss adversary ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        sourceSecondaryLoss (Seeded.memoAdversary (Security.embed adversary)) +
        (TargetSum.acceptanceProbability *
          (2 * (Direct.expectedDirectEncodingQueries (Seeded.memoAdversary (Security.embed adversary)) +
              expectedSourceSignerHashes (Seeded.memoAdversary (Security.embed adversary))) + 1 +
            40 * forgedEncodingFreshProbability (Seeded.memoAdversary (Security.embed adversary)))) /
              ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  rw [advantage_eq_of_mode _ SUFCMA.CountingMode.direct,
    notion_direct_advantage_eq, Security.notionDirect_advantage_eq]
  exact signer_seeded_loss_le_shared_prefix adversary q hsmall hq hbound

theorem mixed_probe_allowance_le_encodingReserve (adversary : Adversary)
    (hcredit : (1 / 128 : ℝ≥0∞) ≤
      Direct.expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary) :
    TargetSum.acceptanceProbability *
      (2 * (Direct.expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary) + 1 +
        40 * forgedEncodingFreshProbability adversary) ≤ sourceEncodingReserve adversary := by
  let credit := Direct.expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary
  have hunit : (1 : ℝ≥0∞) ≤ 128 * credit := by
    calc
      _ = (128 : ℝ≥0∞) * (1 / 128) := by
        rw [one_div]
        exact (ENNReal.mul_inv_cancel (by norm_num) (by finiteness)).symm
      _ ≤ _ := mul_le_mul' le_rfl hcredit
  have hcount : 2 * credit + 1 + 40 * forgedEncodingFreshProbability adversary ≤ 5250 * credit := by
    calc
      _ ≤ 2 * credit + 1 + 40 * 1 :=
        add_le_add le_rfl (mul_le_mul' le_rfl (forgedEncodingFreshProbability_le_one adversary))
      _ = 2 * credit + 41 := by ring
      _ ≤ 2 * credit + 41 * (128 * credit) :=
        add_le_add le_rfl (by simpa using mul_le_mul' (le_refl (41 : ℝ≥0∞)) hunit)
      _ = _ := by ring
  have hrate : TargetSum.acceptanceProbability * 5250 ≤ (3 / 8 : ℝ≥0∞) := by
    unfold TargetSum.acceptanceProbability
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, digestBits]
  calc
    _ ≤ TargetSum.acceptanceProbability * (5250 * credit) := mul_le_mul' le_rfl hcount
    _ = (TargetSum.acceptanceProbability * 5250) * credit := (mul_assoc _ _ _).symm
    _ ≤ (3 / 8 : ℝ≥0∞) * credit := mul_le_mul' hrate le_rfl

theorem signer_advantage_127_of_encoding_credit (adversary : Security.StatementAdversary) (q : Nat)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q)
    (hcredit : (1 / 128 : ℝ≥0∞) ≤
      Direct.expectedDirectEncodingQueries (Seeded.memoAdversary (Security.embed adversary)) +
        expectedSourceSignerHashes (Seeded.memoAdversary (Security.embed adversary))) :
    (SUFCMA.notion ⟨false, true, false, false⟩).advantage Generic.xmss adversary ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  by_cases hlarge : 2 ^ 127 ≤ q
  · calc
      _ ≤ 1 := probEvent_le_one
      _ = ((2 ^ 127 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
        (ENNReal.div_self (by norm_num) (ENNReal.natCast_ne_top _)).symm
      _ ≤ _ := ENNReal.div_le_div (by exact_mod_cast hlarge) le_rfl
  · have hsmall : q < 2 ^ 256 := (Nat.lt_of_not_ge hlarge).trans (by norm_num)
    apply (signer_advantage_le_shared_prefix adversary q hsmall (by omega) hbound).trans
    apply (add_le_add le_rfl (ENNReal.div_le_div
      (mixed_probe_allowance_le_encodingReserve _ hcredit) le_rfl)).trans
    rw [add_assoc]
    apply (add_le_add le_rfl
      (signer_sourceSecondaryLoss_add_encodingReserve_le adversary q hsmall hbound)).trans_eq
    simp only [div_eq_mul_inv]
    rw [← mul_add]
    congr 1
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add]
    norm_num [ENNReal.toReal_inv, digestBits]

/-- info: 'XmssSecurity.TargetSum.Modes.signer_advantage_le_shared_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_advantage_le_shared_prefix

/-- info: 'XmssSecurity.TargetSum.Modes.signer_advantage_127_of_encoding_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_advantage_127_of_encoding_credit

end XmssSecurity.TargetSum.Modes
