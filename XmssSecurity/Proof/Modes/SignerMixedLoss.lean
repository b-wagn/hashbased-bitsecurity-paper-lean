import XmssSecurity.Proof.Modes.SignerAcceptedFirstLane
import XmssSecurity.Proof.Direct.FreshFirstLaneContribution
import XmssSecurity.Proof.Direct.SourceLossBudgetFresh
import XmssSecurity.Proof.Direct.FreshFirstLaneSplit

/-! The signer-mode reduction for arbitrary adversaries, retaining the actual fresh
first-lane contribution and the fresh second-lane allowance under one source budget. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Modes

open Seeded Direct Deciding

theorem signer_seeded_loss_le_source_credit_add_fresh (adversary : Security.StatementAdversary)
    (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q) :
    forgeAdvantage Seeded.scheme (Security.embed adversary) ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (TargetSum.acceptanceProbability *
          (expectedDirectEncodingQueries (memoAdversary (Security.embed adversary)) +
            expectedSourceSignerHashes (memoAdversary (Security.embed adversary)))) /
              ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        sourceSecondaryLoss (memoAdversary (Security.embed adversary)) +
        freshFirstLaneProbability (memoAdversary (Security.embed adversary)) +
        forgedEncodingFreshProbability (memoAdversary (Security.embed adversary)) *
          (TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞))) := by
  have hfirst := (decidingFirstLane_probability_le_accepted_add_fresh_contribution
    (memoAdversary (Security.embed adversary))).trans
      (add_le_add (signer_acceptedPrefixFirstLane_probability_le_source_credit adversary q hsmall hbound) le_rfl)
  apply (forgeAdvantage_deterministic_le_reference_expectedDirectSeed (Security.embed adversary)).trans
  apply (add_le_add (forgeAdvantage_le_deciding_lanes _) le_rfl).trans
  rw [add_assoc]
  apply (add_le_add hfirst
    (prehit_add_secondLane_add_seed_le_sourceSecondaryLoss_add_fresh _)).trans_eq
  ac_rfl

theorem signer_advantage_le_source_credit_add_fresh (adversary : Security.StatementAdversary)
    (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q) :
    (SUFCMA.notion ⟨false, true, false, false⟩).advantage xmss adversary ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (TargetSum.acceptanceProbability *
          (expectedDirectEncodingQueries (memoAdversary (Security.embed adversary)) +
            expectedSourceSignerHashes (memoAdversary (Security.embed adversary)))) /
              ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        sourceSecondaryLoss (memoAdversary (Security.embed adversary)) +
        freshFirstLaneProbability (memoAdversary (Security.embed adversary)) +
        forgedEncodingFreshProbability (memoAdversary (Security.embed adversary)) *
          (TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞))) := by
  rw [advantage_eq_of_mode _ SUFCMA.CountingMode.direct,
    notion_direct_advantage_eq, Security.notionDirect_advantage_eq]
  exact signer_seeded_loss_le_source_credit_add_fresh adversary q hsmall hbound

theorem signer_advantage_le_source_credit_add_fresh_revealed (adversary : Security.StatementAdversary)
    (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q) :
    (SUFCMA.notion ⟨false, true, false, false⟩).advantage xmss adversary ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (2 * TargetSum.acceptanceProbability *
          (expectedDirectEncodingQueries (memoAdversary (Security.embed adversary)) +
            expectedSourceSignerHashes (memoAdversary (Security.embed adversary)))) /
              ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        sourceSecondaryLoss (memoAdversary (Security.embed adversary)) +
        freshRevealedProbability (memoAdversary (Security.embed adversary)) +
        forgedEncodingFreshProbability (memoAdversary (Security.embed adversary)) *
          (TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞))) := by
  apply (signer_advantage_le_source_credit_add_fresh adversary q hsmall hbound).trans
  apply (add_le_add (add_le_add le_rfl
    (freshFirstLaneProbability_le_source_credit_add_revealed _)) le_rfl).trans_eq
  simp only [div_eq_mul_inv]
  ring

/-- info: 'XmssSecurity.Modes.signer_advantage_le_source_credit_add_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_advantage_le_source_credit_add_fresh

/-- info: 'XmssSecurity.Modes.signer_advantage_le_source_credit_add_fresh_revealed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_advantage_le_source_credit_add_fresh_revealed

end XmssSecurity.Modes
