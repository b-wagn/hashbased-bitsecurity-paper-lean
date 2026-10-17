import XmssSecurity.Proof.TargetSum.Modes.SignerClassBudget
import XmssSecurity.Proof.TargetSum.Direct.SourceLossBudget

/-! The source-side losses fit into one half of the 127-bit allowance, while retaining
an explicit reserve for encoding queries, seed queries, and signing. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open Seeded Direct

theorem signer_sourceSecondaryLoss_add_reserve_le
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q) :
    sourceSecondaryLoss (memoAdversary (Security.embed adversary)) +
      (expectedDirectEncodingQueries (memoAdversary (Security.embed adversary)) / 2 +
        expectedDirectSeedQueries (memoAdversary (Security.embed adversary)) / 2 +
        expectedSourceSignerHashes (memoAdversary (Security.embed adversary))) /
          ((2 ^ digestBits : Nat) : ℝ≥0∞) ≤ (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
  (sourceSecondaryLoss_add_reserve_le _).trans
    (ENNReal.div_le_div (signer_expectedClassBudget adversary q hsmall hbound) le_rfl)

theorem signer_sourceSecondaryLoss_le (adversary : Security.StatementAdversary)
    (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q) :
    sourceSecondaryLoss (memoAdversary (Security.embed adversary)) ≤
      (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
  (le_add_right le_rfl).trans (signer_sourceSecondaryLoss_add_reserve_le adversary q hsmall hbound)

/-- info: 'XmssSecurity.TargetSum.Modes.signer_sourceSecondaryLoss_add_reserve_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_sourceSecondaryLoss_add_reserve_le

end XmssSecurity.TargetSum.Modes
