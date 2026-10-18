import XmssSecurity.Proof.TargetSum.Modes.SignerClassBudget
import XmssSecurity.Proof.TargetSum.Direct.SourceLossBudget
import XmssSecurity.Proof.TargetSum.Modes.SignerSourceBudget
import XmssSecurity.Proof.TargetSum.Direct.LimitedPrefixCoupling
import XmssSecurity.Proof.TargetSum.Direct.LimitedAcceptedProbe
import XmssSecurity.Proof.TargetSum.Direct.SourceEncodingReserve
import XmssSecurity.Proof.TargetSum.Direct.CachedEncodingCost
import XmssSecurity.Proof.TargetSum.Direct.SourcePrefixAcceptance
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The signer-counted budget pays for the source-side secondary losses and the encoding
reserve. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open Seeded Direct Deciding

theorem signer_sourceSecondaryLoss_add_encodingReserve_le (adversary : Security.StatementAdversary)
    (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q) :
    sourceSecondaryLoss (Seeded.memoAdversary (Security.embed adversary)) +
      sourceEncodingReserve (Seeded.memoAdversary (Security.embed adversary)) /
        ((2 ^ digestBits : Nat) : ℝ≥0∞) ≤ (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
  (sourceSecondaryLoss_add_encodingReserve_le _).trans
    (ENNReal.div_le_div (signer_expectedClassBudget adversary q hsmall hbound) le_rfl)

end XmssSecurity.TargetSum.Modes
