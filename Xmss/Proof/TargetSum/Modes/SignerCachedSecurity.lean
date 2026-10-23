import Xmss.Proof.TargetSum.Modes.SignerClassBudget
import Xmss.Proof.TargetSum.Direct.SourceLossBudget
import Xmss.Proof.TargetSum.Modes.SignerSourceBudget
import Xmss.Proof.TargetSum.Direct.LimitedPrefixCoupling
import Xmss.Proof.TargetSum.Direct.LimitedAcceptedProbe
import Xmss.Proof.TargetSum.Direct.SourceEncodingReserve
import Xmss.Proof.TargetSum.Direct.CachedEncodingCost
import Xmss.Proof.TargetSum.Direct.SourcePrefixAcceptance
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! The signer-counted budget pays for the source-side secondary losses and the encoding
reserve. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Modes
open Xmss.Modes

open Seeded Direct Deciding

theorem signer_sourceSecondaryLoss_add_encodingReserve_le (adversary : AdversaryBridge.StatementAdversary)
    (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q) :
    sourceSecondaryLoss (Seeded.memoAdversary (AdversaryBridge.embed adversary)) +
      sourceEncodingReserve (Seeded.memoAdversary (AdversaryBridge.embed adversary)) /
        ((2 ^ digestBits : Nat) : ℝ≥0∞) ≤ (q : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) :=
  (sourceSecondaryLoss_add_encodingReserve_le _).trans
    (ENNReal.div_le_div (signer_expectedClassBudget adversary q hsmall hbound) le_rfl)

end Xmss.TargetSum.Modes
