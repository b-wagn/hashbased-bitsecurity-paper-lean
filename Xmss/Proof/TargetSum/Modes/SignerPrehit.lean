import Xmss.Proof.TargetSum.Modes.SignerSourceBudget
import Xmss.Proof.TargetSum.Direct.CollisionLoss
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! The signer-counted budget bounds the direct hash queries on every branch of the reference
execution, so the prehit loss is at most `prehitRate` per expected direct encoding query. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Modes
open Xmss.Modes

open Seeded Direct

theorem signer_prehit_le (adversary : AdversaryBridge.StatementAdversary) (q : Nat)
    (hq : q + 1 ≤ 2 ^ 127)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q) :
    Pr[WinningEncodingPrehitOccurs |
        cappedDetailedGameWithEncodingTrace (Seeded.memoAdversary (AdversaryBridge.embed adversary))] ≤
      prehitRate * Direct.expectedDirectEncodingQueries (Seeded.memoAdversary (AdversaryBridge.embed adversary)) := by
  have hsmall : q < 2 ^ 256 := by omega
  apply winningEncodingPrehit_probability_le_prehitRate_of_phaseBudget _ q hq
  intro keyResult hkey result hresult
  have h := signer_referencePhaseCounts_unlogged_bound adversary q hsmall hbound keyResult hkey
    result hresult
  omega

end Xmss.TargetSum.Modes
