import XmssSecurity.Proof.TargetSum.Modes.SignerSourceBudget
import XmssSecurity.Proof.TargetSum.Direct.CollisionLoss

/-! The signer-counted budget bounds the direct hash queries on every branch of the reference
execution, so the prehit loss is at most `prehitRate` per expected direct encoding query. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open Seeded Direct

theorem signer_prehit_le (adversary : Security.StatementAdversary) (q : Nat)
    (hq : q + 1 ≤ 2 ^ 127)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q) :
    Pr[WinningEncodingPrehitOccurs |
        cappedDetailedGameWithEncodingTrace (memoAdversary (Security.embed adversary))] ≤
      prehitRate * expectedDirectEncodingQueries (memoAdversary (Security.embed adversary)) := by
  have hsmall : q < 2 ^ 256 := by omega
  apply winningEncodingPrehit_probability_le_prehitRate_of_phaseBudget _ q hq
  intro keyResult hkey result hresult
  have h := signer_referencePhaseCounts_unlogged_bound adversary q hsmall hbound keyResult hkey
    result hresult
  omega

end XmssSecurity.TargetSum.Modes
