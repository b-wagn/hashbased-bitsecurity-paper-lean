import Xmss.Proof.TargetSum.Direct.RevealedEncodingPrefix
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Append one deciding probe for an independently supplied encoding to the
limited adversary prefix. The complete public experiment uses at most q + 1 hazards. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Deciding

open CappedExecution FirstLaneOracleSimulation

noncomputable def appendLimitedEncodingPrefixProbe (base : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (encoding : Encoding)
    (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex) :
    LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex :=
  match result.1.1 with
  | none => result
  | some completed =>
      (result.1, result.2 ++ (Deciding.decidingProbeResult base completed.1.epoch
        (Deciding.signedEncoding completed.2.causalState.cache key.secretKey.parameter
          completed.2.attackerTrace.toSigningLog completed.1.epoch)
        encoding completed.1.signature.chainValue).2)

theorem appendLimitedEncodingPrefixProbe_preserves_hit (base : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (encoding : Encoding)
    (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hhit : FirstLaneOracleSimulation.CombinedHit base result.2) :
    FirstLaneOracleSimulation.CombinedHit base (appendLimitedEncodingPrefixProbe base key encoding result).2 := by
  unfold appendLimitedEncodingPrefixProbe
  split
  · exact hhit
  · exact FirstLaneOracleSimulation.CombinedHit.append_of_prefix base _ _ hhit

end Xmss.TargetSum.Deciding
