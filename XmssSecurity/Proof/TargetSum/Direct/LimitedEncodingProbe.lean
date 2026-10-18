import XmssSecurity.Proof.TargetSum.Direct.RevealedEncodingPrefix
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Append one deciding probe for an independently supplied encoding to the
limited adversary prefix. The complete public experiment uses at most q + 1 hazards. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

noncomputable def appendLimitedEncodingPrefixProbe (base : Generic.CappedChain.GlobalChainValueIndex → Digest)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (encoding : Encoding)
    (result : LimitedPrefixResult × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex) :
    LimitedPrefixResult × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex :=
  match result.1.1 with
  | none => result
  | some completed =>
      (result.1, result.2 ++ (Generic.Deciding.decidingProbeResult base completed.1.epoch
        (Generic.Deciding.signedEncoding completed.2.causalState.cache key.secretKey.parameter
          completed.2.attackerTrace.toSigningLog completed.1.epoch)
        encoding completed.1.signature.chainValue).2)

theorem appendLimitedEncodingPrefixProbe_preserves_hit (base : Generic.CappedChain.GlobalChainValueIndex → Digest)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (encoding : Encoding)
    (result : LimitedPrefixResult × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hhit : Generic.FirstLaneOracleSimulation.CombinedHit base result.2) :
    Generic.FirstLaneOracleSimulation.CombinedHit base (appendLimitedEncodingPrefixProbe base key encoding result).2 := by
  unfold appendLimitedEncodingPrefixProbe
  split
  · exact hhit
  · exact Generic.FirstLaneOracleSimulation.CombinedHit.append_of_prefix base _ _ hhit

end XmssSecurity.TargetSum.Deciding
