import XmssSecurity.Proof.TargetSum.Direct.LimitedPrefixCoupling
import XmssSecurity.Proof.TargetSum.Direct.LimitedPrefixSupport
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! A successful limited prefix incurs the deciding probe only when its forged encoding
is accepted. Aborted prefixes retain any collision already recorded in their trace. -/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

abbrev LimitedPrefixResult := Option (Forgery × CappedChain.GlobalHighDirectTracedState) × EncodingBudgetCounters

noncomputable def appendLimitedAcceptedPrefixProbe (base : CappedChain.GlobalChainValueIndex → Digest)
    (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex) :
    LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex :=
  match result.1.1 with
  | none => result
  | some completed =>
      if (Deciding.forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1).isSome then
        (result.1, result.2 ++ (Deciding.prefixProbeResult base completed.2.causalState.cache key.secretKey.parameter
          completed.2.attackerTrace.toSigningLog completed.1).2)
      else result

theorem appendLimitedAcceptedPrefixProbe_preserves_hit (base : CappedChain.GlobalChainValueIndex → Digest)
    (key : CappedChain.ProgrammedGlobalChainKeygenView) (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hhit : FirstLaneOracleSimulation.CombinedHit base result.2) :
    FirstLaneOracleSimulation.CombinedHit base (appendLimitedAcceptedPrefixProbe base key result).2 := by
  unfold appendLimitedAcceptedPrefixProbe
  split
  · exact hhit
  · split
    · exact FirstLaneOracleSimulation.CombinedHit.append_of_prefix base _ _ hhit
    · exact hhit

def LimitedPrefixForgedEncodingAccepted (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex) : Prop :=
  ∃ completed, result.1.1 = some completed ∧
    (Deciding.forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1).isSome

noncomputable instance (key : CappedChain.ProgrammedGlobalChainKeygenView) :
    DecidablePred (LimitedPrefixForgedEncodingAccepted key) := Classical.decPred _

theorem hazardCount_appendLimitedAcceptedPrefixProbe (base : CappedChain.GlobalChainValueIndex → Digest)
    (key : CappedChain.ProgrammedGlobalChainKeygenView) (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex) :
    FirstLaneOracleSimulation.hazardCount (appendLimitedAcceptedPrefixProbe base key result).2 = FirstLaneOracleSimulation.hazardCount result.2 +
      if LimitedPrefixForgedEncodingAccepted key result then 1 else 0 := by
  classical
  rcases result with ⟨⟨completed, counters⟩, trace⟩
  cases completed with
  | none => simp [appendLimitedAcceptedPrefixProbe, LimitedPrefixForgedEncodingAccepted]
  | some completed =>
      by_cases h : (Deciding.forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1).isSome
      all_goals simp [appendLimitedAcceptedPrefixProbe, LimitedPrefixForgedEncodingAccepted, h,
        FirstLaneOracleSimulation.hazardCount_append, Deciding.prefixProbeResult, Deciding.decidingProbeResult_hazardCount]

end XmssSecurity.TargetSum.Deciding
