import Xmss.Proof.TargetSum.Direct.LimitedPrefixCoupling
import Xmss.Proof.TargetSum.Direct.LimitedPrefixSupport
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! A successful limited prefix incurs the deciding probe only when its forged encoding
is accepted. Aborted prefixes retain any collision already recorded in their trace. -/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Deciding

open CappedExecution FirstLaneOracleSimulation

abbrev LimitedPrefixResult := Option (Forgery × CappedExecution.GlobalDirectTracedState) × EncodingBudgetCounters

noncomputable def appendLimitedAcceptedPrefixProbe (base : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex) :
    LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex :=
  match result.1.1 with
  | none => result
  | some completed =>
      if (Deciding.forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1).isSome then
        (result.1, result.2 ++ (Deciding.prefixProbeResult base completed.2.causalState.cache key.secretKey.parameter
          completed.2.attackerTrace.toSigningLog completed.1).2)
      else result

theorem appendLimitedAcceptedPrefixProbe_preserves_hit (base : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hhit : FirstLaneOracleSimulation.CombinedHit base result.2) :
    FirstLaneOracleSimulation.CombinedHit base (appendLimitedAcceptedPrefixProbe base key result).2 := by
  unfold appendLimitedAcceptedPrefixProbe
  split
  · exact hhit
  · split
    · exact FirstLaneOracleSimulation.CombinedHit.append_of_prefix base _ _ hhit
    · exact hhit

def LimitedPrefixForgedEncodingAccepted (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex) : Prop :=
  ∃ completed, result.1.1 = some completed ∧
    (Deciding.forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1).isSome

noncomputable instance (key : CappedExecution.ProgrammedGlobalChainKeygenView) :
    DecidablePred (LimitedPrefixForgedEncodingAccepted key) := Classical.decPred _

theorem hazardCount_appendLimitedAcceptedPrefixProbe (base : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex) :
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

end Xmss.TargetSum.Deciding
