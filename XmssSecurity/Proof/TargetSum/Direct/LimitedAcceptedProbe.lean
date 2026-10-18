import XmssSecurity.Proof.TargetSum.Direct.LimitedPrefixCoupling
import XmssSecurity.Proof.TargetSum.Direct.LimitedPrefixSupport

/-! A successful limited prefix incurs the deciding probe only when its forged encoding
is accepted. Aborted prefixes retain any collision already recorded in their trace. -/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

abbrev LimitedPrefixResult := Option (Forgery × GlobalHighDirectTracedState) × EncodingBudgetCounters

noncomputable def appendLimitedAcceptedPrefixProbe (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView)
    (result : LimitedPrefixResult × ActionTrace GlobalChainValueIndex) :
    LimitedPrefixResult × ActionTrace GlobalChainValueIndex :=
  match result.1.1 with
  | none => result
  | some completed =>
      if (forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1).isSome then
        (result.1, result.2 ++ (prefixProbeResult base completed.2.causalState.cache key.secretKey.parameter
          completed.2.attackerTrace.toSigningLog completed.1).2)
      else result

theorem appendLimitedAcceptedPrefixProbe_preserves_hit (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView) (result : LimitedPrefixResult × ActionTrace GlobalChainValueIndex)
    (hhit : CombinedHit base result.2) :
    CombinedHit base (appendLimitedAcceptedPrefixProbe base key result).2 := by
  unfold appendLimitedAcceptedPrefixProbe
  split
  · exact hhit
  · split
    · exact CombinedHit.append_of_prefix base _ _ hhit
    · exact hhit

def LimitedPrefixForgedEncodingAccepted (key : ProgrammedGlobalChainKeygenView)
    (result : LimitedPrefixResult × ActionTrace GlobalChainValueIndex) : Prop :=
  ∃ completed, result.1.1 = some completed ∧
    (forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1).isSome

noncomputable instance (key : ProgrammedGlobalChainKeygenView) :
    DecidablePred (LimitedPrefixForgedEncodingAccepted key) := Classical.decPred _

theorem hazardCount_appendLimitedAcceptedPrefixProbe (base : GlobalChainValueIndex → Digest)
    (key : ProgrammedGlobalChainKeygenView) (result : LimitedPrefixResult × ActionTrace GlobalChainValueIndex) :
    hazardCount (appendLimitedAcceptedPrefixProbe base key result).2 = hazardCount result.2 +
      if LimitedPrefixForgedEncodingAccepted key result then 1 else 0 := by
  classical
  rcases result with ⟨⟨completed, counters⟩, trace⟩
  cases completed with
  | none => simp [appendLimitedAcceptedPrefixProbe, LimitedPrefixForgedEncodingAccepted]
  | some completed =>
      by_cases h : (forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1).isSome
      all_goals simp [appendLimitedAcceptedPrefixProbe, LimitedPrefixForgedEncodingAccepted, h,
        hazardCount_append, prefixProbeResult, decidingProbeResult_hazardCount]

end XmssSecurity.TargetSum.Deciding
