import XmssSecurity.Proof.TargetSum.Direct.VerificationAcceptance
import XmssSecurity.Proof.TargetSum.Direct.DecidingAcceptedProbe

/-! Preserve the fresh-encoding acceptance factor through the actual verification
phase and the instrumented source finisher, including events selected by a prefix. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum

namespace Deciding

open Direct CappedChain

theorem SourceWinningDecidingFirstLaneEvent.verified
    (key : ProgrammedGlobalChainKeygenView) (result : (Forgery × Bool) × SourceExactTracedState)
    (hevent : SourceWinningDecidingFirstLaneEvent (key, result)) : result.1.2 = true := by
  have hwin : (cappedBothEncodingProjection (sourceGlobalExactProgramResult (key, result))).1.won = true := by
    rcases hevent with hencoding | hchain
    · exact hencoding.1.1
    · exact hchain.1
  exact (GameOutcome.won_eq_true_iff _).mp hwin |>.2.2

def SourcePrefixForgedEncodingFresh
    (result : ProgrammedGlobalChainKeygenView × (Forgery × SourceExactTracedState)) : Prop :=
  result.2.2.1.1.1 (forgeryEncodingInput result.1.publicKey result.2.1) = none

end Deciding
end XmssSecurity.TargetSum
