import Xmss.Proof.TargetSum.Direct.VerificationAcceptance
import Xmss.Proof.TargetSum.Direct.DecidingAcceptedProbe
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Preserve the fresh-encoding acceptance factor through the actual verification
phase and the instrumented source finisher, including events selected by a prefix. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum

namespace Deciding

open Direct CappedExecution

def SourcePrefixForgedEncodingFresh
    (result : CappedExecution.ProgrammedGlobalChainKeygenView × (Forgery × CappedExecution.SourceExactTracedState)) : Prop :=
  result.2.2.1.1.1 (Direct.forgeryEncodingInput result.1.publicKey result.2.1) = none

end Deciding
end Xmss.TargetSum
