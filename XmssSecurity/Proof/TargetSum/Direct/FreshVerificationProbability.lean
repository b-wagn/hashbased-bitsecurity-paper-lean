import XmssSecurity.Proof.TargetSum.Direct.VerificationAcceptance
import XmssSecurity.Proof.TargetSum.Direct.DecidingAcceptedProbe
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Preserve the fresh-encoding acceptance factor through the actual verification
phase and the instrumented source finisher, including events selected by a prefix. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum

namespace Deciding

open Direct Generic.CappedChain

def SourcePrefixForgedEncodingFresh
    (result : Generic.CappedChain.ProgrammedGlobalChainKeygenView × (Generic.Forgery × Generic.CappedChain.SourceExactTracedState)) : Prop :=
  result.2.2.1.1.1 (Generic.Direct.forgeryEncodingInput result.1.publicKey result.2.1) = none

end Deciding
end XmssSecurity.TargetSum
