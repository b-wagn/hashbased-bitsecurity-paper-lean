import XmssSecurity.Proof.TargetSum.Direct.TerminalPrunedPrefix
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The terminal cut preserves the accepted-prefix cancellation coupling: every
cached first-lane witness still produces a hit, and a cut performs no deciding probe. -/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

noncomputable def publicTerminalPrefixExecution (limit : Nat) (adversary : Adversary)
    (key : CappedChain.ProgrammedGlobalChainKeygenView) :
    OracleComp CappedChain.GlobalFirstLaneWorld LimitedPrefixResult :=
  terminalPrunedFirstLanePrefix limit key (adversary.main key.publicKey)
    (CappedChain.GlobalHighDirectTracedState.initial (CappedChain.globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩

end XmssSecurity.TargetSum.Deciding
