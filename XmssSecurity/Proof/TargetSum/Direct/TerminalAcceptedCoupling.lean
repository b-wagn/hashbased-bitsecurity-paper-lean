import XmssSecurity.Proof.TargetSum.Direct.TerminalPrunedCoupling

/-! The terminal cut preserves the accepted-prefix cancellation coupling: every
cached first-lane witness still produces a hit, and a cut performs no deciding probe. -/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

noncomputable def publicTerminalPrefixExecution (limit : Nat) (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) (edgeHigh : GlobalChainEdgeIndex → Digest) :
    OracleComp GlobalFirstLaneWorld LimitedPrefixResult :=
  terminalPrunedFirstLanePrefix limit key edgeHigh (adversary.main key.publicKey)
    (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩

end XmssSecurity.TargetSum.Deciding
