import Xmss.Proof.TargetSum.Direct.TerminalPrunedPrefix
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! The terminal cut preserves the accepted-prefix cancellation coupling: every
cached first-lane witness still produces a hit, and a cut performs no deciding probe. -/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Deciding

open CappedExecution FirstLaneOracleSimulation

noncomputable def publicTerminalPrefixExecution (limit : Nat) (adversary : Adversary)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) :
    OracleComp CappedExecution.GlobalFirstLaneWorld LimitedPrefixResult :=
  terminalPrunedFirstLanePrefix limit key (adversary.main key.publicKey)
    (CappedExecution.GlobalDirectTracedState.initial (CappedExecution.globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩

end Xmss.TargetSum.Deciding
