import XmssSecurity.Proof.TargetSum.GlobalBadEvent
import XmssSecurity.Proof.TargetSum.CappedChain.ChainEventDecomposition

open OracleComp OracleSpec

namespace XmssSecurity.TargetSum

def GlobalWinningChainValueRevealed
    (cache : QueryCache HashSpec) (outcome : GameOutcome) : Prop :=
  ∃ chain, WinningOutcomeBadEventOccurs cache outcome (.chain chain) ∧
    CappedChain.OutcomeChainValueRevealed cache outcome chain

end XmssSecurity.TargetSum

