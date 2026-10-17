import XmssSecurity.Proof.Checksum.GlobalBadEvent
import XmssSecurity.Proof.Checksum.CappedChain.ChainEventDecomposition

open OracleComp OracleSpec

namespace XmssSecurity.Checksum

def GlobalWinningChainValueRevealed
    (cache : QueryCache HashSpec) (outcome : GameOutcome) : Prop :=
  ∃ chain, WinningOutcomeBadEventOccurs cache outcome (.chain chain) ∧
    CappedChain.OutcomeChainValueRevealed cache outcome chain

end XmssSecurity.Checksum

