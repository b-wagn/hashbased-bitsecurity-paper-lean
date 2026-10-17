import XmssSecurity.Proof.TargetSum.CappedChain.ChainEventDecomposition
import XmssSecurity.Proof.TargetSum.WinningEventReduction

open OracleComp OracleSpec

namespace XmssSecurity.TargetSum.CappedChain

noncomputable def WinningOutcomeChainValueHasKeygenOrigin
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) (chain : ChainIndex) : Prop :=
  WinningOutcomeBadEventOccurs finalCache outcome (.chain chain) ∧
    OutcomeChainValueHasKeygenOrigin keygenCache finalCache secretKey outcome chain

end XmssSecurity.TargetSum.CappedChain
