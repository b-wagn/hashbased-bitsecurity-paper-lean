import XmssSecurity.Proof.Checksum.CappedChain.ChainEventDecomposition
import XmssSecurity.Proof.Checksum.WinningEventReduction

open OracleComp OracleSpec

namespace XmssSecurity.Checksum.CappedChain

noncomputable def WinningOutcomeChainValueHasKeygenOrigin
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) (chain : ChainIndex) : Prop :=
  WinningOutcomeBadEventOccurs finalCache outcome (.chain chain) ∧
    OutcomeChainValueHasKeygenOrigin keygenCache finalCache secretKey outcome chain

end XmssSecurity.Checksum.CappedChain
