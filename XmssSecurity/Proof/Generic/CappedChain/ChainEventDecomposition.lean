import XmssSecurity.Proof.Generic.CappedLeafEventProbability
import XmssSecurity.Proof.Generic.CappedSuffixEventProbability
import XmssSecurity.Proof.Generic.ChainTargetInput

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Generic.CappedChain

variable [Code]

set_option maxRecDepth 100000

noncomputable def OutcomeChainValueRevealed (cache : QueryCache HashSpec)
    (outcome : GameOutcome) (chain : ChainIndex) : Prop :=
  outcome.verified = true ∧
    ∃ encoding,
      Concrete.CacheView.decodedEncoding cache outcome.secretKey.parameter
          outcome.forgery.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness) = some encoding ∧
      outcome.forgery.signature.chainValue chain =
        Wots.signChain
          (Concrete.CacheView.chainStep cache outcome.secretKey.parameter
            outcome.forgery.epoch chain)
          (encoding chain) (outcome.secretKey.chainStart outcome.forgery.epoch chain)

end XmssSecurity.Generic.CappedChain
