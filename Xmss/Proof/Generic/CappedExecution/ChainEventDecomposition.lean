import Xmss.Proof.Generic.CappedLeafEventProbability
import Xmss.Proof.Generic.CappedSuffixEventProbability
import Xmss.Proof.Generic.ChainTargetInput

open OracleComp OracleSpec ENNReal

namespace Xmss.Generic.CappedExecution

variable [Code]

set_option maxRecDepth 100000

noncomputable def OutcomeChainValueRevealed (cache : QueryCache HashSpec)
    (outcome : GameOutcome) (chain : ChainIndex) : Prop :=
  outcome.verified = true ∧
    ∃ encoding,
      CacheView.decodedEncoding cache outcome.secretKey.parameter
          outcome.forgery.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness) = some encoding ∧
      outcome.forgery.signature.chainValue chain =
        Wots.signChain
          (CacheView.chainStep cache outcome.secretKey.parameter
            outcome.forgery.epoch chain)
          (encoding chain) (outcome.secretKey.chainStart outcome.forgery.epoch chain)

end Xmss.Generic.CappedExecution
