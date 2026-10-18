import XmssSecurity.Proof.TargetSum.CappedLeafEventProbability
import XmssSecurity.Proof.TargetSum.CappedSuffixEventProbability
import XmssSecurity.Proof.TargetSum.ChainTargetInput

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.CappedChain

set_option maxRecDepth 100000

noncomputable def OutcomeChainValueRevealed (cache : QueryCache HashSpec)
    (outcome : GameOutcome) (chain : ChainIndex) : Prop :=
  outcome.verified = true ∧
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash cache outcome.secretKey.parameter
          outcome.forgery.epoch
          (outcome.forgery.message, outcome.forgery.signature.randomness)) = some encoding ∧
      outcome.forgery.signature.chainValue chain =
        Wots.signChain
          (Concrete.CacheView.chainStep cache outcome.secretKey.parameter
            outcome.forgery.epoch chain)
          (encoding chain) (outcome.secretKey.chainStart outcome.forgery.epoch chain)

end XmssSecurity.TargetSum.CappedChain
