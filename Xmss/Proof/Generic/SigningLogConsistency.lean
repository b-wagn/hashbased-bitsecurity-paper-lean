import Xmss.Proof.Generic.OutcomeClassification

open OracleSpec

namespace Xmss.Generic

variable [Code]

def SigningLogConsistent (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) : Prop :=
  ∀ request signature, SigningTranscript.Returned log request signature →
    ∃ encoding,
      CacheView.decodedEncoding cache secretKey.parameter request.epoch
          (request.message, signature.randomness) = some encoding ∧
      signature = CacheReplay.signWithEncoding cache secretKey
        request.epoch signature.randomness encoding

end Xmss.Generic
