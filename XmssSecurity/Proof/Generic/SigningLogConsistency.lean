import XmssSecurity.Proof.Generic.OutcomeClassification

open OracleSpec

namespace XmssSecurity.Generic

variable [Code]

def SigningLogConsistent (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) : Prop :=
  ∀ request signature, SigningTranscript.Returned log request signature →
    ∃ encoding,
      Concrete.CacheView.decodedEncoding cache secretKey.parameter request.epoch
          (request.message, signature.randomness) = some encoding ∧
      signature = Concrete.CacheReplay.signWithEncoding cache secretKey
        request.epoch signature.randomness encoding

end XmssSecurity.Generic
