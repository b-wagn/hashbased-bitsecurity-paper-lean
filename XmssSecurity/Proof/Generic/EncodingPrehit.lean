import XmssSecurity.Proof.Generic.SigningCacheTrace

namespace XmssSecurity.Generic

variable [Code]

def SigningCacheTrace.HasEncodingInputPrehit
    (trace : SigningCacheTrace) (secretKey : SecretKey) : Prop :=
  ∃ entry ∈ trace, entry.EncodingInputPrehit secretKey

end XmssSecurity.Generic
