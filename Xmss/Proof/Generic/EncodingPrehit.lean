import Xmss.Proof.Generic.SigningCacheTrace

namespace Xmss.Generic

variable [Code]

def SigningCacheTrace.HasEncodingInputPrehit
    (trace : SigningCacheTrace) (secretKey : SecretKey) : Prop :=
  ∃ entry ∈ trace, entry.EncodingInputPrehit secretKey

end Xmss.Generic
