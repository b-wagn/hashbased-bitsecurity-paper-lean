import XmssSecurity.Proof.TargetSum.SigningCacheTrace

namespace XmssSecurity.TargetSum

def SigningCacheTrace.HasEncodingInputPrehit
    (trace : SigningCacheTrace) (secretKey : SecretKey) : Prop :=
  ∃ entry ∈ trace, entry.EncodingInputPrehit secretKey

end XmssSecurity.TargetSum
