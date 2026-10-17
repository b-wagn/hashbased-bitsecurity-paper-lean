import XmssSecurity.Proof.TargetSum.SigningCacheTrace

namespace XmssSecurity.TargetSum

def SigningCacheTrace.HasEncodingInputPrehitAt
    (trace : SigningCacheTrace) (secretKey : SecretKey)
    (targetLeafIndex : LeafIndex) : Prop :=
  ∃ entry ∈ trace,
    entry.request.epoch = targetLeafIndex ∧ entry.EncodingInputPrehit secretKey

def SigningCacheTrace.HasEncodingInputPrehit
    (trace : SigningCacheTrace) (secretKey : SecretKey) : Prop :=
  ∃ entry ∈ trace, entry.EncodingInputPrehit secretKey

end XmssSecurity.TargetSum
