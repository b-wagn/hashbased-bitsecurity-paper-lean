import XmssSecurity.Proof.Checksum.SigningCacheTrace

namespace XmssSecurity.Checksum

def SigningCacheTrace.HasEncodingInputPrehit
    (trace : SigningCacheTrace) (secretKey : SecretKey) : Prop :=
  ∃ entry ∈ trace, entry.EncodingInputPrehit secretKey

end XmssSecurity.Checksum
