import XmssSecurity.Proof.Generic.Scheme.Bridge
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability

/-! The statement's scheme `xmssChecksum` is the copy `Generic.xmss` the proofs work with, for the
checksummed code. -/

namespace XmssSecurity.Checksum

theorem xmssChecksum_eq : xmssChecksum = Generic.xmss := Generic.xmss_eq

end XmssSecurity.Checksum
