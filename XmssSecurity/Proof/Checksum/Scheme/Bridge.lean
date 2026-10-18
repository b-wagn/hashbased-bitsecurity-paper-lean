import XmssSecurity.Proof.Generic.Scheme.Bridge
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability

/-! The statement's scheme `xmssChecksum` is the copy `Generic.xmss` the proofs work with, for the
checksummed code. -/

open XmssSecurity.Generic

namespace XmssSecurity.Checksum

theorem xmssChecksum_eq : xmssChecksum = Generic.xmss := xmss_eq

end XmssSecurity.Checksum
