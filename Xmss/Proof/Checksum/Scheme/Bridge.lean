import Xmss.Proof.Generic.Scheme.Bridge
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Checksum.EncodingProbability

/-! The statement's scheme `xmssChecksum` is the copy `Generic.xmss` the proofs work with, for the
checksummed code. -/

open Xmss.Generic

namespace Xmss.Checksum

theorem xmssChecksum_eq : xmssChecksum = Generic.xmss := xmss_eq

end Xmss.Checksum
