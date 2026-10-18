import XmssSecurity.Proof.Generic.Scheme.Bridge
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The statement's scheme `xmssTargetSum` is the copy `Generic.xmss` the proofs work with, for the
target-sum code. -/

namespace XmssSecurity.TargetSum

theorem xmssTargetSum_eq : xmssTargetSum = Generic.xmss := Generic.xmss_eq

end XmssSecurity.TargetSum
