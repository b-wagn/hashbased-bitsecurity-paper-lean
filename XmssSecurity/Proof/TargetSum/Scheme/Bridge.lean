import XmssSecurity.Proof.Generic.Scheme.Bridge
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The statement's scheme `xmssTargetSum` is the copy `Generic.xmss` the proofs work with, for the
target-sum code. -/

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum

theorem xmssTargetSum_eq : xmssTargetSum = Generic.xmss := xmss_eq

end XmssSecurity.TargetSum
