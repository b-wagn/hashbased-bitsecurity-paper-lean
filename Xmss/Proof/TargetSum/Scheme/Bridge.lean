import Xmss.Proof.Generic.Scheme.Bridge
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! The statement's scheme `xmssTargetSum` is the copy `Generic.xmss` the proofs work with, for the
target-sum code. -/

open Xmss.Generic

namespace Xmss.TargetSum

theorem xmssTargetSum_eq : xmssTargetSum = Generic.xmss := xmss_eq

end Xmss.TargetSum
