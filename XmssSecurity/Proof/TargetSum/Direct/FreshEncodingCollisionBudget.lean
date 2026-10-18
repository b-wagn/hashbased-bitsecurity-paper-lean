import XmssSecurity.Proof.TargetSum.Direct.FreshEncodingCollision
import XmssSecurity.Proof.TargetSum.Direct.SourceSignerQueries

/-! Average fresh encoding collisions over the actual reference prefix. The signed
target's acceptance is charged to source encoding queries and signer hashes. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open Concrete Direct

end XmssSecurity.TargetSum.Deciding
