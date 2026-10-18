import XmssSecurity.Proof.TargetSum.Direct.SourceBudgetExhaustion
import XmssSecurity.Proof.TargetSum.Direct.MixedFirstLane

/-! At an exhausted budget, a cache without an accepted encoding cannot produce
a cached first-lane witness. Actual verification retains its fresh acceptance factor. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open Concrete CappedChain Direct

end XmssSecurity.TargetSum.Deciding
