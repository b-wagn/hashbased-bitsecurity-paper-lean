import XmssSecurity.Proof.TargetSum.Direct.EncodingQueries

/-! The prehit loss charged only to direct encoding queries. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum
namespace Direct

def IsEncodingQueryBound (adversary : Adversary) (E : ℕ) : Prop :=
  ∀ publicKey, (adversary.main publicKey).IsQueryBoundP
    (IsDirectEncodingQuery publicKey.parameter) E

end Direct

end XmssSecurity.TargetSum
