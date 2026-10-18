import XmssSecurity.Proof.TargetSum.SignerSuccessBudget
import XmssSecurity.Proof.TargetSum.Seeded.KeygenExpansion

/-! Seed derivation and tree generation leave every encoding input fresh. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum

attribute [local irreducible] sampleMasterSeed

end XmssSecurity.TargetSum
