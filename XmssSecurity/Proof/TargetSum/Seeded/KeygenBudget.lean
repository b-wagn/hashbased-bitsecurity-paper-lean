import XmssSecurity.Proof.TargetSum.Seeded.BudgetTransfer

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

attribute [local irreducible] sampleMasterSeed deriveChainSecrets gameAfterSecrets derivationCache drawChainOutputs

end XmssSecurity.TargetSum.Seeded
