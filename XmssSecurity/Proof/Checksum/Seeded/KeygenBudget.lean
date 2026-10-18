import XmssSecurity.Proof.Checksum.Seeded.BudgetTransfer

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Checksum.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

attribute [local irreducible] sampleMasterSeed deriveChainSecrets gameAfterSecrets derivationCache drawChainOutputs

end XmssSecurity.Checksum.Seeded
