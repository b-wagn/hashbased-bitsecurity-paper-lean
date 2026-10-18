import XmssSecurity.Proof.TargetSum.Direct.TerminalPrunedPrefix

/-! Once the terminal-pruned prefix exhausts its public budget, its remaining
execution emits no further monitor actions. Signing and direct hashing both stop. -/

open OracleComp OracleSpec
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.FirstLaneOracleSimulation

end XmssSecurity.TargetSum.FirstLaneOracleSimulation

namespace XmssSecurity.TargetSum.CappedChain

open FirstLaneOracleSimulation

end XmssSecurity.TargetSum.CappedChain
