import XmssSecurity.Proof.TargetSum.Direct.TerminalPrunedPrefix

/-! Couple the source to the terminal-pruned public prefix. Besides the usual
agreement-or-hit cases, an early cut certifies that the source cannot have an accepted encoding. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.CappedChain

open Seeded FirstLaneOracleSimulation

end XmssSecurity.TargetSum.CappedChain
