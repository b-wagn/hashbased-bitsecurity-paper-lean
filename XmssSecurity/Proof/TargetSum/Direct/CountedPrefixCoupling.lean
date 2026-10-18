import XmssSecurity.Proof.TargetSum.Direct.CountedSourceCoupling

/-! Couple an entire adversary prefix using the supported source budget. The good
branch retains the actual direct count instead of replacing it by the maximum budget. -/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.CappedChain

open Seeded FirstLaneOracleSimulation

end XmssSecurity.TargetSum.CappedChain
