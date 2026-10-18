import XmssSecurity.Proof.TargetSum.Direct.LimitedAcceptedProbe

/-! Transfer accepted source-prefix events to the limited public experiment and its
expected collision bound, using only the source's semantic weighted query budget. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

end XmssSecurity.TargetSum.Deciding
