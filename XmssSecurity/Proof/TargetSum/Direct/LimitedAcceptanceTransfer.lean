import XmssSecurity.Proof.TargetSum.Direct.SourcePrefixAcceptance

/-! Accepted ideal prefixes come from an accepted source cache or a recorded collision.
This transfers an event probability without identifying post-collision costs. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum

namespace Deciding

open CappedChain FirstLaneOracleSimulation

end Deciding
end XmssSecurity.TargetSum
