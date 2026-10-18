import XmssSecurity.Proof.TargetSum.Direct.LimitedEncodingProbe

/-! Bound fresh revealed deciding values by conditioning the final hash on
acceptance and applying the supplied-encoding prefix probe bound. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

end XmssSecurity.TargetSum.Deciding
