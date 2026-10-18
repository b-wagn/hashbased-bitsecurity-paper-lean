import XmssSecurity.Proof.TargetSum.Scheme.Xmss
import XmssSecurity.Statement.Security.EUFCMA
import XmssSecurity.Proof.Common.EUFCMA.Modes
import XmssSecurity.Proof.TargetSum.Modes.Exact
import XmssSecurity.Proof.Common.Legacy.PerModeNotionsEUFCMA

/-! A basis for the initial uniform standard-unforgeability conjecture:
127-bit direct-query security and an attack on 128 bits with everything charged. -/

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open SUFCMA hiding experiment game gameCounted notion securityGame

end XmssSecurity.TargetSum.EUFCMA
