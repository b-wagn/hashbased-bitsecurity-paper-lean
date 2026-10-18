import XmssSecurity.Proof.Checksum.CappedExactFirstLaneBound
import XmssSecurity.Proof.Checksum.Direct.Basic

/-!
# The first lane under a direct query bound

A version of `CappedExactFirstLaneBound` in which the adversary is charged only for its own
(direct) hash queries, bounded syntactically by `Direct.IsDirectQueryBound adversary D`, while the
final verification is charged `Direct.verifierQueryBound` hash calls.
-/

open OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.Checksum.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

end XmssSecurity.Checksum.CappedChain
