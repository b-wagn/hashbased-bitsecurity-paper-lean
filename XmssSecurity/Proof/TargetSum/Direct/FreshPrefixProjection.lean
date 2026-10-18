import XmssSecurity.Proof.TargetSum.Direct.DecidingSecondLaneFresh
import XmssSecurity.Proof.TargetSum.Direct.FreshVerificationProbability
import XmssSecurity.Proof.TargetSum.Direct.LimitedAcceptanceCancellation

/-! Freshness is the same event in the standard reference prefix and the traced
source prefix. Both lanes can therefore retain one common fresh-encoding probability. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open CappedChain Direct

end XmssSecurity.TargetSum.Deciding
