import Xmss.Proof.TargetSum.EUFCMA.SecondLane
import Xmss.Proof.Generic.Direct.DecidingFirstLaneBridge
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability
/-! Standard forgeries satisfy the existing deciding classification while retaining
standard freshness in the second lane. Encoding and structural queries share the
same direct-query budget. -/

open OracleComp OracleSpec ENNReal

open Xmss.Generic

namespace Xmss.TargetSum.EUFCMA
open Xmss.EUFCMA

open Deciding

theorem forgeAdvantage_withForgedEncodingQuery (adversary : Adversary) :
    forgeAdvantage precomputedScheme (Direct.withForgedEncodingQuery adversary) =
      forgeAdvantage precomputedScheme adversary := by
  rw [forgeAdvantage_eq_detailedGameWithCache, forgeAdvantage_eq_detailedGameWithCache,
    Direct.detailedGameWithCache_withForgedEncodingQuery]

end Xmss.TargetSum.EUFCMA
