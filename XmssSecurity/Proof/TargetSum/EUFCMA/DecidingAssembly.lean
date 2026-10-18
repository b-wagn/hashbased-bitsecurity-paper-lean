import XmssSecurity.Proof.TargetSum.EUFCMA.SecondLane
import XmssSecurity.Proof.Generic.Direct.DecidingFirstLaneBridge
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Standard forgeries satisfy the existing deciding classification while retaining
standard freshness in the second lane. Encoding and structural queries share the
same direct-query budget. -/

open OracleComp OracleSpec ENNReal

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Deciding

theorem forgeAdvantage_withForgedEncodingQuery (adversary : Adversary) :
    forgeAdvantage Concrete.scheme (Direct.withForgedEncodingQuery adversary) =
      forgeAdvantage Concrete.scheme adversary := by
  rw [forgeAdvantage_eq_detailedGameWithCache, forgeAdvantage_eq_detailedGameWithCache,
    Direct.detailedGameWithCache_withForgedEncodingQuery]

end XmssSecurity.TargetSum.EUFCMA
