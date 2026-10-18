import XmssSecurity.Proof.TargetSum.EUFCMA.SecondLane
import XmssSecurity.Proof.Generic.Direct.DecidingFirstLaneBridge
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Standard forgeries satisfy the existing deciding classification while retaining
standard freshness in the second lane. Encoding and structural queries share the
same direct-query budget. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Deciding

theorem forgeAdvantage_withForgedEncodingQuery (adversary : Generic.Adversary) :
    forgeAdvantage Generic.Concrete.scheme (Generic.Direct.withForgedEncodingQuery adversary) =
      forgeAdvantage Generic.Concrete.scheme adversary := by
  rw [forgeAdvantage_eq_detailedGameWithCache, forgeAdvantage_eq_detailedGameWithCache,
    Generic.Direct.detailedGameWithCache_withForgedEncodingQuery]

end XmssSecurity.TargetSum.EUFCMA
