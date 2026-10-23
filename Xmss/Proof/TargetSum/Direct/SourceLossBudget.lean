import Xmss.Proof.TargetSum.Direct.SourceSignerQueries
import Xmss.Proof.TargetSum.Direct.ReferenceSeedQueries
import Xmss.Proof.TargetSum.Direct.CollisionLoss
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! The source-side losses share one budget. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Direct

noncomputable def sourceSecondaryLoss (adversary : Adversary) : ℝ≥0∞ :=
  prehitRate * Direct.expectedDirectEncodingQueries adversary +
    (Direct.expectedDirectStructuralQueries adversary / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
      (Direct.expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary) *
        (TargetSum.acceptanceProbability * ((48 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)))) +
    expectedDirectSeedQueries adversary / ((2 ^ 256 : Nat) : ℝ≥0∞)

end Xmss.TargetSum.Direct
