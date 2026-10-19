import XmssSecurity.Proof.TargetSum.Direct.SourceSignerQueries
import XmssSecurity.Proof.TargetSum.Direct.ReferenceSeedQueries
import XmssSecurity.Proof.TargetSum.Direct.CollisionLoss
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The source-side losses share one budget. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Direct

noncomputable def sourceSecondaryLoss (adversary : Adversary) : ℝ≥0∞ :=
  prehitRate * Direct.expectedDirectEncodingQueries adversary +
    (Direct.expectedDirectStructuralQueries adversary / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
      (Direct.expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary) *
        (TargetSum.acceptanceProbability * ((48 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)))) +
    expectedDirectSeedQueries adversary / ((2 ^ 256 : Nat) : ℝ≥0∞)

end XmssSecurity.TargetSum.Direct
