import XmssSecurity.Proof.TargetSum.Direct.SourceSignerQueries
import XmssSecurity.Proof.TargetSum.Direct.ReferenceSeedQueries
import XmssSecurity.Proof.TargetSum.Direct.CollisionLoss

/-! The source-side losses share one budget. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Direct

noncomputable def sourceSecondaryLoss (adversary : Adversary) : ℝ≥0∞ :=
  prehitRate * expectedDirectEncodingQueries adversary +
    (expectedDirectStructuralQueries adversary / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
      (expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary) *
        (TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)))) +
    expectedDirectSeedQueries adversary / ((2 ^ 256 : Nat) : ℝ≥0∞)

end XmssSecurity.TargetSum.Direct
