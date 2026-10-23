import Xmss.Proof.Generic.CappedEncodingRejection

/-! The probability that a uniform digest decodes. -/

open OracleComp ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace Xmss.Generic.Code

variable [Code]

/-- The probability that a uniform digest decodes. -/
noncomputable def acceptanceProbability : ℝ≥0∞ :=
  (validDigests.card : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)

theorem probEvent_validDigest_uniform :
    Pr[ValidDigest | $ᵗ Digest] = acceptanceProbability := by
  rw [probEvent_uniformSample]
  change (validDigests.card : ℝ≥0∞) / Fintype.card Digest = _
  rw [card_bitVec]
  rfl

theorem acceptanceProbability_ne_top : acceptanceProbability ≠ ⊤ := by
  unfold acceptanceProbability
  exact ENNReal.div_ne_top (by finiteness) (by simp)

end Xmss.Generic.Code
