import Xmss.Proof.Generic.IdealStatement
import VCVio.OracleComp.Constructions.SampleableType

open OracleComp ENNReal

namespace Xmss.Generic.HiddenValue

variable [Code]

noncomputable local instance : SampleableType Digest :=
  SampleableType.ofFintype Digest

omit [Code] in
theorem card_digest : Fintype.card Digest = 2 ^ digestBits := by
  simp

omit [Code] in
theorem uniform_digest_point_probability (target : Digest) :
    Pr[= target | $ᵗ Digest] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [probOutput_uniformSample, card_digest]

end Xmss.Generic.HiddenValue
