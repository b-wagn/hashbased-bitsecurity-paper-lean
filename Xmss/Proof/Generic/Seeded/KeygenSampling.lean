import Xmss.Proof.Generic.Seeded.KeygenExpansion

open OracleComp OracleSpec

namespace Xmss.Generic.Seeded

variable [Code]

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

omit [Code] in
theorem evalDist_samplePublicParameter : 𝒟[Keygen.samplePublicParameter] = 𝒟[$ᵗ Digest] := by
  unfold Keygen.samplePublicParameter
  rw [evalDist_uniformSample]

theorem evalDist_sampleSecret : 𝒟[Keygen.sampleSecret] = 𝒟[$ᵗ ChainSecrets] := by
  apply evalDist_ext
  intro secret
  unfold Keygen.sampleSecret
  simp only [probOutput_uniformSample]

end Xmss.Generic.Seeded
