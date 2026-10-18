import XmssSecurity.Proof.Generic.Seeded.KeygenExpansion

open OracleComp OracleSpec

namespace XmssSecurity.Generic.Seeded

variable [Code]

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem evalDist_samplePublicParameter : 𝒟[Concrete.samplePublicParameter] = 𝒟[$ᵗ Digest] := by
  unfold Concrete.samplePublicParameter
  rw [evalDist_uniformSample]

theorem evalDist_sampleSecret : 𝒟[Concrete.sampleSecret] = 𝒟[$ᵗ ChainSecrets] := by
  apply evalDist_ext
  intro secret
  unfold Concrete.sampleSecret
  simp only [probOutput_uniformSample]

end XmssSecurity.Generic.Seeded
