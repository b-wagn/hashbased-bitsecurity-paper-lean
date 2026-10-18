import XmssSecurity.Proof.Generic.Seeded.KeygenExpansion

open OracleComp OracleSpec

namespace XmssSecurity.Generic.Seeded

variable [Code]

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev ChainSecrets := LeafIndex → ChainIndex → Digest

def chainOutputHalves : ChainOutputs ≃ (ChainSecrets × ChainSecrets) where
  toFun outputs := (fun leafIndex chain => (Rom.hashOutputEquivDigestPair (outputs leafIndex chain)).1,
    outputSecrets outputs)
  invFun halves := fun leafIndex chain =>
    Rom.hashOutputEquivDigestPair.symm (halves.1 leafIndex chain, halves.2 leafIndex chain)
  left_inv outputs := by
    funext leafIndex chain
    exact Rom.hashOutputEquivDigestPair.symm_apply_apply (outputs leafIndex chain)
  right_inv halves := by
    apply Prod.ext <;> funext leafIndex chain
    · exact congrArg Prod.fst (Rom.hashOutputEquivDigestPair.apply_symm_apply
        (halves.1 leafIndex chain, halves.2 leafIndex chain))
    · exact congrArg Prod.snd (Rom.hashOutputEquivDigestPair.apply_symm_apply
        (halves.1 leafIndex chain, halves.2 leafIndex chain))

theorem outputSecrets_from_halves (high low : ChainSecrets) :
    outputSecrets (chainOutputHalves.symm (high, low)) = low :=
  congrArg Prod.snd (chainOutputHalves.apply_symm_apply (high, low))

theorem truncate_from_halves (high low : Digest) :
    truncateHash (Rom.hashOutputEquivDigestPair.symm (high, low)) = low :=
  congrArg Prod.snd (Rom.hashOutputEquivDigestPair.apply_symm_apply (high, low))

theorem evalDist_chainOutputs_from_halves :
    𝒟[$ᵗ ChainOutputs] = 𝒟[do
      let low ← $ᵗ ChainSecrets
      let high ← $ᵗ ChainSecrets
      pure (chainOutputHalves.symm (high, low))] := by
  calc
    _ = 𝒟[chainOutputHalves.symm <$> ($ᵗ (ChainSecrets × ChainSecrets))] :=
      (evalDist_map_bijective_uniform_cross (α := ChainSecrets × ChainSecrets) (β := ChainOutputs)
        chainOutputHalves.symm chainOutputHalves.symm.bijective).symm
    _ = 𝒟[chainOutputHalves.symm <$> (do
        let high ← $ᵗ ChainSecrets
        let low ← $ᵗ ChainSecrets
        pure (high, low))] := by
      rw [evalDist_map, evalDist_map, evalDist_independent_uniform_pair]
    _ = _ := by
      simp only [map_bind, map_pure]
      exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _

theorem evalDist_samplePublicParameter : 𝒟[Concrete.samplePublicParameter] = 𝒟[$ᵗ Digest] := by
  unfold Concrete.samplePublicParameter
  rw [evalDist_uniformSample, evalDist_uniformSample]
  rfl

theorem evalDist_sampleSecret : 𝒟[Concrete.sampleSecret] = 𝒟[$ᵗ ChainSecrets] := by
  apply evalDist_ext
  intro secret
  unfold Concrete.sampleSecret
  simp only [probOutput_uniformSample]

end XmssSecurity.Generic.Seeded
