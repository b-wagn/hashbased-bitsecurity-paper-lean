import Xmss.Proof.Generic.HashInputLemmas
import Xmss.Proof.Generic.StatementLemmas

open OracleComp OracleSpec

namespace Xmss.Generic

variable [Code]

/-- Map a leaf input to the honest leaf input fixed by key generation at the same leaf index. -/
noncomputable def keygenLeafTargetInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (input : HashInput) : HashInput :=
  if h : ∃ leafIndex endpoints,
      input = CacheView.leafInput secretKey.parameter leafIndex endpoints then
    CacheView.leafInput secretKey.parameter h.choose
      (CacheReplay.oneTimePublicKey cache secretKey.parameter
        secretKey.chainStart h.choose)
  else input

@[simp]
theorem keygenLeafTargetInput_leafInput (secretKey : SecretKey)
    (cache : QueryCache HashSpec) (leafIndex : LeafIndex) (endpoints : ChainIndex → Digest) :
    keygenLeafTargetInput secretKey cache
      (CacheView.leafInput secretKey.parameter leafIndex endpoints) =
      CacheView.leafInput secretKey.parameter leafIndex
        (CacheReplay.oneTimePublicKey cache secretKey.parameter
          secretKey.chainStart leafIndex) := by
  unfold keygenLeafTargetInput
  split
  · rename_i h
    obtain ⟨chosenEndpoints, hinput⟩ := h.choose_spec
    have hleafIndex : h.choose = leafIndex := by
      have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
        (hinput.trans rfl)
      simp only [HashDomain.leaf.injEq] at hdomain
      exact hdomain.symm
    rw [hleafIndex]
  · rename_i h
    exfalso
    exact h ⟨leafIndex, endpoints, rfl⟩

attribute [irreducible] keygenLeafTargetInput

end Xmss.Generic

