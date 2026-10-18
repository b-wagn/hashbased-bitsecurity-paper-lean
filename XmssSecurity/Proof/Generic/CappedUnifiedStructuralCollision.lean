import XmssSecurity.Proof.Generic.GlobalBadEvent
import XmssSecurity.Proof.Generic.CappedSuffixEventProbability
import XmssSecurity.Proof.Generic.CappedMerkleEventProbability
import XmssSecurity.Proof.Generic.ExpectedAdaptiveFreshTarget
import XmssSecurity.Proof.Generic.CappedLeafEventProbability
import XmssSecurity.Proof.Generic.CappedChain.ChainEventDecomposition

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Generic

variable [Code]

set_option maxHeartbeats 10000

noncomputable def keygenStructuralTargetInput
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) : HashInput :=
  CappedMerkle.keygenMerkleTargetInput secretKey cache
    (CappedLeaf.keygenLeafTargetInput secretKey cache
      (CappedSuffix.keygenChainTargetInput secretKey cache input))

theorem CappedSuffix.keygenChainTargetInput_leafInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (endpoints : ChainIndex → Digest) :
    CappedSuffix.keygenChainTargetInput secretKey cache
      (Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints) =
    Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints := by
  unfold CappedSuffix.keygenChainTargetInput
  split
  · rename_i h
    obtain ⟨value, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      hinput
    cases hdomain
  · rfl

theorem CappedSuffix.keygenChainTargetInput_merkleInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) :
    CappedSuffix.keygenChainTargetInput secretKey cache
      (Concrete.CacheView.merkleInput secretKey.parameter level node left right) =
    Concrete.CacheView.merkleInput secretKey.parameter level node left right := by
  unfold CappedSuffix.keygenChainTargetInput
  split
  · rename_i h
    obtain ⟨value, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      hinput
    cases hdomain
  · rfl

theorem CappedLeaf.keygenLeafTargetInput_chainInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep)
    (value : Digest) :
    CappedLeaf.keygenLeafTargetInput secretKey cache
      (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value) =
    Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value := by
  unfold CappedLeaf.keygenLeafTargetInput
  split
  · rename_i h
    obtain ⟨endpoints, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      hinput
    cases hdomain
  · rfl

theorem CappedLeaf.keygenLeafTargetInput_merkleInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) :
    CappedLeaf.keygenLeafTargetInput secretKey cache
      (Concrete.CacheView.merkleInput secretKey.parameter level node left right) =
    Concrete.CacheView.merkleInput secretKey.parameter level node left right := by
  unfold CappedLeaf.keygenLeafTargetInput
  split
  · rename_i h
    obtain ⟨endpoints, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      hinput
    cases hdomain
  · rfl

theorem CappedMerkle.keygenMerkleTargetInput_chainInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep)
    (value : Digest) :
    CappedMerkle.keygenMerkleTargetInput secretKey cache
      (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value) =
    Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value := by
  unfold CappedMerkle.keygenMerkleTargetInput
  split
  · rename_i h
    obtain ⟨left, right, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      hinput
    cases hdomain
  · rfl

theorem CappedMerkle.keygenMerkleTargetInput_leafInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (endpoints : ChainIndex → Digest) :
    CappedMerkle.keygenMerkleTargetInput secretKey cache
      (Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints) =
    Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints := by
  unfold CappedMerkle.keygenMerkleTargetInput
  split
  · rename_i h
    obtain ⟨left, right, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter
      hinput
    cases hdomain
  · rfl

@[simp]
theorem keygenStructuralTargetInput_chainInput
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep)
    (value : Digest) :
    keygenStructuralTargetInput secretKey cache
      (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value) =
    CappedSuffix.keygenChainTargetInput secretKey cache
      (Concrete.CacheView.chainInput secretKey.parameter leafIndex chain step value) := by
  unfold keygenStructuralTargetInput
  rw [CappedSuffix.keygenChainTargetInput_chainInput,
    CappedLeaf.keygenLeafTargetInput_chainInput_eq_self,
    CappedMerkle.keygenMerkleTargetInput_chainInput_eq_self]

@[simp]
theorem keygenStructuralTargetInput_leafInput
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (endpoints : ChainIndex → Digest) :
    keygenStructuralTargetInput secretKey cache
      (Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints) =
    CappedLeaf.keygenLeafTargetInput secretKey cache
      (Concrete.CacheView.leafInput secretKey.parameter leafIndex endpoints) := by
  unfold keygenStructuralTargetInput
  rw [CappedSuffix.keygenChainTargetInput_leafInput_eq_self,
    CappedLeaf.keygenLeafTargetInput_leafInput,
    CappedMerkle.keygenMerkleTargetInput_leafInput_eq_self]

@[simp]
theorem keygenStructuralTargetInput_merkleInput
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (level : MerkleLevel) (node : MerkleNode) (left right : Digest) :
    keygenStructuralTargetInput secretKey cache
      (Concrete.CacheView.merkleInput secretKey.parameter level node left right) =
    CappedMerkle.keygenMerkleTargetInput secretKey cache
      (Concrete.CacheView.merkleInput secretKey.parameter level node left right) := by
  unfold keygenStructuralTargetInput
  rw [CappedSuffix.keygenChainTargetInput_merkleInput_eq_self,
    CappedLeaf.keygenLeafTargetInput_merkleInput_eq_self]

theorem adaptiveFreshDigestCollisionWith_of_target_eq
    (initialCache finalCache : QueryCache HashSpec)
    (sourceTarget target : HashInput → HashInput)
    (heq : ∀ input, sourceTarget input ≠ input →
      target input = sourceTarget input)
    (hcollision : Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache
      sourceTarget) :
    Rom.AdaptiveFreshDigestCollisionWith initialCache finalCache target := by
  obtain ⟨input, output, targetOutput, hfinal, hfresh, htarget, hdigest⟩ :=
    hcollision
  have hne : sourceTarget input ≠ input := by
    intro hsame
    rw [hsame, hfresh] at htarget
    contradiction
  refine ⟨input, output, targetOutput, hfinal, hfresh, ?_, ?_⟩
  · rw [heq input hne]
    exact htarget
  · rw [heq input hne]
    exact hdigest

end XmssSecurity.Generic
