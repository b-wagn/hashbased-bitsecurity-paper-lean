import Xmss.Proof.Generic.CappedEncodingExpectedBound
import Xmss.Proof.Generic.CappedUnifiedStructuralCollision
import Xmss.Proof.Generic.ExactKeygenQueryCount
import Xmss.Proof.Generic.LossDecomposition

open OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

namespace Xmss.Generic

variable [Code]

set_option maxRecDepth 100000

theorem CappedSuffix.keygenChainTargetInput_encodingInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (payload : Message × Randomness) :
    CappedSuffix.keygenChainTargetInput secretKey cache
      (CacheView.encodingInput secretKey.parameter leafIndex payload) =
    CacheView.encodingInput secretKey.parameter leafIndex payload := by
  unfold CappedSuffix.keygenChainTargetInput
  split
  · rename_i h
    obtain ⟨value, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter hinput
    cases hdomain
  · rfl

theorem CappedLeaf.keygenLeafTargetInput_encodingInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (payload : Message × Randomness) :
    CappedLeaf.keygenLeafTargetInput secretKey cache
      (CacheView.encodingInput secretKey.parameter leafIndex payload) =
    CacheView.encodingInput secretKey.parameter leafIndex payload := by
  unfold CappedLeaf.keygenLeafTargetInput
  split
  · rename_i h
    obtain ⟨endpoints, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter hinput
    cases hdomain
  · rfl

theorem CappedMerkle.keygenMerkleTargetInput_encodingInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (payload : Message × Randomness) :
    CappedMerkle.keygenMerkleTargetInput secretKey cache
      (CacheView.encodingInput secretKey.parameter leafIndex payload) =
    CacheView.encodingInput secretKey.parameter leafIndex payload := by
  unfold CappedMerkle.keygenMerkleTargetInput
  split
  · rename_i h
    obtain ⟨left, right, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter hinput
    cases hdomain
  · rfl

@[simp]
theorem keygenStructuralTargetInput_encodingInput
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (payload : Message × Randomness) :
    keygenStructuralTargetInput secretKey cache
      (CacheView.encodingInput secretKey.parameter leafIndex payload) =
    CacheView.encodingInput secretKey.parameter leafIndex payload := by
  unfold keygenStructuralTargetInput
  rw [CappedSuffix.keygenChainTargetInput_encodingInput_eq_self,
    CappedLeaf.keygenLeafTargetInput_encodingInput_eq_self,
    CappedMerkle.keygenMerkleTargetInput_encodingInput_eq_self]

theorem encodingHashQuery_structuralQuery_disjoint
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : OracleWorld.Domain) :
    ¬(CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter input ∧
      RandomOracle.IsRelevantHashQuery (fun hashInput =>
        keygenStructuralTargetInput secretKey cache hashInput ≠ hashInput) input) := by
  cases input with
  | inl index => simp [CappedEncodingMonitor.IsEncodingHashQuery]
  | inr hashInput =>
      intro hboth
      rcases hboth with ⟨hencoding, hstructural⟩
      change (encodingInputLeafIndex? secretKey.parameter hashInput).isSome at hencoding
      change keygenStructuralTargetInput secretKey cache hashInput ≠ hashInput at hstructural
      cases hleafIndex : encodingInputLeafIndex? secretKey.parameter hashInput with
      | none => simp [hleafIndex] at hencoding
      | some leafIndex =>
          obtain ⟨payload, hpayload⟩ :=
            exists_encodingInput_of_encodingInputLeafIndex?_eq_some
              secretKey.parameter hashInput leafIndex hleafIndex
          rw [← hpayload] at hstructural
          exact hstructural
            (keygenStructuralTargetInput_encodingInput secretKey cache leafIndex payload)

end Xmss.Generic
