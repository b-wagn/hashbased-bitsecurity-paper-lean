import Xmss.Proof.Generic.MerkleQueryBound
import Xmss.Proof.Generic.Execution
import Xmss.Proof.Generic.LazyScheme

open OracleComp OracleSpec

namespace Xmss.Generic

variable [Code]

theorem Keygen.keygen_support_rootTree
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅)) :
    ∃ parameter secret root,
      keyResult.1 = (⟨root, parameter⟩,
        SecretKey.withoutPrecomputation parameter secret) ∧
      (root, keyResult.2) ∈ support
        ((simulateQ randomOracle
          (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
            OracleComp HashSpec Digest)).run ∅) := by
  unfold Keygen.keygen at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨parameter, parameterCache⟩, hparameter, hafterParameter⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterParameter
  obtain ⟨⟨secret, secretCache⟩, hsecret, hafterSecret⟩ := hafterParameter
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterSecret
  obtain ⟨⟨root, rootCache⟩, hroot, hout⟩ := hafterSecret
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hout
  cases hout
  have hparameterCache : parameterCache = ∅ :=
    xmssRom_lift_probComp_cache_eq Keygen.samplePublicParameter ∅
      (parameter, parameterCache) hparameter
  have hsecretCache : secretCache = ∅ := by
    calc
      secretCache = parameterCache :=
        xmssRom_lift_probComp_cache_eq Keygen.sampleSecret parameterCache
          (secret, secretCache) hsecret
      _ = ∅ := hparameterCache
  have hroute :
      simulateQ romImpl
          (liftM (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
            OracleComp HashSpec Digest)) =
        simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
            OracleComp HashSpec Digest) := by
    simp only [romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
        OracleComp HashSpec Digest)
  rw [hroute, hsecretCache] at hroot
  exact ⟨parameter, secret, root, rfl, hroot⟩

theorem Keygen.keygen_cache_unique_leafAddress
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
    (targetLeafIndex : LeafIndex) (left right : HashInput)
    (leftOutput rightOutput : Digest)
    (hleftP : AtHashAddress keyResult.1.2.parameter (.leaf targetLeafIndex) left)
    (hrightP : AtHashAddress keyResult.1.2.parameter (.leaf targetLeafIndex) right)
    (hleft : keyResult.2 left = some leftOutput)
    (hright : keyResult.2 right = some rightOutput) :
    left = right := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Keygen.keygen_support_rootTree keyResult hmem
  rw [hkey] at hleftP hrightP
  exact CacheReplay.rootTree_cache_unique_leafAddress parameter secret root
    keyResult.2 hroot targetLeafIndex left right leftOutput rightOutput
    hleftP hrightP hleft hright

theorem Keygen.keygen_cache_unique_chainAddress
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
    (targetLeafIndex : LeafIndex) (targetChain : ChainIndex) (targetStep : ChainStep)
    (left right : HashInput) (leftOutput rightOutput : Digest)
    (hleftP : AtHashAddress keyResult.1.2.parameter
      (.chain targetLeafIndex targetChain targetStep) left)
    (hrightP : AtHashAddress keyResult.1.2.parameter
      (.chain targetLeafIndex targetChain targetStep) right)
    (hleft : keyResult.2 left = some leftOutput)
    (hright : keyResult.2 right = some rightOutput) :
    left = right := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Keygen.keygen_support_rootTree keyResult hmem
  rw [hkey] at hleftP hrightP
  exact CacheReplay.rootTree_cache_unique_chainAddress parameter secret root
    keyResult.2 hroot targetLeafIndex targetChain targetStep left right leftOutput rightOutput
    hleftP hrightP hleft hright

theorem Keygen.keygen_cache_unique_merkleAddress
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (left right : HashInput) (leftOutput rightOutput : Digest)
    (hleftP : AtHashAddress keyResult.1.2.parameter
      (.merkle targetLevel targetNode) left)
    (hrightP : AtHashAddress keyResult.1.2.parameter
      (.merkle targetLevel targetNode) right)
    (hleft : keyResult.2 left = some leftOutput)
    (hright : keyResult.2 right = some rightOutput) :
    left = right := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Keygen.keygen_support_rootTree keyResult hmem
  rw [hkey] at hleftP hrightP
  exact CacheReplay.rootTree_cache_unique_merkleAddress parameter secret root
    keyResult.2 hroot targetLevel targetNode left right leftOutput rightOutput
    hleftP hrightP hleft hright

/-- Key generation evaluates only chain, leaf, and Merkle domains, so its cache contains no encoding input. -/
theorem Keygen.keygen_cache_none_encodingInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
    (targetLeafIndex : LeafIndex) (targetInput : Message × Randomness) :
    keyResult.2
      (CacheView.encodingInput keyResult.1.2.parameter targetLeafIndex targetInput) =
        none := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Keygen.keygen_support_rootTree keyResult hmem
  rw [hkey]
  apply CacheReplay.cache_none_of_zero_query_bound
    (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
      OracleComp HashSpec Digest)
    (CacheView.encodingInput parameter targetLeafIndex targetInput)
    ∅ keyResult.2 root
  · exact (Merkle.treeNode_queryBound_zero_encodingAddress parameter secret targetLeafIndex
      treeHeight Merkle.rootNode).of_imp (by
        intro input hinput
        subst input
        rw [CacheView.encodingInput]
        exact atHashAddress_tweakableHashInput_iff parameter
          (.encoding targetLeafIndex) (.encoding targetLeafIndex) _ |>.2 rfl)
  · simp
  · exact hroot

end Xmss.Generic
