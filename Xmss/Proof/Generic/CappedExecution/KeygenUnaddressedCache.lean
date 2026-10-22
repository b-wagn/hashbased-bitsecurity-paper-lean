import Xmss.Proof.Generic.KeygenCache
import Xmss.Proof.Generic.StatementLemmas

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

open OracleComp OracleSpec

namespace Xmss.Generic.CappedExecution

variable [Code]

def KeygenAddressedHashInput
    (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ domain, AtHashAddress parameter domain input

noncomputable instance (parameter : PublicParameter) :
    DecidablePred (KeygenAddressedHashInput parameter) :=
  Classical.decPred _

theorem Hashing.tweakableHash_queryBound_zero_unaddressed
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    (Hashing.tweakableHash parameter domain payload :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  simp [Hashing.tweakableHash, Hashing.oracleHash,
    KeygenAddressedHashInput]

theorem Wots.chainWalk_queryBound_zero_unaddressed
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    (Wots.chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  induction steps with
  | zero => simp [Wots.chainWalk]
  | succ steps ih =>
      rw [Wots.chainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
      intro previous _
      split
      · exact Hashing.tweakableHash_queryBound_zero_unaddressed parameter _ _
      · simp

theorem Wots.oneTimePublicKey_queryBound_zero_unaddressed
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) :
    (Wots.oneTimePublicKey parameter secret leafIndex :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  rw [Wots.oneTimePublicKey]
  apply sequenceFin_queryBound_zero
  intro chain
  exact Wots.chainWalk_queryBound_zero_unaddressed parameter leafIndex chain
    0 (chainLength - 1) (secret leafIndex chain)

theorem Merkle.leafAt_queryBound_zero_unaddressed
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) :
    (Merkle.leafAt parameter secret leafIndex :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  rw [Merkle.leafAt]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Wots.oneTimePublicKey_queryBound_zero_unaddressed parameter secret
      leafIndex) ?_
  intro endpoints _
  exact Hashing.tweakableHash_queryBound_zero_unaddressed parameter _ _

theorem Merkle.treeNode_queryBound_zero_unaddressed
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    (Merkle.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (fun input => ¬ KeygenAddressedHashInput parameter input) 0 := by
  induction levels generalizing node with
  | zero =>
      rw [Merkle.treeNode_zero_eq]
      exact Merkle.leafAt_queryBound_zero_unaddressed parameter secret node
  | succ levels ih =>
      rw [Merkle.treeNode_succ_eq]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih (Merkle.childNode node false)) ?_
      intro left _
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih (Merkle.childNode node true)) ?_
      intro right _
      split
      · exact Hashing.tweakableHash_queryBound_zero_unaddressed parameter _ _
      · simp

theorem Keygen.keygen_cache_none_unaddressed
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
    (input : HashInput)
    (hinput : ¬ KeygenAddressedHashInput keyResult.1.2.parameter input) :
    keyResult.2 input = none := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Keygen.keygen_support_rootTree keyResult hmem
  rw [hkey] at hinput
  apply CacheReplay.cache_none_of_zero_query_bound
    (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
      OracleComp HashSpec Digest) input ∅ keyResult.2 root
  · apply (Merkle.treeNode_queryBound_zero_unaddressed parameter secret
      treeHeight Merkle.rootNode).of_imp
    intro candidate heq
    subst candidate
    exact hinput
  · simp
  · exact hroot

theorem Keygen.keygen_cache_none_at_encodingAddress
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
    (leafIndex : LeafIndex) (input : HashInput)
    (hinput : AtHashAddress keyResult.1.2.parameter (.encoding leafIndex) input) :
    keyResult.2 input = none := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Keygen.keygen_support_rootTree keyResult hmem
  rw [hkey] at hinput
  apply CacheReplay.cache_none_of_zero_query_bound
    (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
      OracleComp HashSpec Digest) input ∅ keyResult.2 root
  · apply (Merkle.treeNode_queryBound_zero_encodingAddress parameter secret
      leafIndex treeHeight Merkle.rootNode).of_imp
    intro candidate heq
    subst candidate
    exact hinput
  · simp
  · exact hroot

end Xmss.Generic.CappedExecution
