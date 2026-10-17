import XmssSecurity.Proof.Checksum.Direct.DecidingOrientation

/-! Cache facts for the honest targets on a deciding path. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Checksum.Deciding

open Concrete

variable (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
  (hkeygen : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))

include hkeygen

/-- Every deciding input has an honest target already present after key generation. -/
theorem keygen_deciding_target_cached (leafIndex : LeafIndex) (chain : ChainIndex)
    (input : HashInput) (hinput : IsDecidingInput keyResult.1.2.parameter leafIndex chain input) :
    ∃ output : HashOutput, keyResult.2 (keygenStructuralTargetInput keyResult.1.2 keyResult.2 input) =
      some output := by
  rcases hinput with ⟨step, value, rfl⟩ | ⟨endpoints, rfl⟩ | ⟨level, left, right, rfl⟩
  · rw [keygenStructuralTargetInput_chainInput,
      CappedSuffix.keygenChainTargetInput_chainInput]
    exact precomputedKeygen_cache_has_chainInput keyResult hkeygen leafIndex chain step
  · rw [keygenStructuralTargetInput_leafInput, CappedLeaf.keygenLeafTargetInput_leafInput]
    exact keygen_cache_has_leafInput _ (precomputedKeygen_support_oldKeygen keyResult hkeygen)
      leafIndex
  · rw [keygenStructuralTargetInput_merkleInput,
      CappedMerkle.keygenMerkleTargetInput_merkleInput]
    exact precomputedKeygen_cache_has_merkleInput_in_largerCache keyResult hkeygen
      keyResult.2 le_rfl level _ (CappedMerkle.nodeIndex_valid_at_level leafIndex level)

/-- Key generation contains only the honest input at each deciding address. -/
theorem keygen_deciding_input_none (leafIndex : LeafIndex) (chain : ChainIndex)
    (input : HashInput) (hinput : IsDecidingInput keyResult.1.2.parameter leafIndex chain input)
    (hne : input ≠ keygenStructuralTargetInput keyResult.1.2 keyResult.2 input) :
    keyResult.2 input = none := by
  rcases hinput with ⟨step, value, rfl⟩ | ⟨endpoints, rfl⟩ | ⟨level, left, right, rfl⟩
  · apply precomputedKeygen_cache_chainInput_eq_none_of_ne keyResult hkeygen leafIndex chain step
    intro heq
    apply hne
    simpa only [keygenStructuralTargetInput_chainInput,
      CappedSuffix.keygenChainTargetInput_chainInput] using congrArg
        (CacheView.chainInput keyResult.1.2.parameter leafIndex chain step) heq
  · apply keygen_cache_leafInput_eq_none_of_ne _
      (precomputedKeygen_support_oldKeygen keyResult hkeygen) leafIndex
    intro heq
    apply hne
    simpa only [keygenStructuralTargetInput_leafInput, CappedLeaf.keygenLeafTargetInput_leafInput]
      using congrArg (CacheView.leafInput keyResult.1.2.parameter leafIndex)
        (show endpoints = CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart leafIndex from heq)
  · apply precomputedKeygen_cache_merkleInput_eq_none_of_ne_in_largerCache keyResult hkeygen
      keyResult.2 le_rfl level _ (CappedMerkle.nodeIndex_valid_at_level leafIndex level)
    intro heq
    apply hne
    simpa only [keygenStructuralTargetInput_merkleInput,
      CappedMerkle.keygenMerkleTargetInput_merkleInput] using congrArg
        (fun pair : Digest × Digest => CacheView.merkleInput keyResult.1.2.parameter level
          (Concrete.nodeIndex leafIndex level.val) pair.1 pair.2) heq

/-- Extending the random-oracle cache preserves every honest target on the deciding path. -/
theorem keygen_deciding_target_stable (finalCache : QueryCache HashSpec)
    (hle : keyResult.2 ≤ finalCache) (leafIndex : LeafIndex) (chain : ChainIndex)
    (input : HashInput) (hinput : IsDecidingInput keyResult.1.2.parameter leafIndex chain input) :
    keygenStructuralTargetInput keyResult.1.2 keyResult.2 input =
      keygenStructuralTargetInput keyResult.1.2 finalCache input := by
  rcases hinput with ⟨step, value, rfl⟩ | ⟨endpoints, rfl⟩ | ⟨level, left, right, rfl⟩
  · simp only [keygenStructuralTargetInput_chainInput,
      CappedSuffix.keygenChainTargetInput_chainInput]
    exact congrArg (CacheView.chainInput keyResult.1.2.parameter leafIndex chain step)
      (precomputedKeygen_chainWalk_eq_of_cache_le keyResult hkeygen finalCache hle leafIndex
        chain step.val (Nat.le_of_lt step.isLt))
  · simp only [keygenStructuralTargetInput_leafInput, CappedLeaf.keygenLeafTargetInput_leafInput]
    exact congrArg (CacheView.leafInput keyResult.1.2.parameter leafIndex)
      (keygen_oneTimePublicKey_eq_of_cache_le _
        (precomputedKeygen_support_oldKeygen keyResult hkeygen) finalCache hle leafIndex)
  · rw [keygenStructuralTargetInput_merkleInput,
      keygenStructuralTargetInput_merkleInput,
      CappedMerkle.keygenMerkleTargetInput_merkleInput]
    rw [CappedMerkle.keygenMerkleTargetInput_merkleInput]
    have hstable := precomputedKeygen_merkleChildren_eq_of_cache_le keyResult hkeygen
      finalCache hle level (Concrete.nodeIndex leafIndex level.val)
      (CappedMerkle.nodeIndex_valid_at_level leafIndex level)
    have hleft := congrArg Prod.fst hstable
    have hright := congrArg Prod.snd hstable
    simp only at hleft hright
    rw [hleft, hright]

/-- A collision against the replayed honest target gives a fresh deciding-path witness. -/
theorem decidingWitness_of_final_target_collision (finalCache : QueryCache HashSpec)
    (hle : keyResult.2 ≤ finalCache) (leafIndex : LeafIndex) (chain : ChainIndex)
    (input : HashInput) (output : HashOutput)
    (hinput : IsDecidingInput keyResult.1.2.parameter leafIndex chain input)
    (hcached : finalCache input = some output)
    (hne : input ≠ keygenStructuralTargetInput keyResult.1.2 finalCache input)
    (hcollision : CacheView.digestAt finalCache input = CacheView.digestAt finalCache
      (keygenStructuralTargetInput keyResult.1.2 finalCache input)) :
    DecidingCollisionWitness keyResult.1.2 keyResult.2 finalCache leafIndex chain := by
  have hstable := keygen_deciding_target_stable keyResult hkeygen finalCache hle leafIndex chain
    input hinput
  rw [← hstable] at hne hcollision
  obtain ⟨targetOutput, htarget⟩ := keygen_deciding_target_cached keyResult hkeygen leafIndex chain
    input hinput
  exact ⟨input, output, targetOutput, hinput, hcached,
    keygen_deciding_input_none keyResult hkeygen leafIndex chain input hinput hne,
    htarget, hcollision⟩

end XmssSecurity.Checksum.Deciding
