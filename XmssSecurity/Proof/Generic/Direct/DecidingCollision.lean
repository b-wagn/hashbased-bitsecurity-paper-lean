import XmssSecurity.Proof.Generic.Direct.DecidingClassification
import XmssSecurity.Proof.Generic.Direct.DecidingCache
import XmssSecurity.Proof.Generic.Direct.DecidingPrefix

/-! Turn the deterministic deciding-path classification into fresh collision witnesses. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Generic.Deciding

variable [Code]

open Concrete

section witnesses

variable (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
  (hkeygen : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
  (finalCache : QueryCache HashSpec) (hle : keyResult.2 ≤ finalCache)

include hkeygen hle

theorem decidingWitness_of_chain_collision (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) (output : Digest)
    (hcached : finalCache (CacheView.chainInput keyResult.1.2.parameter leafIndex chain step value) =
      some output)
    (hne : value ≠ Wots.walk
      (CacheView.chainStep finalCache keyResult.1.2.parameter leafIndex chain) 0 step.val
      (keyResult.1.2.chainStart leafIndex chain))
    (heq : CacheView.chainStep finalCache keyResult.1.2.parameter leafIndex chain step.val value =
      CacheView.chainStep finalCache keyResult.1.2.parameter leafIndex chain step.val
        (Wots.walk (CacheView.chainStep finalCache keyResult.1.2.parameter leafIndex chain)
          0 step.val (keyResult.1.2.chainStart leafIndex chain))) :
    DecidingCollisionWitness keyResult.1.2 keyResult.2 finalCache leafIndex chain := by
  apply decidingWitness_of_final_target_collision keyResult hkeygen finalCache hle leafIndex chain
    _ output (Or.inl ⟨step, value, rfl⟩) hcached
  · rw [keygenStructuralTargetInput_chainInput, CappedSuffix.keygenChainTargetInput_chainInput]
    exact fun h => hne (CacheView.chainInput_injective _ _ _ _ h)
  · rw [keygenStructuralTargetInput_chainInput, CappedSuffix.keygenChainTargetInput_chainInput]
    simpa only [CacheView.chainStep_eq _ _ _ _ _ _ step.isLt] using heq

theorem decidingWitness_of_leaf_collision (leafIndex : LeafIndex) (chain : ChainIndex)
    (endpoints : ChainIndex → Digest) (output : Digest)
    (hcached : finalCache (CacheView.leafInput keyResult.1.2.parameter leafIndex endpoints) =
      some output)
    (hcollision : Wots.HasLeafCollision (CacheView.leafHash finalCache keyResult.1.2.parameter leafIndex)
      endpoints (CacheReplay.oneTimePublicKey finalCache keyResult.1.2.parameter
        keyResult.1.2.chainStart leafIndex)) :
    DecidingCollisionWitness keyResult.1.2 keyResult.2 finalCache leafIndex chain := by
  apply decidingWitness_of_final_target_collision keyResult hkeygen finalCache hle leafIndex chain
    _ output (Or.inr (Or.inl ⟨endpoints, rfl⟩)) hcached
  · rw [keygenStructuralTargetInput_leafInput, CappedLeaf.keygenLeafTargetInput_leafInput]
    exact fun h => hcollision.1 (CacheView.leafInput_injective _ _ h)
  · rw [keygenStructuralTargetInput_leafInput, CappedLeaf.keygenLeafTargetInput_leafInput]
    exact hcollision.2

theorem decidingWitness_of_merkle_collision (leafIndex : LeafIndex) (chain : ChainIndex)
    (level : MerkleLevel) (current sibling honestCurrent honestSibling : Digest)
    (output : Digest)
    (hcached : finalCache (CacheView.nodeInput keyResult.1.2.parameter leafIndex level
      current sibling) = some output)
    (hne : (current, sibling) ≠ (honestCurrent, honestSibling))
    (heq : CacheView.nodeHash finalCache keyResult.1.2.parameter leafIndex level.val
      current sibling = CacheView.nodeHash finalCache keyResult.1.2.parameter leafIndex level.val
        honestCurrent honestSibling)
    (hhonest : CappedMerkle.orderedNodePair leafIndex level.val honestCurrent honestSibling =
      (CacheReplay.treeNode finalCache keyResult.1.2.parameter keyResult.1.2.chainStart level.val
          (Concrete.childNode (Concrete.nodeIndex leafIndex level.val) false),
        CacheReplay.treeNode finalCache keyResult.1.2.parameter keyResult.1.2.chainStart level.val
          (Concrete.childNode (Concrete.nodeIndex leafIndex level.val) true))) :
    DecidingCollisionWitness keyResult.1.2 keyResult.2 finalCache leafIndex chain := by
  have hinput : IsDecidingInput keyResult.1.2.parameter leafIndex chain
      (CacheView.nodeInput keyResult.1.2.parameter leafIndex level current sibling) := by
    rw [CappedMerkle.nodeInput_eq_merkleInput_ordered]
    exact Or.inr (Or.inr ⟨level, _, _, rfl⟩)
  have htarget : keygenStructuralTargetInput keyResult.1.2 finalCache
      (CacheView.nodeInput keyResult.1.2.parameter leafIndex level current sibling) =
      CacheView.nodeInput keyResult.1.2.parameter leafIndex level honestCurrent honestSibling := by
    rw [CappedMerkle.nodeInput_eq_merkleInput_ordered, keygenStructuralTargetInput_merkleInput,
      CappedMerkle.keygenMerkleTargetInput_merkleInput,
      CappedMerkle.nodeInput_eq_merkleInput_ordered]
    have hleft := congrArg Prod.fst hhonest
    have hright := congrArg Prod.snd hhonest
    simp only at hleft hright
    rw [hleft, hright]
  apply decidingWitness_of_final_target_collision keyResult hkeygen finalCache hle leafIndex chain
    _ output hinput hcached
  · rw [htarget]
    intro hsame
    apply hne
    apply CappedMerkle.orderedNodePair_injective leafIndex level.val
    apply nodePayload_injective
    rw [CappedMerkle.nodeInput_eq_merkleInput_ordered,
      CappedMerkle.nodeInput_eq_merkleInput_ordered] at hsame
    exact payload_eq_of_tweakableHashInput_eq _ _ hsame
  · rw [htarget]
    simpa only [CacheView.nodeHash_eq _ _ _ _ _ _ level.isLt] using heq

end witnesses

/-- A structural collision extracted from a supported forgery has its query cached and is fresh
relative to key generation. -/
theorem structuralCollision_afterKeygen_witness (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support ((simulateQ romImpl
      (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (encoding : Encoding) (hverified : execution.1.verified = true)
    (hdecode : forgedEncoding execution.2 execution.1.secretKey.parameter execution.1.forgery =
      some encoding)
    (hcollision : DecidingStructuralCollision execution.2 execution.1 encoding) :
    DecidingCollisionWitness keyResult.1.2 keyResult.2 execution.2 execution.1.forgery.epoch
      (decidingChain execution.2 execution.1.secretKey execution.1.signingLog
        execution.1.forgery encoding) := by
  have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen
    execution hafter
  have hkeys := CappedLeaf.detailedGameAfterKeygen_keys_eq adversary keyResult.1.1 keyResult.1.2
    keyResult.2 execution hafter
  have hle := xmssRom_cache_le _ keyResult.2 execution hafter
  let chain := decidingChain execution.2 execution.1.secretKey execution.1.signingLog
    execution.1.forgery encoding
  rcases hcollision with hchain | hleaf | ⟨level, hmerkle⟩
  · obtain ⟨offset, hoffset, hne, heq⟩ := hchain
    change offset < chainLength - 1 - (encoding chain).val at hoffset
    have hquery := CappedSuffix.detailed_execution_verified_chain_query_cached_as
      adversary execution hgame encoding hverified hdecode chain offset hoffset
    dsimp only [OracleSpec.Range, HashSpec, RandomOracleModel.HashSpec, OracleSpec.ofFn] at hquery
    obtain ⟨output, hcached⟩ := hquery
    have hwalk := CappedSuffix.Wots.walk_signChain_eq_honest
      (CacheView.chainStep execution.2 execution.1.secretKey.parameter execution.1.forgery.epoch chain)
      (encoding chain) offset (execution.1.secretKey.chainStart execution.1.forgery.epoch chain)
    change Wots.walk
        (CacheView.chainStep execution.2 execution.1.secretKey.parameter execution.1.forgery.epoch chain)
        (encoding chain).val offset (execution.1.forgery.signature.chainValue chain) ≠
      Wots.walk
        (CacheView.chainStep execution.2 execution.1.secretKey.parameter execution.1.forgery.epoch chain)
        (encoding chain).val offset (Wots.signChain _ (encoding chain)
          (execution.1.secretKey.chainStart execution.1.forgery.epoch chain)) at hne
    rw [hwalk] at hne
    change CacheView.chainStep execution.2 execution.1.secretKey.parameter execution.1.forgery.epoch
        chain ((encoding chain).val + offset)
        (Wots.walk
          (CacheView.chainStep execution.2 execution.1.secretKey.parameter execution.1.forgery.epoch chain)
          (encoding chain).val offset (execution.1.forgery.signature.chainValue chain)) =
      CacheView.chainStep execution.2 execution.1.secretKey.parameter execution.1.forgery.epoch
        chain ((encoding chain).val + offset)
        (Wots.walk
          (CacheView.chainStep execution.2 execution.1.secretKey.parameter execution.1.forgery.epoch chain)
          (encoding chain).val offset (Wots.signChain _ (encoding chain)
            (execution.1.secretKey.chainStart execution.1.forgery.epoch chain))) at heq
    rw [hwalk] at heq
    rw [hkeys.2] at hcached hne heq
    exact decidingWitness_of_chain_collision keyResult hkeygen execution.2 hle
      execution.1.forgery.epoch chain ⟨(encoding chain).val + offset, by omega⟩ _ output
      hcached hne heq
  · have hquery := CappedLeaf.detailed_execution_verified_leaf_cached_as
      adversary execution hgame encoding hverified hdecode
    dsimp only [OracleSpec.Range, HashSpec, RandomOracleModel.HashSpec, OracleSpec.ofFn] at hquery
    obtain ⟨output, hcached⟩ := hquery
    rw [hkeys.2] at hcached hleaf
    exact decidingWitness_of_leaf_collision keyResult hkeygen execution.2 hle
      execution.1.forgery.epoch chain _ output hcached hleaf
  · have hquery := CappedMerkle.detailed_execution_verified_merkle_query_cached_as
      adversary execution hgame encoding hverified hdecode level
    dsimp only [OracleSpec.Range, HashSpec, RandomOracleModel.HashSpec, OracleSpec.ofFn] at hquery
    obtain ⟨output, hcached⟩ := hquery
    have hcurrent := CacheReplay.authenticationPath_ascends_to_treeNode execution.2
      execution.1.secretKey execution.1.forgery.epoch execution.1.forgery.signature.randomness
      encoding level.val (Nat.le_of_lt level.isLt)
    have hsibling : signaturePath (CacheReplay.signWithEncoding execution.2 execution.1.secretKey
        execution.1.forgery.epoch execution.1.forgery.signature.randomness encoding) level.val =
      CacheReplay.treeNode execution.2 execution.1.secretKey.parameter execution.1.secretKey.chainStart
        level.val (Concrete.authenticationPathNode execution.1.forgery.epoch level) := by
      simp [signaturePath, CacheReplay.signWithEncoding, CacheReplay.authenticationPath, level.isLt]
    obtain ⟨hne, heq⟩ := hmerkle
    have hhonest := CappedMerkle.ordered_honestNodePair_eq_children execution.2 execution.1.secretKey
      execution.1.forgery.epoch level
    rw [← hcurrent, ← hsibling] at hhonest
    rw [hkeys.2] at hcached hne heq hhonest
    exact decidingWitness_of_merkle_collision keyResult hkeygen execution.2 hle
      execution.1.forgery.epoch chain level _ _ _ _ output hcached hne heq hhonest

/-- A winning execution outside the first lane and outside adversary-phase structural collisions
has a fresh collision during verification, on the path selected before verification. -/
theorem deciding_afterKeygen_orientation (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec)
    (hprefix : prefixResult ∈ support ((simulateQ romImpl
      (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (hcached : prefixResult.2 (CacheView.encodingInput keyResult.1.2.parameter prefixResult.1.1.epoch
      (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none)
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support ((simulateQ romImpl
      (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2))
    (hwin : execution.1.won = true)
    (hencoding : ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding)
    (hrevealed : ¬ DecidingChainValueRevealed execution.2 execution.1)
    (hprefixCollision : ¬ Rom.AdaptiveFreshDigestCollisionWith keyResult.2 prefixResult.2
      (keygenStructuralTargetInput keyResult.1.2 keyResult.2)) :
    Rom.AdaptiveFreshDigestCollisionWith prefixResult.2 execution.2
      (decidingTargetInput keyResult.1.2 keyResult.2 prefixResult.1.1.epoch
        (outcomeDecidingChain prefixResult.2
          ⟨keyResult.1.1, keyResult.1.2, prefixResult.1.1, prefixResult.1.2, false⟩)) := by
  have hfull := afterKeygen_of_phases adversary keyResult.1.1 keyResult.1.2 keyResult.2
    prefixResult hprefix execution hafter
  have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary keyResult hkeygen
    execution hfull
  rcases winning_outcome_deciding_classification execution.2 execution.1
      (capped_detailed_execution_consistent adversary execution hgame) hwin with
    henc | hrev | ⟨encoding, hdecode, hcollision⟩
  · exact (hencoding henc).elim
  · exact (hrevealed hrev).elim
  · have hwitness := structuralCollision_afterKeygen_witness adversary keyResult hkeygen
      execution hfull encoding (execution.1.won_eq_true_iff.mp hwin).2.2 hdecode hcollision
    have hselected := outcomeDecidingChain_prefix_eq_final adversary keyResult hkeygen
      prefixResult hprefix hcached execution hafter
    have hforgery := (verificationPhase_support _ _ _ _ _ hafter).2.2.1
    rw [hselected, outcomeDecidingChain_eq execution.2 execution.1 encoding hdecode, ← hforgery]
    exact decidingCollision_of_witness keyResult.1.2 keyResult.2 prefixResult.2 execution.2
      (xmssRom_cache_le _ keyResult.2 prefixResult hprefix)
      (xmssRom_cache_le _ prefixResult.2 execution hafter) _ _ hwitness hprefixCollision

end XmssSecurity.Generic.Deciding
