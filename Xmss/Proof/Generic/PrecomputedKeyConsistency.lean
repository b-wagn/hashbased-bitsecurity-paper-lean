import Xmss.Proof.Generic.CappedExecution.TreeCacheStability
import Xmss.Proof.Generic.PrecomputedKeygenCache

open OracleComp OracleSpec

namespace Xmss.Generic

variable [Code]

def PrecomputedKeyConsistent (keygenCache : QueryCache HashSpec)
    (secretKey : SecretKey) : Prop :=
  ∀ largerCache, keygenCache ≤ largerCache →
    ∀ leafIndex randomness encoding,
      Signing.precomputedSignWithEncoding secretKey leafIndex randomness encoding =
        CacheReplay.signWithEncoding largerCache secretKey leafIndex randomness encoding

theorem keygen_support_treeCacheStable
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅)) :
    CappedExecution.TreeCacheStable keyResult.1.2.parameter keyResult.1.2.chainStart
      keyResult.2 := by
  let chain : ChainIndex := ⟨0, Code.numChains_pos⟩
  let view : ProgrammedFixedChainKeygenView := {
    publicKey := keyResult.1.1
    secretKey := keyResult.1.2
    cache := keyResult.2
    table := keygenChainValueTable keyResult.2 keyResult.1.2 chain
  }
  apply CappedExecution.actualFixedChainKeygen_support_treeCacheStable chain view
  unfold actualFixedChainKeygen
  rw [mem_support_bind_iff]
  exact ⟨keyResult, hkeyResult, by simp [view]⟩

theorem Keygen.precomputedKeygen_support_oldKeygen
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.precomputedKeygen).run ∅)) :
    ((keyResult.1.1, Keygen.erasePrecomputation keyResult.1.2), keyResult.2) ∈
      support ((simulateQ romImpl Keygen.keygen).run ∅) := by
  have hmapped : ((Keygen.erasePrecomputedKeyResult keyResult.1, keyResult.2)) ∈
      support ((simulateQ romImpl
        (Keygen.erasePrecomputedKeyResult <$> Keygen.precomputedKeygen)).run ∅) := by
    rw [simulateQ_map, StateT.run_map, support_map]
    exact ⟨keyResult, hmem, rfl⟩
  rw [Keygen.erasePrecomputedKeygen_eq_keygen] at hmapped
  exact hmapped

theorem Keygen.oldKeygen_support_materializedPrecomputedKeygen
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅)) :
    Keygen.materializeCachedKeyResult keyResult ∈ support
      ((simulateQ romImpl Keygen.precomputedKeygen).run ∅) := by
  apply (mem_support_iff_of_evalDist_eq
    Keygen.evalDist_materialized_keygen_eq_precomputedKeygen _).mp
  rw [support_map]
  exact ⟨keyResult, hmem, rfl⟩

theorem Keygen.precomputedKeygen_support_secretKey_components
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.precomputedKeygen).run ∅)) :
    ∃ parameter secret,
      keyResult.1.2 = Keygen.precomputedSecretKey parameter secret keyResult.2 := by
  unfold Keygen.precomputedKeygen at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨parameter, parameterCache⟩, hparameter, hafterParameter⟩ := hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterParameter
  obtain ⟨⟨secret, secretCache⟩, hsecret, hafterSecret⟩ := hafterParameter
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterSecret
  obtain ⟨⟨treeResult, rootCache⟩, hroot, hout⟩ := hafterSecret
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hout
  subst keyResult
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
            OracleComp HashSpec Digest).withQueryLog) =
        simulateQ randomOracle
          (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
            OracleComp HashSpec Digest).withQueryLog := by
    simp only [romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
        OracleComp HashSpec Digest).withQueryLog
  rw [hroute, hsecretCache] at hroot
  have hcache := hashCacheOfLog_eq_finalCache_of_empty
    (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
      OracleComp HashSpec Digest) (treeResult, rootCache) hroot
  exact ⟨parameter, secret, by simp only; rw [hcache]⟩

theorem Keygen.precomputedKeygen_support_consistent
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.precomputedKeygen).run ∅)) :
    PrecomputedKeyConsistent keyResult.2 keyResult.1.2 := by
  obtain ⟨parameter, secret, hsecretKey⟩ :=
    Keygen.precomputedKeygen_support_secretKey_components keyResult hmem
  have hold := Keygen.precomputedKeygen_support_oldKeygen keyResult hmem
  have hstable := keygen_support_treeCacheStable
    ((keyResult.1.1, Keygen.erasePrecomputation keyResult.1.2), keyResult.2) hold
  intro largerCache hle leafIndex randomness encoding
  rw [hsecretKey] at hold hstable ⊢
  unfold Signing.precomputedSignWithEncoding CacheReplay.signWithEncoding
  refine congrArg₂ (Xmss.Signature.mk randomness) ?_ ?_
  · rw [CacheReplay.precomputedSignedChainValues_eq]
    funext chain
    exact Keygen.keygen_chainWalk_eq_of_cache_le
      ((keyResult.1.1,
        Keygen.erasePrecomputation
          (Keygen.precomputedSecretKey parameter secret keyResult.2)), keyResult.2)
      hold largerCache hle leafIndex chain (encoding chain).val
        (Nat.le_pred_of_lt (encoding chain).isLt)
  · rw [CacheReplay.precomputedAuthenticationPath_eq]
    exact CappedExecution.TreeCacheStable.authenticationPath_eq
      (Keygen.precomputedSecretKey parameter secret keyResult.2) keyResult.2
      hstable largerCache hle leafIndex

theorem Keygen.precomputedKeygen_cache_none_encodingInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.precomputedKeygen).run ∅))
    (targetLeafIndex : LeafIndex) (targetInput : Message × Randomness) :
    keyResult.2
      (CacheView.encodingInput keyResult.1.2.parameter targetLeafIndex targetInput) =
        none := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Keygen.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Keygen.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Keygen.keygen_cache_none_encodingInput oldKeyResult hold targetLeafIndex targetInput

theorem Keygen.precomputedKeygen_chainWalk_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1) :
    Wots.walk
        (CacheView.chainStep keyResult.2 keyResult.1.2.parameter leafIndex chain)
        0 steps (keyResult.1.2.chainStart leafIndex chain) =
      Wots.walk
        (CacheView.chainStep largerCache keyResult.1.2.parameter leafIndex chain)
        0 steps (keyResult.1.2.chainStart leafIndex chain) := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Keygen.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Keygen.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Keygen.keygen_chainWalk_eq_of_cache_le oldKeyResult hold largerCache hle leafIndex
    chain steps hsteps

theorem Keygen.precomputedKeygen_cache_has_chainInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.precomputedKeygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep) :
    ∃ output, keyResult.2
      (CacheView.chainInput keyResult.1.2.parameter leafIndex chain step
        (Wots.walk
          (CacheView.chainStep keyResult.2 keyResult.1.2.parameter leafIndex chain)
          0 step.val (keyResult.1.2.chainStart leafIndex chain))) = some output := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Keygen.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Keygen.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Keygen.keygen_cache_has_chainInput oldKeyResult hold leafIndex chain step

theorem Keygen.precomputedKeygen_cache_chainInput_eq_none_of_ne
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.precomputedKeygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep) (value : Digest)
    (hne : value ≠ Wots.walk
      (CacheView.chainStep keyResult.2 keyResult.1.2.parameter leafIndex chain)
      0 step.val (keyResult.1.2.chainStart leafIndex chain)) :
    keyResult.2
      (CacheView.chainInput keyResult.1.2.parameter leafIndex chain step value) = none := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Keygen.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Keygen.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Keygen.keygen_cache_chainInput_eq_none_of_ne oldKeyResult hold leafIndex chain step
    value hne

theorem Keygen.precomputedKeygen_cache_has_chainValue_preimage
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.precomputedKeygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (digit : Digit)
    (hpositive : 0 < digit.val) :
    ∃ previous : ChainStep, ∃ output,
      previous.val + 1 = digit.val ∧
      keyResult.2
        (CacheView.chainInput keyResult.1.2.parameter leafIndex chain previous
          (Wots.walk
            (CacheView.chainStep keyResult.2 keyResult.1.2.parameter leafIndex chain)
            0 previous.val (keyResult.1.2.chainStart leafIndex chain))) = some output ∧
      output =
        Wots.signChain
          (CacheView.chainStep keyResult.2 keyResult.1.2.parameter leafIndex chain)
          digit (keyResult.1.2.chainStart leafIndex chain) := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Keygen.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Keygen.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Keygen.keygen_cache_has_chainValue_preimage oldKeyResult hold leafIndex chain digit
    hpositive

theorem Keygen.precomputedKeygen_cache_has_merkleInput_in_largerCache
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (treeHeight - (level.val + 1))) :
    ∃ output, keyResult.2
      (CacheView.merkleInput keyResult.1.2.parameter level node
        (CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Merkle.childNode node false))
        (CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Merkle.childNode node true))) = some output := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Keygen.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Keygen.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Keygen.keygen_cache_has_merkleInput_in_largerCache oldKeyResult hold largerCache
    hle level node hnode

theorem Keygen.precomputedKeygen_cache_merkleInput_eq_none_of_ne_in_largerCache
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (treeHeight - (level.val + 1)))
    (left right : Digest)
    (hne : (left, right) ≠
      (CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Merkle.childNode node false),
        CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Merkle.childNode node true))) :
    keyResult.2
      (CacheView.merkleInput keyResult.1.2.parameter level node left right) = none := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Keygen.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Keygen.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Keygen.keygen_cache_merkleInput_eq_none_of_ne_in_largerCache oldKeyResult hold
    largerCache hle level node hnode left right hne

theorem Keygen.precomputedKeygen_merkleChildren_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (treeHeight - (level.val + 1))) :
    (CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Merkle.childNode node false),
      CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Merkle.childNode node true)) =
    (CacheReplay.treeNode largerCache keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Merkle.childNode node false),
      CacheReplay.treeNode largerCache keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Merkle.childNode node true)) := by
  let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
    ((keyResult.1.1, Keygen.erasePrecomputation keyResult.1.2), keyResult.2)
  have hold := Keygen.precomputedKeygen_support_oldKeygen keyResult hmem
  exact Keygen.keygen_merkleChildren_eq_of_cache_le oldKeyResult hold largerCache hle
    level node hnode

end Xmss.Generic
