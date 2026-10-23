import Xmss.Proof.Generic.MerkleQueryBound
import Xmss.Proof.Generic.QueryPresence
import Xmss.Proof.Generic.StatementLemmas

open OracleComp OracleSpec

namespace Xmss.Generic.CacheReplay

variable [Code]

theorem treeNode_merkle_query_cached_in_largerCache
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node)
    (hcontains : MerkleAddressInSubtree targetLevel targetNode levels node)
    (initialCache resultCache largerCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Merkle.treeNode parameter secret levels node :
          OracleComp HashSpec Digest)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ output, resultCache
      (CacheView.merkleInput parameter targetLevel targetNode
        (treeNode largerCache parameter secret targetLevel.val
          (Merkle.childNode targetNode false))
        (treeNode largerCache parameter secret targetLevel.val
          (Merkle.childNode targetNode true))) = some output := by
  induction levels generalizing node initialCache resultCache digest with
  | zero => simp [MerkleAddressInSubtree] at hcontains
  | succ levels ih =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      have hleftValid := childNode_subtreeValid levels node false hvalid
      have hrightValid := childNode_subtreeValid levels node true hvalid
      rw [Merkle.treeNode_succ_eq, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨left, leftCache⟩, hleft, hrest⟩ := hmem
      have hrestAll := hrest
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨right, rightCache⟩, hright, hnode⟩ := hrest
      by_cases hcurrent : targetLevel.val = levels
      · have htargetLevel : targetLevel = ⟨levels, hlevel⟩ := Fin.ext hcurrent
        subst targetLevel
        have htargetNode : targetNode = node := by
          unfold MerkleAddressInSubtree at hcontains
          have hcover : TreeCovers 0 node targetNode := by
            simpa [hcurrent] using hcontains.2
          exact (treeCovers_zero_iff node targetNode).mp hcover |>.symm
        subst targetNode
        have hrightLe : rightCache ≤ resultCache :=
          randomOracle_cache_le
            (Hashing.nodeHash parameter ⟨levels, hlevel⟩ node left right :
              OracleComp HashSpec Digest)
            rightCache (digest, resultCache) (by
              simpa only [hlevel, ↓reduceDIte] using hnode)
        obtain ⟨output, hcached, _⟩ := tweakableHash_query_cached parameter
          (.merkle ⟨levels, hlevel⟩ node) (Hashing.nodePayload left right)
          rightCache resultCache digest (by
            simpa [Hashing.nodeHash, hlevel] using hnode)
        have hleftEval := eval_answerFn_largerCache_eq_of_mem_support
          (Merkle.treeNode parameter secret levels (Merkle.childNode node false) :
            OracleComp HashSpec Digest)
          initialCache leftCache largerCache left hleft
          ((randomOracle_cache_le
            (do
              let right ← Merkle.treeNode parameter secret levels
                (Merkle.childNode node true)
              Hashing.nodeHash parameter ⟨levels, hlevel⟩ node left right :
              OracleComp HashSpec Digest)
            leftCache (digest, resultCache) (by
              simpa only [hlevel, ↓reduceDIte] using hrestAll)).trans hle)
        have hrightEval := eval_answerFn_largerCache_eq_of_mem_support
          (Merkle.treeNode parameter secret levels (Merkle.childNode node true) :
            OracleComp HashSpec Digest)
          leftCache rightCache largerCache right hright (hrightLe.trans hle)
        rw [eval_treeNode] at hleftEval hrightEval
        refine ⟨output, ?_⟩
        rw [hleftEval, hrightEval]
        exact hcached
      · have htargetLt : targetLevel.val < levels := by
          unfold MerkleAddressInSubtree at hcontains
          omega
        have hleftLe : leftCache ≤ resultCache :=
          randomOracle_cache_le
            (do
              let right ← Merkle.treeNode parameter secret levels
                (Merkle.childNode node true)
              Hashing.nodeHash parameter ⟨levels, hlevel⟩ node left right :
              OracleComp HashSpec Digest)
            leftCache (digest, resultCache) (by
              simpa only [hlevel, ↓reduceDIte] using hrestAll)
        have hpartition := merkleAddressInSubtree_step_sum targetLevel targetNode levels
          node hlevel hvalid
        rw [if_pos hcontains] at hpartition
        have hdomain : HashDomain.merkle ⟨levels, hlevel⟩ node ≠
            .merkle targetLevel targetNode := by
          intro heq
          have hlevelEq := congrArg Fin.val (HashDomain.merkle.inj heq).1
          exact hcurrent hlevelEq.symm
        rw [if_neg hdomain, add_zero] at hpartition
        by_cases hleftContains : MerkleAddressInSubtree targetLevel targetNode levels
            (Merkle.childNode node false)
        · obtain ⟨output, hcached⟩ :=
            ih (Merkle.childNode node false) (Nat.le_of_succ_le hlevels)
              hleftValid hleftContains initialCache leftCache left hleft (hleftLe.trans hle)
          exact ⟨output, hleftLe hcached⟩
        · have hrightContains : MerkleAddressInSubtree targetLevel targetNode levels
              (Merkle.childNode node true) := by
            simp only [hleftContains, if_false, zero_add] at hpartition
            split at hpartition
            · assumption
            · omega
          have hrightLe : rightCache ≤ resultCache :=
            randomOracle_cache_le
              (Hashing.nodeHash parameter ⟨levels, hlevel⟩ node left right :
                OracleComp HashSpec Digest)
              rightCache (digest, resultCache) (by
                simpa only [hlevel, ↓reduceDIte] using hnode)
          obtain ⟨output, hcached⟩ :=
            ih (Merkle.childNode node true) (Nat.le_of_succ_le hlevels)
              hrightValid hrightContains leftCache rightCache right hright (hrightLe.trans hle)
          exact ⟨output, hrightLe hcached⟩

theorem rootTree_merkle_query_cached
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (hnode : targetNode.val < 2 ^ (treeHeight - (targetLevel.val + 1)))
    (root : Digest) (cache largerCache : QueryCache HashSpec)
    (hmem : (root, cache) ∈ support
      ((simulateQ randomOracle
        (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
          OracleComp HashSpec Digest)).run ∅))
    (hle : cache ≤ largerCache) :
    ∃ output, cache
      (CacheView.merkleInput parameter targetLevel targetNode
        (treeNode largerCache parameter secret targetLevel.val
          (Merkle.childNode targetNode false))
        (treeNode largerCache parameter secret targetLevel.val
          (Merkle.childNode targetNode true))) = some output := by
  apply treeNode_merkle_query_cached_in_largerCache parameter secret targetLevel targetNode
    treeHeight Merkle.rootNode le_rfl
  · unfold TreeSubtreeValid Merkle.rootNode lifetime
    norm_num
  · unfold MerkleAddressInSubtree TreeCovers Merkle.rootNode lifetime
    constructor
    · exact targetLevel.isLt
    · constructor
      · simp
      · simpa using hnode
  · exact hmem
  · exact hle

end Xmss.Generic.CacheReplay

namespace Xmss.Generic

variable [Code]

theorem Keygen.keygen_cache_has_merkleInput_in_largerCache
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (treeHeight - (level.val + 1))) :
    ∃ output, keyResult.2
      (CacheView.merkleInput keyResult.1.2.parameter level node
        (CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Merkle.childNode node false))
        (CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Merkle.childNode node true))) = some output := by
  obtain ⟨parameter, secret, root, hkey, hroot⟩ :=
    Keygen.keygen_support_rootTree keyResult hmem
  rw [hkey]
  exact CacheReplay.rootTree_merkle_query_cached parameter secret level node hnode
    root keyResult.2 largerCache hroot hle

theorem Keygen.keygen_cache_has_merkleInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (treeHeight - (level.val + 1))) :
    ∃ output, keyResult.2
      (CacheView.merkleInput keyResult.1.2.parameter level node
        (CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Merkle.childNode node false))
        (CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Merkle.childNode node true))) = some output :=
  Keygen.keygen_cache_has_merkleInput_in_largerCache keyResult hmem keyResult.2 le_rfl
    level node hnode

theorem Keygen.keygen_cache_merkleInput_eq_none_of_ne_in_largerCache
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (treeHeight - (level.val + 1)))
    (left right : Digest)
    (hne : (left, right) ≠
      (CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Merkle.childNode node false),
        CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Merkle.childNode node true))) :
    keyResult.2 (CacheView.merkleInput keyResult.1.2.parameter level node left right) =
      none := by
  obtain ⟨honestOutput, hhonest⟩ :=
    Keygen.keygen_cache_has_merkleInput_in_largerCache keyResult hmem largerCache hle
      level node hnode
  cases hforged : keyResult.2
      (CacheView.merkleInput keyResult.1.2.parameter level node left right) with
  | none => rfl
  | some forgedOutput =>
      exfalso
      apply hne
      apply Hashing.nodePayload_injective
      exact payload_eq_of_tweakableHashInput_eq keyResult.1.2.parameter
        (.merkle level node)
        (Keygen.keygen_cache_unique_merkleAddress keyResult hmem level node
          (CacheView.merkleInput keyResult.1.2.parameter level node left right)
          (CacheView.merkleInput keyResult.1.2.parameter level node
            (CacheReplay.treeNode largerCache keyResult.1.2.parameter
              keyResult.1.2.chainStart level.val (Merkle.childNode node false))
            (CacheReplay.treeNode largerCache keyResult.1.2.parameter
              keyResult.1.2.chainStart level.val (Merkle.childNode node true)))
          forgedOutput honestOutput (by simp [CacheView.merkleInput])
          (by simp [CacheView.merkleInput]) hforged hhonest)

theorem Keygen.keygen_merkleChildren_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Keygen.keygen).run ∅))
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
  obtain ⟨initialOutput, hinitial⟩ :=
    Keygen.keygen_cache_has_merkleInput keyResult hmem level node hnode
  obtain ⟨largerOutput, hlarger⟩ :=
    Keygen.keygen_cache_has_merkleInput_in_largerCache keyResult hmem largerCache hle
      level node hnode
  apply Hashing.nodePayload_injective
  exact payload_eq_of_tweakableHashInput_eq keyResult.1.2.parameter (.merkle level node)
    (Keygen.keygen_cache_unique_merkleAddress keyResult hmem level node
      (CacheView.merkleInput keyResult.1.2.parameter level node
        (CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Merkle.childNode node false))
        (CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Merkle.childNode node true)))
      (CacheView.merkleInput keyResult.1.2.parameter level node
        (CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Merkle.childNode node false))
        (CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Merkle.childNode node true)))
      initialOutput largerOutput (by simp [CacheView.merkleInput])
      (by simp [CacheView.merkleInput]) hinitial hlarger)

end Xmss.Generic
