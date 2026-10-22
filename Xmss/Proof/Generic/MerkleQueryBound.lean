import Xmss.Proof.Generic.TreeQueryBound
import Xmss.Proof.Generic.StatementLemmas

namespace Xmss.Generic

variable [Code]

def MerkleAddressInSubtree (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (levels : Nat) (node : MerkleNode) : Prop :=
  targetLevel.val < levels ∧
    TreeCovers (levels - (targetLevel.val + 1)) node targetNode

instance (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (levels : Nat) (node : MerkleNode) :
    Decidable (MerkleAddressInSubtree targetLevel targetNode levels node) := by
  unfold MerkleAddressInSubtree
  infer_instance

omit [Code] in
theorem treeSubtreeValid_mono {small large : Nat} {node : MerkleNode}
    (hle : small ≤ large) (hvalid : TreeSubtreeValid large node) :
    TreeSubtreeValid small node := by
  unfold TreeSubtreeValid at hvalid ⊢
  have hpow : 2 ^ small ≤ 2 ^ large := Nat.pow_le_pow_right (by omega) hle
  nlinarith

omit [Code] in
theorem treeCovers_zero_iff (left right : MerkleNode) :
    TreeCovers 0 left right ↔ left = right := by
  constructor
  · intro h
    apply Fin.ext
    unfold TreeCovers at h
    simp only [pow_zero, mul_one] at h
    omega
  · rintro rfl
    unfold TreeCovers
    simp

theorem merkleAddressInSubtree_step_sum
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (levels : Nat) (node : MerkleNode) (hlevel : levels < treeHeight)
    (hvalid : TreeSubtreeValid (levels + 1) node) :
    (if MerkleAddressInSubtree targetLevel targetNode levels
          (Merkle.childNode node false) then 1 else 0) +
        ((if MerkleAddressInSubtree targetLevel targetNode levels
          (Merkle.childNode node true) then 1 else 0) +
          if HashDomain.merkle ⟨levels, hlevel⟩ node =
            .merkle targetLevel targetNode then 1 else 0) =
      if MerkleAddressInSubtree targetLevel targetNode (levels + 1) node then 1 else 0 := by
  by_cases hlt : targetLevel.val < levels
  · have hparentLt : targetLevel.val < levels + 1 := by omega
    have hexponent : levels + 1 - (targetLevel.val + 1) =
        (levels - (targetLevel.val + 1)) + 1 := by omega
    have hsmall : (levels - (targetLevel.val + 1)) + 1 ≤ levels + 1 := by omega
    have hpartition := treeCovers_children_sum
      (levels - (targetLevel.val + 1)) node targetNode
      (treeSubtreeValid_mono hsmall hvalid)
    have hdomain : HashDomain.merkle ⟨levels, hlevel⟩ node ≠
        .merkle targetLevel targetNode := by
      intro heq
      have hlevelEq := congrArg Fin.val (HashDomain.merkle.inj heq).1
      simp only at hlevelEq
      omega
    unfold MerkleAddressInSubtree
    simp only [hlt, hparentLt, true_and, hdomain, if_false, add_zero]
    rw [hexponent]
    exact hpartition
  · by_cases heq : targetLevel.val = levels
    · have hlevelEq : targetLevel = ⟨levels, hlevel⟩ := by
        apply Fin.ext
        exact heq
      subst targetLevel
      simp only [MerkleAddressInSubtree, lt_self_iff_false, false_and, if_false,
        Nat.lt_succ_self, true_and, Nat.sub_self, treeCovers_zero_iff,
        HashDomain.merkle.injEq]
      simp
    · have habove : levels < targetLevel.val := by omega
      have hnotParent : ¬targetLevel.val < levels + 1 := by omega
      have hdomain : HashDomain.merkle ⟨levels, hlevel⟩ node ≠
          .merkle targetLevel targetNode := by
        intro hsame
        have hlevelEq := congrArg Fin.val (HashDomain.merkle.inj hsame).1
        simp only at hlevelEq
        omega
      simp [MerkleAddressInSubtree, hlt, hnotParent, hdomain]

open OracleComp OracleSpec

theorem Merkle.treeNode_queryBound_merkleAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node) :
    (Merkle.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.merkle targetLevel targetNode))
        (if MerkleAddressInSubtree targetLevel targetNode levels node then 1 else 0) := by
  induction levels generalizing node with
  | zero =>
      rw [Merkle.treeNode_zero_eq]
      simpa [MerkleAddressInSubtree] using
        Merkle.leafAt_queryBound_zero_merkleAddress parameter secret node
          targetLevel targetNode
  | succ levels ih =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      have hleftValid := childNode_subtreeValid levels node false hvalid
      have hrightValid := childNode_subtreeValid levels node true hvalid
      have hleft := ih (Merkle.childNode node false)
        (Nat.le_of_succ_le hlevels) hleftValid
      have hright := ih (Merkle.childNode node true)
        (Nat.le_of_succ_le hlevels) hrightValid
      rw [Merkle.treeNode_succ_eq]
      have hcontinuation (left : Digest) :
          (do
            let right ← Merkle.treeNode parameter secret levels
              (Merkle.childNode node true)
            Hashing.nodeHash parameter ⟨levels, hlevel⟩ node left right :
            OracleComp HashSpec Digest).IsQueryBoundP
              (AtHashAddress parameter (.merkle targetLevel targetNode))
              ((if MerkleAddressInSubtree targetLevel targetNode levels
                  (Merkle.childNode node true) then 1 else 0) +
                if HashDomain.merkle ⟨levels, hlevel⟩ node =
                  .merkle targetLevel targetNode then 1 else 0) := by
        refine OracleComp.isQueryBoundP_bind hright ?_
        intro right _
        by_cases heq : HashDomain.merkle ⟨levels, hlevel⟩ node =
            .merkle targetLevel targetNode
        · simp only [heq, if_pos]
          obtain ⟨hlevelEq, hnodeEq⟩ := HashDomain.merkle.inj heq
          subst targetLevel
          subst targetNode
          exact Hashing.tweakableHash_queryBound_atAddress parameter
            (.merkle ⟨levels, hlevel⟩ node) (Hashing.nodePayload left right)
        · simp only [heq, if_false]
          exact Hashing.tweakableHash_queryBound_atOtherAddress parameter
            (.merkle targetLevel targetNode) (.merkle ⟨levels, hlevel⟩ node)
            (Hashing.nodePayload left right) heq
      have hall := OracleComp.isQueryBoundP_bind hleft
        (fun left _ => hcontinuation left)
      simpa only [hlevel, ↓reduceDIte,
        merkleAddressInSubtree_step_sum targetLevel targetNode levels node hlevel hvalid]
        using hall

theorem Merkle.rootTree_queryBound_merkleAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLevel : MerkleLevel) (targetNode : MerkleNode) :
    (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.merkle targetLevel targetNode)) 1 := by
  apply (Merkle.treeNode_queryBound_merkleAddress parameter secret targetLevel targetNode
    treeHeight Merkle.rootNode le_rfl (by
      unfold TreeSubtreeValid Merkle.rootNode lifetime
      norm_num)).mono
  split <;> omega

theorem CacheReplay.rootTree_cache_unique_merkleAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (root : Digest) (cache : QueryCache HashSpec)
    (hmem : (root, cache) ∈ support
      ((simulateQ randomOracle
        (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
          OracleComp HashSpec Digest)).run ∅))
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (left right : HashInput) (leftOutput rightOutput : Digest)
    (hleftP : AtHashAddress parameter (.merkle targetLevel targetNode) left)
    (hrightP : AtHashAddress parameter (.merkle targetLevel targetNode) right)
    (hleft : cache left = some leftOutput)
    (hright : cache right = some rightOutput) :
    left = right := by
  exact CacheReplay.cache_unique_of_query_bound_one
    (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
      OracleComp HashSpec Digest)
    (AtHashAddress parameter (.merkle targetLevel targetNode)) ∅ cache root
    (Merkle.rootTree_queryBound_merkleAddress parameter secret targetLevel targetNode)
    (by simp) hmem left right leftOutput rightOutput hleftP hrightP hleft hright

end Xmss.Generic
