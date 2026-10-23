import Xmss.Proof.Generic.ConcreteQueryBound
import Xmss.Proof.Generic.StatementLemmas

open OracleComp OracleSpec

namespace Xmss.Generic

variable [Code]

def TreeCovers (levels : Nat) (node : MerkleNode) (leafIndex : LeafIndex) : Prop :=
  node.val * 2 ^ levels ≤ leafIndex.val ∧ leafIndex.val < (node.val + 1) * 2 ^ levels

def TreeSubtreeValid (levels : Nat) (node : MerkleNode) : Prop :=
  (node.val + 1) * 2 ^ levels ≤ lifetime

instance (levels : Nat) (node : MerkleNode) (leafIndex : LeafIndex) :
    Decidable (TreeCovers levels node leafIndex) := by
  unfold TreeCovers
  infer_instance

omit [Code] in
theorem childNode_val_of_subtreeValid_succ (levels : Nat) (node : MerkleNode)
    (right : Bool) (hvalid : TreeSubtreeValid (levels + 1) node) :
    (Merkle.childNode node right).val = 2 * node.val + if right then 1 else 0 := by
  rw [Merkle.childNode, Merkle.merkleNodeOfNat]
  apply Nat.mod_eq_of_lt
  unfold TreeSubtreeValid at hvalid
  rw [pow_succ] at hvalid
  have hpow : 0 < 2 ^ levels := pow_pos (by omega) _
  split <;> nlinarith

omit [Code] in
theorem childNode_subtreeValid (levels : Nat) (node : MerkleNode)
    (right : Bool) (hvalid : TreeSubtreeValid (levels + 1) node) :
    TreeSubtreeValid levels (Merkle.childNode node right) := by
  unfold TreeSubtreeValid
  rw [childNode_val_of_subtreeValid_succ levels node right hvalid]
  unfold TreeSubtreeValid at hvalid
  rw [pow_succ] at hvalid
  have hpow : 0 < 2 ^ levels := pow_pos (by omega) _
  split <;> nlinarith

omit [Code] in
theorem treeCovers_children_sum (levels : Nat) (node : MerkleNode) (leafIndex : LeafIndex)
    (hvalid : TreeSubtreeValid (levels + 1) node) :
    (if TreeCovers levels (Merkle.childNode node false) leafIndex then 1 else 0) +
        (if TreeCovers levels (Merkle.childNode node true) leafIndex then 1 else 0) =
      if TreeCovers (levels + 1) node leafIndex then 1 else 0 := by
  by_cases hleft : TreeCovers levels (Merkle.childNode node false) leafIndex
  <;> by_cases hright : TreeCovers levels (Merkle.childNode node true) leafIndex
  <;> by_cases hparent : TreeCovers (levels + 1) node leafIndex
  <;> simp only [hleft, hright, hparent, ↓reduceIte]
  all_goals
    unfold TreeCovers at hleft hright hparent
    simp only [childNode_val_of_subtreeValid_succ levels node false hvalid,
      childNode_val_of_subtreeValid_succ levels node true hvalid,
      Bool.false_eq_true, ↓reduceIte] at hleft hright
    rw [pow_succ] at hparent
    have hpow : 0 < 2 ^ levels := pow_pos (by omega) _
    ring_nf at hleft hright hparent
    omega

theorem Merkle.treeNode_queryBound_leafAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLeafIndex : LeafIndex) (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node) :
    (Merkle.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.leaf targetLeafIndex))
        (if TreeCovers levels node targetLeafIndex then 1 else 0) := by
  induction levels generalizing node with
  | zero =>
      rw [Merkle.treeNode_zero_eq]
      by_cases hcover : TreeCovers 0 node targetLeafIndex
      · have heq : node = targetLeafIndex := by
          apply Fin.ext
          unfold TreeCovers at hcover
          simp only [pow_zero, mul_one] at hcover
          omega
        subst targetLeafIndex
        simpa [hcover] using
          Merkle.leafAt_queryBound_leafAddress parameter secret node node
      · have hne : node ≠ targetLeafIndex := by
          intro heq
          subst targetLeafIndex
          apply hcover
          unfold TreeCovers
          simp
        simpa [hcover] using
          Merkle.leafAt_queryBound_zero_at_other_leaf parameter secret node
            targetLeafIndex hne
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
              (AtHashAddress parameter (.leaf targetLeafIndex))
              (if TreeCovers levels (Merkle.childNode node true) targetLeafIndex then 1 else 0) := by
        refine OracleComp.isQueryBoundP_bind (m := 0) hright ?_
        intro right _
        exact Hashing.tweakableHash_queryBound_atOtherAddress parameter
          (.leaf targetLeafIndex) (.merkle ⟨levels, hlevel⟩ node)
          (Hashing.nodePayload left right) (by simp)
      have hall := OracleComp.isQueryBoundP_bind hleft
        (fun left _ => hcontinuation left)
      simpa only [hlevel, ↓reduceDIte, Nat.add_zero,
        treeCovers_children_sum levels node targetLeafIndex hvalid] using hall

theorem Merkle.rootTree_queryBound_leafAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLeafIndex : LeafIndex) :
    (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.leaf targetLeafIndex)) 1 := by
  have hbound := Merkle.treeNode_queryBound_leafAddress parameter secret targetLeafIndex
    treeHeight Merkle.rootNode le_rfl (by
      unfold TreeSubtreeValid Merkle.rootNode lifetime
      norm_num)
  have hcover : TreeCovers treeHeight Merkle.rootNode targetLeafIndex := by
    unfold TreeCovers Merkle.rootNode
    constructor
    · simp
    · simp [lifetime]
  simpa [hcover] using hbound

/-- A supported root-tree execution from an empty cache contains at most one input at each leaf address. -/
theorem CacheReplay.rootTree_cache_unique_leafAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (root : Digest) (cache : QueryCache HashSpec)
    (hmem : (root, cache) ∈ support
      ((simulateQ randomOracle
        (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
          OracleComp HashSpec Digest)).run ∅))
    (targetLeafIndex : LeafIndex) (left right : HashInput)
    (leftOutput rightOutput : Digest)
    (hleftP : AtHashAddress parameter (.leaf targetLeafIndex) left)
    (hrightP : AtHashAddress parameter (.leaf targetLeafIndex) right)
    (hleft : cache left = some leftOutput)
    (hright : cache right = some rightOutput) :
    left = right := by
  exact CacheReplay.cache_unique_of_query_bound_one
    (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
      OracleComp HashSpec Digest)
    (AtHashAddress parameter (.leaf targetLeafIndex)) ∅ cache root
    (Merkle.rootTree_queryBound_leafAddress parameter secret targetLeafIndex)
    (by simp) hmem left right leftOutput rightOutput hleftP hrightP hleft hright

theorem Merkle.treeNode_queryBound_chainAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLeafIndex : LeafIndex) (targetChain : ChainIndex) (targetStep : ChainStep)
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node) :
    (Merkle.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep))
        (if TreeCovers levels node targetLeafIndex then 1 else 0) := by
  induction levels generalizing node with
  | zero =>
      rw [Merkle.treeNode_zero_eq]
      by_cases hcover : TreeCovers 0 node targetLeafIndex
      · have heq : node = targetLeafIndex := by
          apply Fin.ext
          unfold TreeCovers at hcover
          simp only [pow_zero, mul_one] at hcover
          omega
        subst targetLeafIndex
        simpa [hcover] using
          Merkle.leafAt_queryBound_chainAddress parameter secret node node
            targetChain targetStep
      · have hne : node ≠ targetLeafIndex := by
          intro heq
          subst targetLeafIndex
          apply hcover
          unfold TreeCovers
          simp
        simpa [hcover] using
          Merkle.leafAt_queryBound_zero_chainAddress_at_other_leafIndex parameter secret node
            targetLeafIndex targetChain targetStep hne
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
              (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep))
              (if TreeCovers levels (Merkle.childNode node true) targetLeafIndex then 1 else 0) := by
        refine OracleComp.isQueryBoundP_bind (m := 0) hright ?_
        intro right _
        exact Hashing.tweakableHash_queryBound_atOtherAddress parameter
          (.chain targetLeafIndex targetChain targetStep) (.merkle ⟨levels, hlevel⟩ node)
          (Hashing.nodePayload left right) (by simp)
      have hall := OracleComp.isQueryBoundP_bind hleft
        (fun left _ => hcontinuation left)
      simpa only [hlevel, ↓reduceDIte, Nat.add_zero,
        treeCovers_children_sum levels node targetLeafIndex hvalid] using hall

theorem Merkle.rootTree_queryBound_chainAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLeafIndex : LeafIndex) (targetChain : ChainIndex) (targetStep : ChainStep) :
    (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep)) 1 := by
  have hbound := Merkle.treeNode_queryBound_chainAddress parameter secret targetLeafIndex
    targetChain targetStep treeHeight Merkle.rootNode le_rfl (by
      unfold TreeSubtreeValid Merkle.rootNode lifetime
      norm_num)
  have hcover : TreeCovers treeHeight Merkle.rootNode targetLeafIndex := by
    unfold TreeCovers Merkle.rootNode
    constructor
    · simp
    · simp [lifetime]
  simpa [hcover] using hbound

/-- A supported root-tree execution from an empty cache contains at most one input at each chain-step address. -/
theorem CacheReplay.rootTree_cache_unique_chainAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (root : Digest) (cache : QueryCache HashSpec)
    (hmem : (root, cache) ∈ support
      ((simulateQ randomOracle
        (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
          OracleComp HashSpec Digest)).run ∅))
    (targetLeafIndex : LeafIndex) (targetChain : ChainIndex) (targetStep : ChainStep)
    (left right : HashInput) (leftOutput rightOutput : Digest)
    (hleftP : AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep) left)
    (hrightP : AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep) right)
    (hleft : cache left = some leftOutput)
    (hright : cache right = some rightOutput) :
    left = right := by
  exact CacheReplay.cache_unique_of_query_bound_one
    (Merkle.treeNode parameter secret treeHeight Merkle.rootNode :
      OracleComp HashSpec Digest)
    (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep)) ∅ cache root
    (Merkle.rootTree_queryBound_chainAddress parameter secret targetLeafIndex
      targetChain targetStep)
    (by simp) hmem left right leftOutput rightOutput hleftP hrightP hleft hright

end Xmss.Generic
