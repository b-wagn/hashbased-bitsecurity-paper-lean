import Xmss.Proof.Generic.ConcreteCorrectness
import Xmss.Proof.Generic.TreeQueryBound

namespace Xmss.Generic

variable [Code]

omit [Code] in
theorem treeSubtreeValid_pathNode
    (leafIndex : LeafIndex) (levels : Nat) (hlevels : levels ≤ treeHeight) :
    TreeSubtreeValid levels
      (CacheReplay.pathNode leafIndex levels) := by
  have hfactor :
      2 ^ (treeHeight - levels) * 2 ^ levels = lifetime := by
    rw [← pow_add, Nat.sub_add_cancel hlevels]
    rfl
  have hquotient : leafIndex.val / 2 ^ levels < 2 ^ (treeHeight - levels) := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos (by omega) _)]
    rw [hfactor]
    exact leafIndex.isLt
  have hpath :
      (CacheReplay.pathNode leafIndex levels).val =
        leafIndex.val / 2 ^ levels := by
    unfold CacheReplay.pathNode Merkle.merkleNodeOfNat
    exact Nat.mod_eq_of_lt
      ((Nat.div_le_self leafIndex.val _).trans_lt leafIndex.isLt)
  unfold TreeSubtreeValid
  rw [hpath]
  nlinarith

omit [Code] in
theorem authenticationPathNode_subtreeValid
    (leafIndex : LeafIndex) (level : MerkleLevel) :
    TreeSubtreeValid level.val
      (Merkle.authenticationPathNode leafIndex level) := by
  have hparent : TreeSubtreeValid (level.val + 1)
      (CacheReplay.pathNode leafIndex (level.val + 1)) :=
    treeSubtreeValid_pathNode leafIndex (level.val + 1) (by omega)
  have hchildren := CacheReplay.pathNode_children
    leafIndex level.val level.isLt
  by_cases hbit : leafIndex.val.testBit level.val = true
  · rw [if_pos hbit] at hchildren
    have hvalid := childNode_subtreeValid level.val
      (CacheReplay.pathNode leafIndex (level.val + 1)) false hparent
    rw [hchildren.1] at hvalid
    exact hvalid
  · rw [if_neg hbit] at hchildren
    have hvalid := childNode_subtreeValid level.val
      (CacheReplay.pathNode leafIndex (level.val + 1)) true hparent
    rw [hchildren.2] at hvalid
    exact hvalid

end Xmss.Generic
