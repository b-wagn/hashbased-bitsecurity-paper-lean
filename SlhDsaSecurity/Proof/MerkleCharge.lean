import SlhDsaSecurity.Proof.CollisionToDeviating
import SlhDsaSecurity.Proof.CacheReplay

/-!
# A Merkle path collision, charged

This is the first full composition of the forgery decomposition: it takes the object the
extraction chain actually produces — a `BinaryPath.Collision` inside a `LayerCollision` — and
lands on the object the charge actually consumes, a `StructuralTerm.DeviatingCollision`.

Three facts meet here.

* `BinaryPath.canonical_step` says the canonical pair at a path position recombines to the
  honest node above it, so the collision's shared hash value *is* that honest node.
* `CacheReplay.tweakable_replayQuery` says the `Id`-level `combine` the extraction reasons
  with is the truncation of whatever the cache holds at the corresponding byte input — so the
  shared value is a cache entry's truncation.
* `CollisionToDeviating.deviatingCollision_of_tree_pair` converts a differing child pair whose
  input is cached into the charged event.

What is carried as hypotheses rather than derived is the index bookkeeping: `BinaryPath`
indexes a path by `Nat` and divides by powers of two, while the canonical graph indexes nodes
by `Fin`. Matching the two is arithmetic with no cryptographic content, and keeping it in the
hypotheses lets the actual argument be stated once rather than per layer.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.MerkleCharge

open CanonicalGraph Extraction

/-- **A path collision is a charged structural event.** -/
theorem deviatingCollision_of_pathCollision {α : Type} (publicSeed : Digest) (cells : Cells)
    (cache : QueryCache HashSpec) (address : Address) (nodes : Nat → Nat → Digest)
    (index height : Nat) (leaf : Digest) (siblings : Nat → Digest)
    (location : Tree) (parentHeight : Fin subtreeHeight)
    (parentIndex : Fin (2 ^ (subtreeHeight - (parentHeight.val + 1))))
    -- the combination rule the extraction uses, answered from this cache
    (combine : Nat → Nat → Digest → Digest → Digest)
    (hcombine : ∀ h i l r, combine h i l r =
      @Hashing.tweakable Id _ (CacheReplay.replayQuery cache) publicSeed
        (SlhDsaSecurity.Merkle.nodeAddress address h i) (BinaryPath.pairBytes (l, r)))
    (hnodes : ∀ h i, nodes (h + 1) i =
      combine (h + 1) i (nodes h (2 * i)) (nodes h (2 * i + 1)))
    -- how this path position sits in the canonical graph
    (haddress : (StructuralNode.tree location parentHeight parentIndex).address =
      SlhDsaSecurity.Merkle.nodeAddress address (height + 1) (index / 2 ^ (height + 1)))
    (hchildren : (StructuralNode.tree location parentHeight parentIndex).children =
      [.structural (merkleChild location parentHeight parentIndex 0),
        .structural (merkleChild location parentHeight parentIndex 1)])
    (hdistinct : (Node.structural (merkleChild location parentHeight parentIndex 0)) ≠
      .structural (merkleChild location parentHeight parentIndex 1))
    (hparentCell : cells (.structural (.tree location parentHeight parentIndex)) =
      nodes (height + 1) (index / 2 ^ (height + 1)))
    (hleftCell : cells (.structural (merkleChild location parentHeight parentIndex 0)) =
      (BinaryPath.canonicalPair nodes index height).1)
    (hrightCell : cells (.structural (merkleChild location parentHeight parentIndex 1)) =
      (BinaryPath.canonicalPair nodes index height).2)
    -- the collision, and the cache entry its own query left behind
    (hcollision : BinaryPath.Collision nodes combine index leaf siblings height)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed
        (StructuralNode.tree location parentHeight parentIndex).address
        (BinaryPath.pairBytes
          (BinaryPath.ordered index height
            (BinaryPath.value combine index leaf siblings height) (siblings height)))) =
      some output) :

    StructuralTerm.DeviatingCollision publicSeed cells result := by
  obtain ⟨hdiffers, hjoins⟩ := hcollision
  set actual := BinaryPath.ordered index height
    (BinaryPath.value combine index leaf siblings height) (siblings height) with hactualDef
  -- The canonical pair recombines to the honest node, so the shared value is that node.
  have hcanonical := BinaryPath.canonical_step nodes combine hnodes index height
  -- The shared value is also the truncation of the cached answer at the actual pair.
  have hactual : combine (height + 1) (index / 2 ^ (height + 1)) actual.1 actual.2 =
      Hashing.truncate output := by
    rw [hcombine, ← haddress]
    exact CacheReplay.tweakable_replayQuery cache publicSeed _ _ output hentry
  refine CollisionToDeviating.deviatingCollision_of_tree_pair publicSeed cells location
    parentHeight parentIndex actual.1 actual.2 hchildren hdistinct ?_ result output ?_ ?_
  · -- The actual pair differs from the honest one.
    rw [hleftCell, hrightCell]
    exact fun hsame =>
      hdiffers (Prod.ext (congrArg Prod.fst hsame) (congrArg Prod.snd hsame))
  · rw [hcache]
    exact hentry
  · -- and its answer truncates to the parent's honest cell.
    rw [hparentCell, ← hcanonical, ← hjoins]
    exact hactual.symm

end SlhDsaSecurity.MerkleCharge
