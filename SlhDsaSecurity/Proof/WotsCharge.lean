import SlhDsaSecurity.Proof.CollisionToDeviating
import SlhDsaSecurity.Proof.CacheReplay
import SlhDsaSecurity.Proof.Extraction.Wots
import SlhDsaSecurity.Proof.CanonicalCells
import SlhDsaSecurity.Proof.CanonicalGraph.Correspondence

/-!
# A WOTS chain collision, charged

The third composition, and the one whose shape is a chain rather than a tree.

`Extraction.WotsPreimage.exists_preimage_witness` hands back a preimage, not a collision: on
some chain the forged value, hashed forward a positive number of steps, reaches the honestly
revealed value. `Extraction.Wots.chain_eq_or_collision` already turns that into the dichotomy
the charge needs — either the two chains started equal, in which case the adversary holds a
chain value no signature revealed and the win is on the secret side, or they differ somewhere
and then join, which is a `ChainCollision`.

A `ChainCollision` is the single-child shape: two different values hashed under the same
position address give the same result. So the composition below is the chain analogue of
`MerkleCharge`, resting on `CollisionToDeviating.deviatingCollision_of_single_child`.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.WotsCharge

open CanonicalGraph Extraction

/-- **A WOTS chain collision is a charged structural event.** -/
theorem deviatingCollision_of_chainCollision {α : Type} (publicSeed : Digest)
    (cells : Cells) (cache : QueryCache HashSpec) (parent : StructuralNode) (child : Node)
    (address : Address) (start offset : Nat) (actual canonical : Digest)
    -- how this chain position sits in the canonical graph
    (hchildren : parent.children = [child])
    (haddress : parent.address =
      { address with hashOrIndex := BitVec.ofNat 32 (start + offset) })
    (hchildCell : cells child =
      @SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed address
        start offset canonical)
    (hparentCell : cells (.structural parent) =
      @Hashing.tweakable Id _ (CacheReplay.replayQuery cache) publicSeed parent.address
        (bytesBE n (@SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed
          address start offset canonical)))
    -- the collision, and the cache entry its own query left behind
    (hcollision : @Wots.ChainCollision (CacheReplay.replayQuery cache) publicSeed address
      start actual canonical offset)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed parent.address
      (bytesBE n (@SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed
        address start offset actual))) = some output) :
    StructuralTerm.DeviatingCollision publicSeed cells result := by
  obtain ⟨hdiffers, hjoins⟩ := hcollision
  refine CollisionToDeviating.deviatingCollision_of_single_child publicSeed cells parent child
    (@SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed address
      start offset actual) hchildren ?_ result output ?_ ?_
  · rw [hchildCell]
    exact hdiffers
  · rw [hcache]
    exact hentry
  · have hcached := CacheReplay.tweakable_replayQuery cache publicSeed parent.address
      (bytesBE n (@SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed
        address start offset actual)) output hentry
    rw [hparentCell, ← hcached, haddress]
    exact hjoins

/-! ## Without the bookkeeping

A chain position's node is `CanonicalGraph.wotsPosition`, and the graph's definitions supply
every hypothesis: the node at position `p + 1` has the node at position `p` as its only child
(whether or not `p` is the chain's start), its address carries `p` in `hashOrIndex`, and its
child's honest cell is the chain value at `p` by
`CanonicalGraph.value_wotsPosition`. -/

/-- **A WOTS chain collision is charged, unconditionally.** -/
theorem deviatingCollision_of_chainCollision_canonical {α : Type}
    (secretSeed publicSeed : Digest) (cache : QueryCache HashSpec) (key : WotsKey)
    (chainIndex : Fin chains) (position : Fin w) (hposition : position.val < w - 1)
    (actual : Digest)
    (hcollision : @Wots.ChainCollision (CacheReplay.replayQuery cache) publicSeed
      { key.address with chainOrHeight := BitVec.ofNat 32 chainIndex.val } 0 actual
      (@Hashing.derive Id _ (CacheReplay.replayQuery cache) publicSeed secretSeed
        (SlhDsaSecurity.Wots.secretAddress key.address chainIndex)) position.val)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed
      (StructuralNode.wotsHash key chainIndex ⟨position.val, hposition⟩).address
      (bytesBE n (@SlhDsaSecurity.Wots.chain Id _ (CacheReplay.replayQuery cache) publicSeed
        { key.address with chainOrHeight := BitVec.ofNat 32 chainIndex.val } 0 position.val
        actual))) = some output) :
    StructuralTerm.DeviatingCollision publicSeed
      (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) result := by
  have hchildren : (StructuralNode.wotsHash key chainIndex ⟨position.val, hposition⟩).children =
      [.structural (wotsPosition key chainIndex position)] := by
    unfold wotsPosition
    split <;> simp_all [StructuralNode.children]
  refine deviatingCollision_of_chainCollision publicSeed
    (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) cache
    (.wotsHash key chainIndex ⟨position.val, hposition⟩)
    (.structural (wotsPosition key chainIndex position))
    { key.address with chainOrHeight := BitVec.ofNat 32 chainIndex.val } 0 position.val
    actual _ hchildren ?_ ?_ ?_ hcollision result output hcache hentry
  · simp [StructuralNode.address]
  · exact @value_wotsPosition (CacheReplay.replayQuery cache) secretSeed publicSeed
      key chainIndex position
  · rw [CanonicalCells.parentCell_tweakable cache secretSeed publicSeed, hchildren,
      CollisionToDeviating.childBytes_single,
      @value_wotsPosition (CacheReplay.replayQuery cache) secretSeed publicSeed]

end SlhDsaSecurity.WotsCharge
