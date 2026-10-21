import SlhDsaSecurity.Proof.CollisionToDeviating
import SlhDsaSecurity.Proof.CacheReplay
import SlhDsaSecurity.Proof.Extraction.Fors

/-!
# A FORS leaf collision, charged

The last of the four node shapes. `Extraction.Fors.LeafCollision` says a forged secret differs
from the honest one at a FORS leaf yet hashes to the same leaf value under that leaf's
address — already the single-child shape, so the composition is the direct analogue of
`WotsCharge`.

`Extraction.Fors.recoveredLeaf_canonical_secret_or_collision` is what produces it, and its
other branch is the one that matters for the budget: if there is no collision then the
revealed secret *is* the honest secret, which means the FORS position was disclosed by a
signature. That is the coverage avenue, charged at `2 ^ -129` on the message class, not the
structural avenue — so the two halves of the FORS argument land in different classes, which is
exactly why the per-class accounting is what makes the target reachable.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ForsLeafCharge

open CanonicalGraph Extraction

/-- **A FORS leaf collision is a charged structural event.** -/
theorem deviatingCollision_of_leafCollision {α : Type} (publicSeed secretSeed : Digest)
    (cells : Cells) (cache : QueryCache HashSpec) (parent : StructuralNode) (child : Node)
    (address : Address) (index : Nat) (forgedSecret : Digest)
    -- how this leaf sits in the canonical graph
    (hchildren : parent.children = [child])
    (haddress : parent.address = SlhDsaSecurity.Fors.nodeAddress address 0 index)
    (hchildCell : cells child =
      @SlhDsaSecurity.Fors.secret Id _ (CacheReplay.replayQuery cache) secretSeed publicSeed
        address index)
    (hparentCell : cells (.structural parent) =
      @Hashing.tweakable Id _ (CacheReplay.replayQuery cache) publicSeed parent.address
        (bytesBE n (@SlhDsaSecurity.Fors.secret Id _ (CacheReplay.replayQuery cache)
          secretSeed publicSeed address index)))
    -- the collision, and the cache entry its own query left behind
    (hcollision : @Fors.LeafCollision (CacheReplay.replayQuery cache) secretSeed publicSeed
      address index forgedSecret)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed parent.address
      (bytesBE n forgedSecret)) = some output) :
    StructuralTerm.DeviatingCollision publicSeed cells result := by
  obtain ⟨hdiffers, hjoins⟩ := hcollision
  refine CollisionToDeviating.deviatingCollision_of_single_child publicSeed cells parent child
    forgedSecret hchildren ?_ result output ?_ ?_
  · rw [hchildCell]
    exact hdiffers
  · rw [hcache]
    exact hentry
  · have hcached := CacheReplay.tweakable_replayQuery cache publicSeed parent.address
      (bytesBE n forgedSecret) output hentry
    rw [hparentCell, ← hcached, haddress]
    exact hjoins

end SlhDsaSecurity.ForsLeafCharge
