import SlhDsaSecurity.Proof.CollisionToDeviating
import SlhDsaSecurity.Proof.CacheReplay
import SlhDsaSecurity.Proof.Extraction.Fors

/-!
# A FORS root-compression collision, charged

The companion to `MerkleCharge` for the other node shape the extraction chain produces.
`Extraction.Fors.CompressionCollision` says two different root arrays hash to the same value
under the FORS root address; the charge wants a differing child together with a cache entry
whose answer truncates to the parent's honest cell.

The derivation is short because the collision already carries both halves. That the arrays
differ follows from the byte inputs differing, since they share a seed and an address and so
can only differ in their payloads. That the shared hash value is the parent's honest cell is
the FORS public key being that cell — `CanonicalGraph.Correspondence.fors_publicKey_cell` —
and `CacheReplay.shortHash_replayQuery` turns the `Id`-level hash into the cached answer's
truncation.

As in `MerkleCharge`, the correspondence between the extraction's indices and the canonical
graph's nodes is carried as hypotheses: it is bookkeeping, discharged where the layer is
known, and stating it here would tie the argument to one layer.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ForsCharge

open CanonicalGraph Extraction

/-- **A FORS root-compression collision is a charged structural event.** -/
theorem deviatingCollision_of_compressionCollision {α : Type} (publicSeed : Digest)
    (cells : Cells) (cache : QueryCache HashSpec) (parent : StructuralNode)
    (children : Fin forsTrees → Node) (actualRoots canonicalRoots : Fin forsTrees → Digest)
    (address : Address)
    -- how this compression node sits in the canonical graph
    (hchildren : parent.children = List.ofFn children)
    (hinj : Function.Injective children)
    (haddress : parent.address = Extraction.Fors.rootAddress address)
    (hchildCells : ∀ tree, cells (children tree) = canonicalRoots tree)
    (hparentCell : cells (.structural parent) =
      @Hashing.shortHash Id _ (CacheReplay.replayQuery cache)
        (Hashing.tweakableInput publicSeed (Extraction.Fors.rootAddress address)
          (digestArrayBytes canonicalRoots)))
    -- the collision, and the cache entry its own query left behind
    (hcollision : @Extraction.Fors.CompressionCollision (CacheReplay.replayQuery cache)
      actualRoots canonicalRoots publicSeed address)
    (result : α × QueryCache HashSpec) (output : HashOutput)
    (hcache : result.2 = cache)
    (hentry : cache (Hashing.tweakableInput publicSeed parent.address
      (digestArrayBytes actualRoots)) = some output) :
    StructuralTerm.DeviatingCollision publicSeed cells result := by
  obtain ⟨hinputs, hjoins⟩ := hcollision
  -- Sharing a seed and an address, the inputs can differ only in their payloads.
  have harrays : actualRoots ≠ canonicalRoots := by
    intro hsame
    exact hinputs (by rw [hsame])
  obtain ⟨tree, htree⟩ := Function.ne_iff.mp harrays
  refine CollisionToDeviating.deviatingCollision_of_array publicSeed cells parent children
    actualRoots hchildren hinj ⟨tree, ?_⟩ result output ?_ ?_
  · rw [hchildCells tree]
    exact htree
  · rw [hcache]
    exact hentry
  · -- The shared hash value is the parent's honest cell, read out of the cache.
    rw [hparentCell, ← hjoins]
    exact (CacheReplay.shortHash_replayQuery cache _ output (haddress ▸ hentry)).symm

end SlhDsaSecurity.ForsCharge
