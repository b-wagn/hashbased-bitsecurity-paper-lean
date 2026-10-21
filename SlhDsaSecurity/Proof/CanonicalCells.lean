import SlhDsaSecurity.Proof.CacheReplay
import SlhDsaSecurity.Proof.CanonicalGraph.Evaluation

/-!
# The honest cells, read under the replay instance

Each of the four charge compositions carries a hypothesis saying that the parent node's honest
cell is the hash of its children's bytes under the parent's address. That hypothesis does not
have to be supplied per shape: `CanonicalGraph.value_equation` already states it
for every `StructuralNode`, and because the development's `[HasQuery HashSpec Id]` is a
variable rather than a fixed instance, it can be instantiated at `CacheReplay.replayQuery` —
the instance that answers from the cache the game left behind.

So `parentCell_tweakable` below discharges one hypothesis of `MerkleCharge`, `ForsCharge`,
`WotsCharge` and `ForsLeafCharge` in a single statement, for whichever cache the run produced.
What remains per shape is only the child-side bookkeeping: which graph node a given extraction
index names.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.CanonicalCells

open CanonicalGraph

/-- **The honest cell of a node is the tweakable hash of its children's bytes**, read under
the instance that answers from a finished cache. -/
theorem parentCell_tweakable (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (parent : StructuralNode) :
    @value (CacheReplay.replayQuery cache) secretSeed publicSeed
        (.structural parent) =
      @Hashing.tweakable Id _ (CacheReplay.replayQuery cache) publicSeed parent.address
        (childBytes (@value (CacheReplay.replayQuery cache) secretSeed publicSeed)
          parent.children) :=
  @value_equation (CacheReplay.replayQuery cache) secretSeed publicSeed parent

/-- The same, read out of the cache: when the node's own canonical query is cached, its honest
cell is that answer's truncation. -/
theorem parentCell_eq_truncate (cache : QueryCache HashSpec) (secretSeed publicSeed : Digest)
    (parent : StructuralNode) (output : HashOutput)
    (hentry : cache (canonicalInput publicSeed
      (@value (CacheReplay.replayQuery cache) secretSeed publicSeed) parent) =
      some output) :
    @value (CacheReplay.replayQuery cache) secretSeed publicSeed
        (.structural parent) = Hashing.truncate output := by
  rw [parentCell_tweakable cache secretSeed publicSeed parent]
  exact CacheReplay.tweakable_replayQuery cache publicSeed parent.address _ output hentry

end SlhDsaSecurity.CanonicalCells
