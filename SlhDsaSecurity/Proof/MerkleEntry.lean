import SlhDsaSecurity.Proof.CacheReplay
import SlhDsaSecurity.Proof.Extraction.BinaryPath

/-!
# The Merkle path's queries are cached

Chaining the peeling lemmas onto the verifier's Merkle path. The path is a fold of
`subtreeHeight` tweakable calls, and `MerkleCharge.deviatingCollision_of_pathCollision` needs,
at the height where the collision sits, an entry in the cache at that step's byte input.

Three identifications do it. `CacheReplay.queriesUnder_foldlM_get` says the `k`-th step
consults its input at the value `replayFold` has reached; `CacheReplay.replayFold_eq_foldl`
and `CacheReplay.foldl_finRange_take` rewrite that value as a fold over `List.finRange k`;
and `Extraction.BinaryPath.value_eq_fold` recognises *that* fold as
`Extraction.BinaryPath.value`, which is the value the collision is stated about.

The step of the replayed fold is `Hashing.tweakable` under `CacheReplay.replayQuery`
(`CacheReplay.replayFold_step_eq_tweakable`), so the `combine` the extraction reasons with and
the advance the replay performs are the same function.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.MerkleEntry

open CacheReplay Extraction

/-- The byte input the Merkle path's `j`-th step hashes. -/
def pathInput (publicSeed : Digest) (address : Address) (index : Nat)
    (siblings : Nat → Digest) : Digest → Fin subtreeHeight → Bytes :=
  fun value j => Hashing.tweakableInput publicSeed
    (SlhDsaSecurity.Merkle.nodeAddress address (j.val + 1) (index / 2 ^ (j.val + 1)))
    (BinaryPath.pairBytes (BinaryPath.ordered index j.val value (siblings j.val)))

/-- The recombination the extraction reasons with, answered from this cache. -/
noncomputable def pathCombine (cache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) : Nat → Nat → Digest → Digest → Digest :=
  fun height nodeIndex left right =>
    @Hashing.tweakable Id _ (replayQuery cache) publicSeed
      (SlhDsaSecurity.Merkle.nodeAddress address height nodeIndex)
      (BinaryPath.pairBytes (left, right))

/-- **The replayed path fold is the extraction's path value.** -/
theorem replayFold_eq_value (cache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) (index : Nat) (leaf : Digest) (siblings : Nat → Digest)
    (k : Nat) (hk : k ≤ subtreeHeight) :
    replayFold cache (pathInput publicSeed address index siblings)
        ((List.finRange subtreeHeight).take k) leaf =
      BinaryPath.value (pathCombine cache publicSeed address) index leaf siblings k := by
  rw [replayFold_eq_foldl, BinaryPath.value_eq_fold]
  exact foldl_finRange_take subtreeHeight k hk
    (fun value j => Hashing.truncate (replay cache (Hashing.tweakableInput publicSeed
      (SlhDsaSecurity.Merkle.nodeAddress address (j + 1) (index / 2 ^ (j + 1)))
      (BinaryPath.pairBytes (BinaryPath.ordered index j value (siblings j)))))) leaf

/-- **The step at any height leaves its input cached.** This is the hypothesis
`MerkleCharge.deviatingCollision_of_pathCollision` takes as `hentry`, with the running value
in the form the collision names it. -/
theorem pathInput_cached (cache initialCache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) (index : Nat) (leaf : Digest) (siblings : Nat → Digest)
    (height : Fin subtreeHeight) (result : Digest)
    (hmem : (result, cache) ∈ support ((simulateQ randomOracle
      ((List.finRange subtreeHeight).foldlM (m := OracleComp HashSpec)
        (fun value j => Hashing.shortHash
          (pathInput publicSeed address index siblings value j)) leaf)).run initialCache)) :
    cache (pathInput publicSeed address index siblings
      (BinaryPath.value (pathCombine cache publicSeed address) index leaf siblings height.val)
      height) ≠ none := by
  have hlt : height.val < (List.finRange subtreeHeight).length := by
    simpa using height.isLt
  have hquery := queriesUnder_foldlM_get cache
    (pathInput publicSeed address index siblings) (List.finRange subtreeHeight) leaf
    height.val hlt
  rw [show (List.finRange subtreeHeight)[height.val]'hlt = height from by apply Fin.ext; simp,
    replayFold_eq_value cache publicSeed address index leaf siblings height.val
      (le_of_lt height.isLt)] at hquery
  exact cached_of_queriesUnder
    ((List.finRange subtreeHeight).foldlM (m := OracleComp HashSpec)
      (fun value j => Hashing.shortHash
        (pathInput publicSeed address index siblings value j)) leaf)
    initialCache cache result _ hquery hmem

end SlhDsaSecurity.MerkleEntry
