import SlhDsaSecurity.Proof.AdversaryQueries
import SlhDsaSecurity.Proof.WarmedCharges
import SlhDsaSecurity.Proof.HonestProbes

/-!
# What key generation buys with the budget it spends

The target is `q / 2 ^ 127` exactly, and the charges carry three small defects that have to be
paid for out of the same budget. The room comes from the accounting itself: every hash call in
the game is charged, key generation's included, and after the graph is walked key generation
adds nothing to the cache. It spends and buys nothing.

So the growth a charge sees is bounded not by the whole count but by the count less what key
generation took. `HonestProbes.run_keygenInternal_world_eq_pure` is the half about the cache —
from the walk's table key generation is a `pure` computation, leaving the table exactly as it
found it — and `AdversaryQueries.mem_support_counted_bind_count` is the half about the count,
remembering how the total splits between the phases.

How much key generation takes is read off the Merkle recursion, and it is the whole subtree
rather than one path through it: every leaf ends in a compression call, so a subtree of height
`h` costs at least `2 ^ h`, and at `subtreeHeight` that is `512`. Following a single path would
give only `h + 1`, which covers the charges' defects but not the forgery's own claimed cells —
the input half records one candidate per claimed cell, a few hundred of them, and that is what
the larger constant pays for.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.HonestGrowth

open Security WarmedGame CacheReplay CanonicalGraph

/-- The walk's cache is the cache key generation is known to ask nothing new of. -/
theorem walk_cache_eq_warmCache
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) :
    ∃ outputs : Programming.Outputs,
      walk.2 = HonestProbes.warmCache walk.1.1.2.2 walk.1.1.1 outputs := by
  obtain ⟨outputs, hcells, hcache⟩ := mem_support_graphWalk hwalk
  exact ⟨outputs, by rw [hcache, hcells]; rfl⟩

/-! ## How much key generation spends

The exact number is not needed — the defects the charges carry sum to less than `2 ^ -125`, and
four units of budget at `2 ^ -127` apiece already exceed that. Four is read off the Merkle
recursion: each level above the leaves ends in one compression call, and the subtree has nine
of them. -/

theorem hash_eq_liftM (input : Bytes) :
    (Hashing.hash (m := OracleComp OracleWorld) input) =
      liftM (OracleWorld.query (Sum.inr input)) := rfl

/-- A single query is charged its own cost. -/
theorem count_query (queried : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (result : (OracleWorld.Range queried × Nat) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom (countAllHashes
      (liftM (OracleWorld.query queried) :
        OracleComp OracleWorld (OracleWorld.Range queried)))).run cache)) :
    result.1.2 = hashCost queried := by
  rw [GrowthBudget.countAllHashes_query, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff] at hmem
  obtain ⟨step, -, hpure⟩ := hmem
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hpure
  rw [hpure]

/-- A tweakable call is charged one unit. -/
theorem one_le_count_tweakable (publicSeed : Digest) (address : Address) (payload : Bytes)
    (cache : QueryCache HashSpec) (result : (Digest × Nat) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom (countAllHashes
      (Hashing.tweakable (m := OracleComp OracleWorld) publicSeed address payload))).run cache)) :
    1 ≤ result.1.2 := by
  rw [show (Hashing.tweakable (m := OracleComp OracleWorld) publicSeed address payload) =
      Hashing.truncate <$> (Hashing.hash (m := OracleComp OracleWorld)
        (Hashing.tweakableInput publicSeed address payload)) from by
      simp [Hashing.tweakable, Hashing.shortHash, map_eq_bind_pure_comp],
    AdversaryQueries.countAllHashes_map, simulateQ_map, StateT.run_map, support_map] at hmem
  obtain ⟨inner, hinner, heq⟩ := hmem
  have hcount := count_query (Sum.inr (Hashing.tweakableInput publicSeed address payload)) cache
    inner hinner
  rw [show result.1.2 = inner.1.2 from by rw [← heq], hcount]
  exact Nat.le_refl 1

/-- **A Merkle subtree of height `h` is charged at least `2 ^ h` units**: one compression at
every leaf, and the subtree has that many. Following a single path would give only `h + 1`;
taking both children at each step is what makes the honest phase's spend large enough to cover
the charges' defects. -/
theorem pow_le_count_merkleNode (secretSeed publicSeed : Digest) (address : Address) :
    ∀ (height index : Nat) (cache : QueryCache HashSpec)
      (result : (Digest × Nat) × QueryCache HashSpec),
      result ∈ support ((simulateQ KeygenUniform.rom (countAllHashes
        (SlhDsaSecurity.Merkle.node (m := OracleComp OracleWorld) secretSeed publicSeed address
          height index))).run cache) →
        2 ^ height ≤ result.1.2 := by
  intro height
  induction height with
  | zero =>
    intro index cache result hmem
    rw [SlhDsaSecurity.Merkle.node, SlhDsaSecurity.Wots.publicKey] at hmem
    obtain ⟨endpoints, middleCache, first, second, -, hsecond, hsplit⟩ :=
      AdversaryQueries.mem_support_counted_bind_count _ _ cache result hmem
    have hone : (1 : Nat) ≤ second := one_le_count_tweakable publicSeed _ _ middleCache
      ⟨⟨result.1.1, second⟩, result.2⟩ hsecond
    simp only [pow_zero]
    omega
  | succ height ih =>
    intro index cache result hmem
    rw [SlhDsaSecurity.Merkle.node] at hmem
    obtain ⟨left, leftCache, leftCount, restCount, hleft, hrest, hsplit⟩ :=
      AdversaryQueries.mem_support_counted_bind_count _ _ cache result hmem
    obtain ⟨right, rightCache, rightCount, lastCount, hright, hlast, hsplit'⟩ :=
      AdversaryQueries.mem_support_counted_bind_count _ _ leftCache _ hrest
    have hleftCount : 2 ^ height ≤ leftCount :=
      ih (2 * index) cache ⟨⟨left, leftCount⟩, leftCache⟩ hleft
    have hrightCount : 2 ^ height ≤ rightCount :=
      ih (2 * index + 1) leftCache ⟨⟨right, rightCount⟩, rightCache⟩ hright
    have hone : (1 : Nat) ≤ lastCount := one_le_count_tweakable publicSeed _ _ rightCache
      ⟨⟨result.1.1, lastCount⟩, result.2⟩ hlast
    have hpow : 2 ^ (height + 1) = 2 ^ height + 2 ^ height := by rw [pow_succ]; omega
    simp only at hsplit'
    omega

attribute [local irreducible] SlhDsaSecurity.Merkle.node

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **Key generation is charged at least `2 ^ subtreeHeight` units.** -/
theorem pow_le_count_keygen (secretSeed prfSeed publicSeed : Digest)
    (cache : QueryCache HashSpec)
    (result : ((SecretKey × PublicKey) × Nat) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom (countAllHashes
      (Scheme.keygenInternal secretSeed prfSeed publicSeed))).run cache)) :
    2 ^ subtreeHeight ≤ result.1.2 := by
  rw [Scheme.keygenInternal] at hmem
  obtain ⟨root, middleCache, first, second, hfirst, -, hsplit⟩ :=
    AdversaryQueries.mem_support_counted_bind_count _ _ cache result hmem
  have hnode : 2 ^ subtreeHeight ≤ first := pow_le_count_merkleNode secretSeed publicSeed
    (SlhDsaSecurity.Hypertree.address (layers - 1) 0) subtreeHeight 0 cache
    ⟨⟨root, first⟩, middleCache⟩ hfirst
  omega

attribute [local irreducible] WarmedGame.afterSeeds Scheme.keygenInternal Scheme.verify
  Scheme.sign Security.signingOracle Security.countQueries

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
/-- **Key generation spends budget and buys nothing.** On a warmed tail the cache grows by at
most the total hash count *less* what key generation charged: after the graph is walked key
generation asks the cache nothing new, so it leaves the cache exactly as it found it while still
being charged for every call it makes. -/
theorem growth_le_count_sub_keygen (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (tail adversary walk)) :
    ∃ (keygenCount : Nat) (keys : SecretKey × PublicKey),
      ((keys, keygenCount), walk.2) ∈ support ((simulateQ KeygenUniform.rom
        (countAllHashes (Scheme.keygenInternal walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2))).run
          walk.2) ∧
        keygenCount ≤ result.1.2 ∧
          GrowthCharge.GrowthAtMost walk.2 result.2 (result.1.2 - keygenCount) := by
  obtain ⟨outputs, hwarm⟩ := walk_cache_eq_warmCache hwalk
  have hrun : result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes (WarmedGame.afterSeeds adversary walk.1.1))).run walk.2) := hresult
  unfold WarmedGame.afterSeeds at hrun
  obtain ⟨keys, keyCache, keygenCount, restCount, hkeys, hrest, hsplit⟩ :=
    AdversaryQueries.mem_support_counted_bind_count _ _ walk.2 result hrun
  -- Key generation leaves the walk's cache exactly as it found it.
  have huncounted := WarmedSplit.mem_support_of_countAllHashes _ walk.2
    ⟨⟨keys, keygenCount⟩, keyCache⟩ hkeys
  rw [hwarm, HonestProbes.run_keygenInternal_world_eq_pure, support_pure,
    Set.mem_singleton_iff] at huncounted
  have hkeyCache : keyCache = walk.2 := by rw [hwarm]; exact (Prod.ext_iff.mp huncounted).2
  rw [hkeyCache] at hkeys hrest
  refine ⟨keygenCount, keys, hkeys, by omega, ?_⟩
  rw [show result.1.2 - keygenCount = restCount from by omega]
  exact GrowthBudget.growth_le_count _ walk.2 ⟨⟨result.1.1, restCount⟩, result.2⟩ hrest

/-- **`2 ^ subtreeHeight` units of the budget are spent before the adversary runs.** The cache
the tail grows is bounded by the total hash count less that, which is the room the charges'
defects and the forgery's own claimed cells need. -/
theorem growth_le_count_sub_pow (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (tail adversary walk)) :
    GrowthCharge.GrowthAtMost walk.2 result.2 (result.1.2 - 2 ^ subtreeHeight) := by
  obtain ⟨keygenCount, keys, hkeys, -, hgrowth⟩ :=
    growth_le_count_sub_keygen adversary hwalk hresult
  have hpow : (2 : Nat) ^ subtreeHeight ≤ keygenCount :=
    pow_le_count_keygen walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2
      ⟨⟨keys, keygenCount⟩, walk.2⟩ hkeys
  exact GrowthBudget.GrowthAtMost.mono hgrowth (by omega)

/-- The same at the coarser constant the earlier accounting used. -/
theorem growth_le_count_sub_four (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (tail adversary walk)) :
    GrowthCharge.GrowthAtMost walk.2 result.2 (result.1.2 - 4) :=
  GrowthBudget.GrowthAtMost.mono (growth_le_count_sub_pow adversary hwalk hresult)
    (by simp only [subtreeHeight]; omega)

end SlhDsaSecurity.HonestGrowth
