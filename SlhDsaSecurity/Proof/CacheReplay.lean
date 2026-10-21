import SlhDsaSecurity.Proof.QueryCached

/-!
# Replaying a run against its own final cache

This is the threading step the forgery decomposition needs, and the reason it is available
at all is that the scheme's operations are written against `[HasQuery HashSpec m]` for an
arbitrary monad: the extraction chain's `(m := Id)` statements hold for *any* hash function,
so they may be instantiated at the function the game itself produced.

`replay` turns a finished cache into such a function, and `run_eq_replay` says a hash-only
computation's oracle result is exactly what `replay` of the *final* cache computes. Both
directions of the threading follow: every value the verifier computed is reproduced by the
final cache, and every input it consulted is therefore present in that cache — which is what
`StructuralTerm.DeviatingCollision` and `GrowthCharge.Bad` quantify over.

The restriction to `OracleComp HashSpec` is essential rather than cosmetic. A computation that
also flips coins cannot be replayed from a cache, because the coins leave no trace in it; the
verifier is hash-only, which is why the statement is about it and not about the whole game.
-/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.CacheReplay

/-- A finished cache, read as a total hash function. -/
def replay (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => ((cache input).getD default : Id HashOutput)

/-- The oracle step either returns a cached value and leaves the cache alone, or samples and
installs one. -/
theorem step_shape (input : Bytes) (initialCache : QueryCache HashSpec)
    (step : HashOutput × QueryCache HashSpec)
    (hstep : step ∈ support ((randomOracle input).run initialCache)) :
    step.2 = initialCache.cacheQuery input step.1 ∨ step.2 = initialCache := by
  cases hcached : initialCache input with
  | some cached =>
    right
    have hrun : (randomOracle input).run initialCache =
        (pure (cached, initialCache) :
          ProbComp (HashOutput × QueryCache HashSpec)) := by
      rw [QueryImpl.withCaching_run_some _ hcached]
    rw [hrun, support_pure, Set.mem_singleton_iff] at hstep
    exact congrArg Prod.snd hstep
  | none =>
    left
    have hrun : (randomOracle input).run initialCache =
        (fun value => (value, initialCache.cacheQuery input value)) <$>
          ($ᵗ HashOutput : ProbComp HashOutput) := by
      rw [QueryImpl.withCaching_run_none _ hcached]
      simp [uniformSampleImpl]
    rw [hrun, support_map] at hstep
    obtain ⟨value, -, hpair⟩ := hstep
    rw [← congrArg Prod.snd hpair, ← congrArg Prod.fst hpair]

/-- The step's answer is what its cache then holds. -/
theorem step_cached (input : Bytes) (initialCache : QueryCache HashSpec)
    (step : HashOutput × QueryCache HashSpec)
    (hstep : step ∈ support ((randomOracle input).run initialCache)) :
    step.2 input = some step.1 := by
  rcases step_shape input initialCache step hstep with hshape | hshape
  · rw [hshape, QueryCache.cacheQuery_self]
  · cases hcached : initialCache input with
    | some cached =>
      have hrun : (randomOracle input).run initialCache =
          (pure (cached, initialCache) :
            ProbComp (HashOutput × QueryCache HashSpec)) := by
        rw [QueryImpl.withCaching_run_some _ hcached]
      rw [hrun, support_pure, Set.mem_singleton_iff] at hstep
      rw [hshape, hcached, congrArg Prod.fst hstep]
    | none =>
      exfalso
      have hrun : (randomOracle input).run initialCache =
          (fun value => (value, initialCache.cacheQuery input value)) <$>
            ($ᵗ HashOutput : ProbComp HashOutput) := by
        rw [QueryImpl.withCaching_run_none _ hcached]
        simp [uniformSampleImpl]
      rw [hrun, support_map] at hstep
      obtain ⟨value, -, hpair⟩ := hstep
      have hcache : initialCache.cacheQuery input value = initialCache :=
        (congrArg Prod.snd hpair).trans hshape
      have := congrFun hcache input
      rw [QueryCache.cacheQuery_self, hcached] at this
      simp at this

/-- Entries already present persist through a hash-only run. -/
theorem cache_value_persists {α : Type} (computation : OracleComp HashSpec α)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache))
    (input : Bytes) (output : HashOutput) (hentry : initialCache input = some output) :
    finalCache input = some output := by
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    simp only [Prod.mk.injEq] at hmem
    obtain ⟨-, rfl⟩ := hmem
    exact hentry
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    rcases eq_or_ne input queried with rfl | hne
    · -- The queried input was already present, so the step returns it unchanged.
      have hrun : (randomOracle input).run initialCache =
          (pure (output, initialCache) :
            ProbComp (HashOutput × QueryCache HashSpec)) := by
        rw [QueryImpl.withCaching_run_some _ hentry]
      rw [hrun, support_pure, Set.mem_singleton_iff] at hstep
      refine ih step.1 step.2 result hrest ?_
      rw [congrArg Prod.snd hstep]
      exact hentry
    · refine ih step.1 step.2 result hrest ?_
      rcases step_shape queried initialCache step hstep with hshape | hshape
      · rw [hshape, QueryCache.cacheQuery_of_ne initialCache step.1 hne]
        exact hentry
      · rw [hshape]
        exact hentry

/-- **A hash-only run is reproduced by its own final cache.** -/
theorem run_eq_replay {α : Type} (computation : OracleComp HashSpec α)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache)) :
    result = simulateQ (replay finalCache) computation := by
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    simp only [Prod.mk.injEq] at hmem
    obtain ⟨rfl, -⟩ := hmem
    rw [simulateQ_pure]
    rfl
  | query_bind input next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    have hfinal : finalCache input = some step.1 :=
      cache_value_persists (next step.1) step.2 finalCache result hrest input step.1
        (step_cached input initialCache step hstep)
    rw [ih step.1 step.2 result hrest, simulateQ_bind, simulateQ_spec_query]
    have hreplay : replay finalCache input = step.1 := by simp [replay, hfinal]
    rw [hreplay]
    rfl

/-! ## Reading the extraction chain's `Id`-level hashes out of the cache

The extraction chain states its collisions with `Hashing.tweakable (m := Id)`, under the
`[HasQuery HashSpec Id]` the development carries as a variable. `replayQuery` is the instance
that answers from a finished cache, and the two lemmas below say what that answers with: a
hash call is the cache's value, and a tweakable call is its truncation.

With these, every `Id`-level equation the extraction produces becomes a statement about cache
entries, which is what the structural charge quantifies over — so an accepted forgery's
collisions can be read off the cache the game itself left behind. -/

/-- The `HasQuery` instance that answers from a finished cache. -/
def replayQuery (cache : QueryCache HashSpec) : HasQuery HashSpec Id :=
  ⟨fun input => ((cache input).getD default : Id HashOutput)⟩

theorem hash_replayQuery (cache : QueryCache HashSpec) (input : Bytes) (output : HashOutput)
    (hentry : cache input = some output) :
    @Hashing.hash Id (replayQuery cache) input = output := by
  simp [Hashing.hash, replayQuery, hentry]

/-- A tweakable call reads the truncation of the cached answer at its own byte input. -/
theorem tweakable_replayQuery (cache : QueryCache HashSpec) (publicSeed : Digest)
    (address : Address) (payload : Bytes) (output : HashOutput)
    (hentry : cache (Hashing.tweakableInput publicSeed address payload) = some output) :
    @Hashing.tweakable Id _ (replayQuery cache) publicSeed address payload =
      Hashing.truncate output := by
  simp only [Hashing.tweakable, Hashing.shortHash, Hashing.hash, replayQuery, hentry,
    Option.getD_some]
  simp [Functor.map, hentry]

/-- The same for a bare `shortHash`, which the FORS compression collision is stated with. -/
theorem shortHash_replayQuery (cache : QueryCache HashSpec) (input : Bytes)
    (output : HashOutput) (hentry : cache input = some output) :
    @Hashing.shortHash Id _ (replayQuery cache) input = Hashing.truncate output := by
  simp only [Hashing.shortHash, Hashing.hash, replayQuery, hentry, Option.getD_some]
  simp [Functor.map, hentry]

/-! ## Which inputs a replayed run has cached

`run_eq_replay` says what a run *computed*; the structural charge also needs to know that the
inputs it consulted are *present* in the cache, since `StructuralTerm.DeviatingCollision` and
`GrowthCharge.Bad` both quantify over cache entries. Value correspondence does not give that
on its own: `replay` answers `default` at an absent input, so an equation could in principle
hold with nothing cached.

`QueriesUnder` names the inputs a hash-only computation consults when its answers come from a
given cache — the head query of each bind, and then whatever the continuation consults once
that answer is fixed. `cached_of_queriesUnder` then says every such input really is in the
final cache. Together with `run_eq_replay` this is the full threading: the verifier's computed
values are cache values, and the inputs behind them are cache entries.
-/

/-- The inputs a hash-only computation consults when answered from `cache`. -/
inductive QueriesUnder (cache : QueryCache HashSpec) :
    {α : Type} → OracleComp HashSpec α → Bytes → Prop where
  | head {α : Type} (input : Bytes) (next : HashOutput → OracleComp HashSpec α) :
      QueriesUnder cache (query (spec := HashSpec) input >>= next) input
  | tail {α : Type} (input probe : Bytes) (next : HashOutput → OracleComp HashSpec α) :
      QueriesUnder cache (next (replay cache input)) probe →
        QueriesUnder cache (query (spec := HashSpec) input >>= next) probe

/-- **Every input a replayed run consults is in its final cache.** -/
theorem cached_of_queriesUnder {α : Type} (computation : OracleComp HashSpec α)
    (initialCache finalCache : QueryCache HashSpec) (result : α) (probe : Bytes)
    (hquery : QueriesUnder finalCache computation probe)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache)) :
    finalCache probe ≠ none := by
  induction hquery generalizing initialCache result with
  | head input next =>
    rw [simulateQ_bind, show simulateQ randomOracle
        (query (spec := HashSpec) input) = randomOracle input from by simp,
      StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    have hentry : finalCache input = some step.1 :=
      cache_value_persists (next step.1) step.2 finalCache result hrest input step.1
        (step_cached input initialCache step hstep)
    rw [hentry]
    simp
  | tail input probe next _ ih =>
    rw [simulateQ_bind, show simulateQ randomOracle
        (query (spec := HashSpec) input) = randomOracle input from by simp,
      StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    -- The answer the run took is the one `replay` reproduces, so the continuations agree.
    have hentry : finalCache input = some step.1 :=
      cache_value_persists (next step.1) step.2 finalCache result hrest input step.1
        (step_cached input initialCache step hstep)
    have hreplay : replay finalCache input = step.1 := by simp [replay, hentry]
    exact ih step.2 result (by rw [hreplay]; exact hrest)

end SlhDsaSecurity.CacheReplay
