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

end SlhDsaSecurity.CacheReplay
