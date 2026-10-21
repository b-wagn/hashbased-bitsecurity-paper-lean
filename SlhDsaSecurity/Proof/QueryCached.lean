import SlhDsaSecurity.Proof.GrowthCharge

/-!
# A query that is made is a query that is cached

`GrowthCharge.cache_mono` and `cache_value_persists` say that what is already in the cache
stays there. This file supplies the converse direction, which is what the forgery
decomposition needs: a computation that *makes* a hash call leaves that call's input in the
final cache, with the very answer the call returned.

The need for it is where the two halves of `hsplit` meet. The extraction chain
(`Extraction.*`) is algebra about values the verifier computed; the charge
(`StructuralTerm.DeviatingCollision`, `CombinedCharge.CombinedBad`) is a statement about cache
entries. Nothing connects them until one observes that the verifier obtained those values by
querying, so the entries are present — and that each such query is one of the `q` charged
calls, which is why the event is affordable at the structural rate in the first place.

Both branches of the oracle give the entry. On a miss the answer is sampled and written; on a
hit the entry was already there and is the answer returned. So no freshness assumption is
needed, which matters: the verifier's calls are mostly repeats of calls the signer already
made, and under the all-queries-counted accounting those repeats are charged anyway.
-/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.QueryCached

/-! A hash call is written `Hashing.hash input`, which in `OracleComp OracleWorld` is
definitionally `query (spec := OracleWorld) (Sum.inr input)` — the form below, and the one the
induction in `GrowthCharge` produces. Callers may pass either. -/

/-- A single hash call leaves its input in the cache, holding the answer it returned. -/
theorem step_cached (input : Bytes) (initialCache : QueryCache HashSpec)
    (step : HashOutput × QueryCache HashSpec)
    (hstep : step ∈ support ((KeygenUniform.rom (Sum.inr input)).run initialCache)) :
    step.2 input = some step.1 := by
  cases hcached : initialCache input with
  | some cached =>
    have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
        (pure (cached, initialCache) :
          ProbComp (HashOutput × QueryCache HashSpec)) := by
      change (randomOracle input).run initialCache = _
      rw [QueryImpl.withCaching_run_some _ hcached]
    rw [hrun, support_pure, Set.mem_singleton_iff] at hstep
    subst hstep
    exact hcached
  | none =>
    have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
        (fun answer => (answer, initialCache.cacheQuery input answer)) <$>
          ($ᵗ HashOutput : ProbComp HashOutput) := by
      change (randomOracle input).run initialCache = _
      rw [QueryImpl.withCaching_run_none _ hcached]
      simp [uniformSampleImpl]
    rw [hrun, support_map] at hstep
    obtain ⟨answer, -, rfl⟩ := hstep
    exact QueryCache.cacheQuery_self initialCache input answer

/-- **A computation that makes a hash call leaves that input cached.** -/
theorem cached_of_hash {α : Type} (input : Bytes)
    (next : HashOutput → OracleComp OracleWorld α)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ KeygenUniform.rom
        ((query (spec := OracleWorld) (Sum.inr input)) >>= next)).run initialCache)) :
    finalCache input ≠ none := by
  rw [simulateQ_bind, show simulateQ KeygenUniform.rom
      (query (spec := OracleWorld) (Sum.inr input)) = KeygenUniform.rom (Sum.inr input)
      from by simp, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨step, hstep, hrest⟩ := hmem
  refine GrowthCharge.cache_mono (next step.1) step.2 finalCache result hrest input ?_
  rw [step_cached input initialCache step hstep]
  simp

/-- The answer is recoverable too: the call's input ends up holding the value the call
returned, so a caller may read the verifier's computed value straight out of the cache. -/
theorem answer_cached_of_hash {α : Type} (input : Bytes)
    (next : HashOutput → OracleComp OracleWorld α)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ KeygenUniform.rom
        ((query (spec := OracleWorld) (Sum.inr input)) >>= next)).run initialCache)) :
    ∃ answer : HashOutput, finalCache input = some answer ∧
      (result, finalCache) ∈
        support ((simulateQ KeygenUniform.rom (next answer)).run
          (initialCache.cacheQuery input answer)) := by
  rw [simulateQ_bind, show simulateQ KeygenUniform.rom
      (query (spec := OracleWorld) (Sum.inr input)) = KeygenUniform.rom (Sum.inr input)
      from by simp, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨step, hstep, hrest⟩ := hmem
  have hentry : step.2 input = some step.1 := step_cached input initialCache step hstep
  refine ⟨step.1, GrowthCharge.cache_value_persists (next step.1) step.2 finalCache result
    hrest input step.1 hentry, ?_⟩
  have hsame : initialCache.cacheQuery input step.1 = step.2 := by
    cases hcached : initialCache input with
    | some cached =>
      have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
          (pure (cached, initialCache) :
            ProbComp (HashOutput × QueryCache HashSpec)) := by
        change (randomOracle input).run initialCache = _
        rw [QueryImpl.withCaching_run_some _ hcached]
      rw [hrun, support_pure, Set.mem_singleton_iff] at hstep
      subst hstep
      funext probe
      by_cases hprobe : probe = input
      · subst hprobe
        rw [QueryCache.cacheQuery_self]
        exact hcached.symm
      · exact QueryCache.cacheQuery_of_ne initialCache cached hprobe
    | none =>
      have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
          (fun answer => (answer, initialCache.cacheQuery input answer)) <$>
            ($ᵗ HashOutput : ProbComp HashOutput) := by
        change (randomOracle input).run initialCache = _
        rw [QueryImpl.withCaching_run_none _ hcached]
        simp [uniformSampleImpl]
      rw [hrun, support_map] at hstep
      obtain ⟨answer, -, rfl⟩ := hstep
      rfl
  rwa [hsame]

end SlhDsaSecurity.QueryCached
