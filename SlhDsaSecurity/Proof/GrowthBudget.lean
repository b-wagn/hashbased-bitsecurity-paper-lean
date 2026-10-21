import SlhDsaSecurity.Proof.GrowthCharge
import SlhDsaSecurity.Statement.Security
import SlhDsaSecurity.Proof.VerificationBudget

/-!
# Cache growth is dominated by the total hash count

`GrowthCharge.prob_hitWithin_le` charges a run against its observable cache growth, while
the all-queries-counted experiment bounds the *total* number of hash calls. Repeated calls
are charged but do not grow the cache, so the count always dominates the growth; this file
proves that inequality, which is what lets the charge consume the experiment's budget.

`countAllHashes` only adds bookkeeping to the returned value: it issues exactly the queries
of the underlying computation, in the same order, so the cache evolves identically and the
count is the number of hash queries made. Each new cache entry is created by a hash query,
hence `growth ≤ count`.
-/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.GrowthBudget

open Security GrowthCharge

theorem GrowthAtMost.mono {initial final : QueryCache HashSpec} {limit limit' : Nat}
    (hgrowth : GrowthAtMost initial final limit) (hle : limit ≤ limit') :
    GrowthAtMost initial final limit' :=
  fun inputs hnodup hmembers => (hgrowth inputs hnodup hmembers).trans hle

/-- Removing the freshly installed entry costs one unit of growth budget. -/
theorem growth_of_cacheQuery {initial final : QueryCache HashSpec} {limit : Nat}
    {input : Bytes} {answer : HashOutput}
    (hgrowth : GrowthAtMost (initial.cacheQuery input answer) final limit) :
    GrowthAtMost initial final (limit + 1) := by
  intro inputs hnodup hmembers
  have hshorter : (inputs.erase input).length ≤ limit := by
    refine hgrowth (inputs.erase input) (hnodup.erase input) ?_
    intro i hi
    have hne : i ≠ input := by
      intro hsame
      subst hsame
      exact (hnodup.not_mem_erase) hi
    have hmem : i ∈ inputs := List.mem_of_mem_erase hi
    refine ⟨?_, (hmembers i hmem).2⟩
    rw [QueryCache.cacheQuery_of_ne initial answer hne]
    exact (hmembers i hmem).1
  have hlength : inputs.length ≤ (inputs.erase input).length + 1 := by
    by_cases hmem : input ∈ inputs
    · rw [List.length_erase_of_mem hmem]
      have := List.length_pos_of_mem hmem
      omega
    · rw [List.erase_of_not_mem hmem]
      omega
  omega

@[simp] theorem countAllHashes_pure {α : Type} (value : α) :
    countAllHashes (pure value : OracleComp OracleWorld α) = pure (value, 0) := by
  simp [countAllHashes]

theorem countAllHashes_query_bind {α : Type} (queried : OracleWorld.Domain)
    (next : OracleWorld.Range queried → OracleComp OracleWorld α) :
    countAllHashes (liftM (OracleWorld.query queried) >>= next) =
      liftM (OracleWorld.query queried) >>= fun answer =>
        (fun result => (result.1, hashCost queried + result.2)) <$>
          countAllHashes (next answer) := by
  simp only [countAllHashes, simulateQ_bind, simulateQ_spec_query, addCostOracle,
    QueryImpl.withAddCost, QueryImpl.withCost]
  simp [Functor.map_map, map_bind, bind_map_left]

/-- The total count is additive over sequencing: the count of `c >>= f` splits into the
count of `c` and the count of the continuation. -/
theorem countAllHashes_bind {α β : Type} (computation : OracleComp OracleWorld α)
    (continuation : α → OracleComp OracleWorld β) :
    countAllHashes (computation >>= continuation) =
      (countAllHashes computation >>= fun first =>
        countAllHashes (continuation first.1) >>= fun second =>
          (pure (second.1, first.2 + second.2) :
            OracleComp OracleWorld (β × Nat))) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [countAllHashes_pure]
  | query_bind queried next ih =>
    rw [bind_assoc, countAllHashes_query_bind, countAllHashes_query_bind]
    simp only [ih]
    simp [map_bind, bind_map_left, bind_assoc, Nat.add_assoc]

/-- The `Nat` total count is exactly the `kind` component of the `Counts` counter driven by
the same per-query cost. Every bound already proved about `countQueries` therefore transfers
to the all-queries-counted total. -/
theorem countAllHashes_eq_component {α : Type} (kind : QueryKind)
    (computation : OracleComp OracleWorld α) :
    (fun result : α × Counts => (result.1, result.2 kind)) <$>
        countQueries (fun input => Counts.single kind (hashCost input)) computation =
      countAllHashes computation := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    rw [VerificationBudget.countQueries_pure, countAllHashes_pure, map_pure]
    rfl
  | query_bind queried next ih =>
    rw [VerificationBudget.countQueries_bind, VerificationBudget.countQueries_query,
      countAllHashes_query_bind]
    simp only [map_bind, bind_assoc, pure_bind]
    refine congrArg (fun continuation => liftM (OracleWorld.query queried) >>= continuation) ?_
    funext answer
    rw [← ih answer]
    simp only [map_bind, bind_map_left, Functor.map_map]
    refine congrArg (fun step => countQueries
      (fun input => Counts.single kind (hashCost input)) (next answer) >>= step) ?_
    funext inner
    simp [map_pure, Counts.single, Pi.add_apply, Pi.single_eq_same, Function.comp_def]
    rfl

/-- Every new cache entry is created by a hash query, so growth never exceeds the count. -/
theorem growth_le_count {α : Type} (computation : OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec) (result : (α × Nat) × QueryCache HashSpec)
    (hmem : result ∈
      support ((simulateQ KeygenUniform.rom (countAllHashes computation)).run initialCache)) :
    GrowthAtMost initialCache result.2 result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
    rw [countAllHashes_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    subst hmem
    intro inputs _ hmembers
    cases inputs with
    | nil => simp
    | cons input rest =>
      obtain ⟨hnone, hsome⟩ := hmembers input (by simp)
      exact absurd hnone hsome
  | query_bind queried next ih =>
    rw [countAllHashes_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨⟨answer, middleCache⟩, hquery, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    have hgrowth := ih answer middleCache inner hinner
    have hfinal : result.2 = inner.2 := by rw [← heq]
    have hcount : result.1.2 = hashCost queried + inner.1.2 := by rw [← heq]
    rcases queried with coin | input
    · -- A uniform coin costs nothing and leaves the cache alone.
      have hcache : middleCache = initialCache := by
        symm
        simpa [KeygenUniform.rom, XmssSecurity.RandomOracleModel.impl, unifFwdImpl] using hquery
      subst hcache
      rw [hfinal, hcount]
      simpa [hashCost, XmssSecurity.RandomOracleModel.hashCost] using hgrowth
    · -- A hash call costs one and installs at most one entry.
      have hcost : hashCost (Sum.inr input) = 1 := rfl
      rw [hfinal, hcount, hcost]
      change (answer, middleCache) ∈ support ((randomOracle input).run initialCache) at hquery
      cases hcached : initialCache input with
      | some cached =>
        rw [QueryImpl.withCaching_run_some _ hcached, support_pure,
          Set.mem_singleton_iff] at hquery
        have hcache : middleCache = initialCache := (Prod.ext_iff.mp hquery).2
        subst hcache
        exact GrowthAtMost.mono hgrowth (by omega)
      | none =>
        rw [QueryImpl.withCaching_run_none _ hcached, support_map] at hquery
        obtain ⟨sampled, _, hpair⟩ := hquery
        have hcache : middleCache = initialCache.cacheQuery input sampled :=
          (Prod.ext_iff.mp hpair).2.symm
        subst hcache
        rw [Nat.add_comm]
        exact growth_of_cacheQuery hgrowth

end SlhDsaSecurity.GrowthBudget
