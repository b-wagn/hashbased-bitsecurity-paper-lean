import SlhDsaSecurity.Proof.CacheReplay
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Pre-sampling an unused oracle entry is free

Every charge is parameterised by the honest cells, but the experiment samples the seeds — and
so determines the cells — inside the run. Closing that needs the experiment rewritten as
*sample a cell table, then program the oracle from it*, which is what
`CanonicalGraph.Programming` does for key generation.

The step that lets such a rewrite be prepended to a run at all is below: filling a cache entry
that is currently empty, with a uniform value, does not change the law of whatever runs next.
In the lazy random-oracle model this is intuitively obvious — the entry would have been
sampled with the same law on first use, and never used entries are never observed — but it is
exactly the fact a presampling argument needs, and VCVio does not carry it.

`evalDist_prepend_fresh` is that statement. Note the `Prod.fst`: the two runs end with
*different caches*, since one has an extra entry, so only the value can be compared. That is
all any later step needs, because the caches agree wherever the entry is not involved.
-/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.Presample

/-- Writing two different keys commutes. -/
theorem cacheQuery_comm (cache : QueryCache HashSpec) {left right : Bytes}
    (hne : left ≠ right) (leftValue rightValue : HashOutput) :
    (cache.cacheQuery left leftValue).cacheQuery right rightValue =
      (cache.cacheQuery right rightValue).cacheQuery left leftValue := by
  simp only [QueryCache.cacheQuery]
  exact Function.update_comm hne _ _ _

/-- **Filling a fresh entry with a uniform value does not change what follows.** -/
theorem evalDist_prepend_fresh {α : Type} (computation : OracleComp HashSpec α) :
    ∀ (cache : QueryCache HashSpec) (target : Bytes), cache target = none →
      𝒟[Prod.fst <$> (simulateQ randomOracle computation).run cache] =
        𝒟[(do
          let value ← ($ᵗ HashOutput : ProbComp HashOutput)
          Prod.fst <$> (simulateQ randomOracle computation).run
            (cache.cacheQuery target value))] := by
  induction computation using OracleComp.inductionOn with
  | pure result =>
    intro cache target _
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _).symm
  | query_bind input next ih =>
    intro cache target hfresh
    simp only [simulateQ_bind, show simulateQ randomOracle
        (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) = randomOracle input
      from by simp, StateT.run_bind]
    by_cases hsame : input = target
    · subst hsame
      rw [QueryImpl.withCaching_run_none _ hfresh]
      simp only [uniformSampleImpl, bind_map_left, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind]
      refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ (fun value => ?_)
      rw [QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self cache input value),
        pure_bind]
    · cases hlookup : cache input with
      | some cached =>
        rw [QueryImpl.withCaching_run_some _ hlookup, pure_bind]
        refine (ih cached cache target hfresh).trans
          (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ (fun value => ?_))
        rw [QueryImpl.withCaching_run_some _
          (by rw [QueryCache.cacheQuery_of_ne cache value hsame]; exact hlookup), pure_bind]
      | none =>
        rw [QueryImpl.withCaching_run_none _ hlookup]
        simp only [uniformSampleImpl, bind_map_left, map_eq_bind_pure_comp, Function.comp_def,
          bind_assoc, pure_bind]
        have hinner : ∀ value : HashOutput,
            𝒟[Prod.fst <$> (simulateQ randomOracle (next value)).run
                (cache.cacheQuery input value)] =
              𝒟[(do
                let extra ← ($ᵗ HashOutput : ProbComp HashOutput)
                Prod.fst <$> (simulateQ randomOracle (next value)).run
                  ((cache.cacheQuery input value).cacheQuery target extra))] :=
          fun value => ih value (cache.cacheQuery input value) target
            (by rw [QueryCache.cacheQuery_of_ne cache value (Ne.symm hsame)]; exact hfresh)
        refine (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ hinner).trans ?_
        refine (OracleComp.DeferredSampling.evalDist_bind_comm _ _ _).trans ?_
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ (fun extra => ?_)
        rw [QueryImpl.withCaching_run_none _
          (by rw [QueryCache.cacheQuery_of_ne cache extra hsame]; exact hlookup)]
        simp only [uniformSampleImpl, bind_map_left, map_eq_bind_pure_comp, Function.comp_def,
          bind_assoc, pure_bind, cacheQuery_comm cache hsame]

/-! ## Pre-sampling a whole table

Iterating the step over a duplicate-free list of inputs that are all still empty: the entire
table may be drawn before the run instead of during it. `CanonicalGraph.Programming.order` is
such a list — it is `Nodup` by `order_nodup` — so this is what fixes the honest cells ahead of
the adversary, which is what every charge is parameterised by. -/

/-- Draw a uniform value for each input in turn and write it into the cache. -/
noncomputable def prefill : List Bytes → QueryCache HashSpec → ProbComp (QueryCache HashSpec)
  | [], cache => pure cache
  | target :: rest, cache => do
      let value ← ($ᵗ HashOutput : ProbComp HashOutput)
      prefill rest (cache.cacheQuery target value)

/-- **A whole table of unused entries may be pre-sampled.** -/
theorem evalDist_prefill {α : Type} (computation : OracleComp HashSpec α) :
    ∀ (targets : List Bytes) (cache : QueryCache HashSpec), targets.Nodup →
      (∀ target ∈ targets, cache target = none) →
      𝒟[Prod.fst <$> (simulateQ randomOracle computation).run cache] =
        𝒟[(do
          let filled ← prefill targets cache
          Prod.fst <$> (simulateQ randomOracle computation).run filled)] := by
  intro targets
  induction targets with
  | nil => intro cache _ _; rw [prefill, pure_bind]
  | cons target rest ih =>
    intro cache hnodup hfresh
    have hnotMem : target ∉ rest := (List.nodup_cons.mp hnodup).1
    have hrest : rest.Nodup := (List.nodup_cons.mp hnodup).2
    rw [prefill, bind_assoc]
    refine (evalDist_prepend_fresh computation cache target
      (hfresh target (by simp))).trans ?_
    refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ (fun value => ?_)
    refine ih (cache.cacheQuery target value) hrest (fun probe hprobe => ?_)
    have hne : probe ≠ target := fun hsame => hnotMem (hsame ▸ hprobe)
    rw [QueryCache.cacheQuery_of_ne cache value hne]
    exact hfresh probe (by simp [hprobe])

end SlhDsaSecurity.Presample
