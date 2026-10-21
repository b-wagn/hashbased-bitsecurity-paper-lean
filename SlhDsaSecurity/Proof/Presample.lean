import SlhDsaSecurity.Proof.CacheReplay
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import SlhDsaSecurity.Proof.GraphFreshSampling
import SlhDsaSecurity.Proof.CanonicalGraph.Programming

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

/-! ## Prepending a traversal

`prefill` draws a fixed list of entries, but the honest parties' queries are not a fixed list:
each node's byte input is built from its children's cells, so it depends on the answers given
earlier. That is why `CanonicalGraph.Programming.warmup` is a traversal rather than a flat
table write.

Prepending such a traversal is still free, and for the same reason: each of its queries lands
on an input that is still empty, so by `evalDist_prepend_fresh` the value it draws could have
been drawn in advance. The difference from `evalDist_prefill` is that the next input is chosen
using the value just drawn, so the induction peels one query at a time rather than quantifying
over a list of targets fixed up front.

With this, the experiment may be rewritten as *traverse the graph, then run* — and
`GraphFreshSampling.evalDist_evaluate_eq_uniform_program` turns that traversal into a uniform
table and a programmed cache, which is what fixes the honest cells ahead of the adversary. -/

theorem evalDist_prepend_evaluate {α State Index : Type}
    (computation : OracleComp HashSpec α) (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State)
    (hseparated : GraphFreshSampling.Separated input) :
    ∀ (nodes : List Index) (state : State) (cache : QueryCache HashSpec), nodes.Nodup →
      GraphFreshSampling.FreshFor input nodes cache →
      𝒟[Prod.fst <$> (simulateQ randomOracle computation).run cache] =
        𝒟[Prod.fst <$> (simulateQ randomOracle
          (GraphFreshSampling.evaluate input step nodes state >>= fun _ => computation)).run
            cache] := by
  intro nodes
  induction nodes with
  | nil =>
    intro state cache _ _
    rw [GraphFreshSampling.evaluate, pure_bind]
  | cons node rest ih =>
    intro state cache hnodup hfresh
    have hnotMem : node ∉ rest := (List.nodup_cons.mp hnodup).1
    have hrest : rest.Nodup := (List.nodup_cons.mp hnodup).2
    have hhead : cache (input node state) = none := hfresh node (by simp) state
    refine (evalDist_prepend_fresh computation cache (input node state) hhead).trans ?_
    have hstep : ∀ value : HashOutput,
        𝒟[Prod.fst <$> (simulateQ randomOracle computation).run
            (cache.cacheQuery (input node state) value)] =
          𝒟[Prod.fst <$> (simulateQ randomOracle
            (GraphFreshSampling.evaluate input step rest (step node state value) >>=
              fun _ => computation)).run (cache.cacheQuery (input node state) value)] := by
      intro value
      refine ih (step node state value) (cache.cacheQuery (input node state) value) hrest ?_
      intro other hother otherState
      rw [QueryCache.cacheQuery_of_ne cache value
        (hseparated other node (fun hsame => hnotMem (hsame ▸ hother)) otherState state)]
      exact hfresh other (by simp [hother]) otherState
    refine (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ hstep).trans ?_
    rw [GraphFreshSampling.evaluate, bind_assoc]
    simp only [simulateQ_bind, show simulateQ randomOracle
        (liftM (HashSpec.query (input node state)) : OracleComp HashSpec HashOutput) =
      randomOracle (input node state) from by simp, StateT.run_bind]
    rw [QueryImpl.withCaching_run_none _ hhead]
    simp only [uniformSampleImpl, bind_map_left, map_eq_bind_pure_comp, Function.comp_def,
      bind_assoc, pure_bind]

/-! ## The same, in the game's oracle world

The experiment is `OracleComp OracleWorld` — hash calls and coin flips together — so the step
has to be available there too. A coin flip does not touch the hash cache, so it commutes with
the prepended draw exactly as a hash query at a different input does; that is the only new
case.

One detail decides whether this goes through. The prepended draw puts the right-hand side
under a binder, and `rw` does not rewrite under binders: unfolding the query step with `rw`
rewrites only the left, after which the two sides no longer match and every later step fails
on a `Range` mismatch that is really just the untouched side. Using `simp only` for that first
unfolding, which does go under binders, removes the whole difficulty. -/

theorem evalDist_prepend_fresh_world {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (cache : QueryCache HashSpec) (target : Bytes), cache target = none →
      𝒟[Prod.fst <$> (simulateQ KeygenUniform.rom computation).run cache] =
        𝒟[(do
          let value ← ($ᵗ HashOutput : ProbComp HashOutput)
          Prod.fst <$> (simulateQ KeygenUniform.rom computation).run
            (cache.cacheQuery target value))] := by
  induction computation using OracleComp.inductionOn with
  | pure result =>
    intro cache target _
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _).symm
  | query_bind queried next ih =>
    intro cache target hfresh
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rcases queried with coin | input
    · have hcoin : ∀ probe : QueryCache HashSpec,
          (KeygenUniform.rom (Sum.inl coin)).run probe =
            (fun value => (value, probe)) <$>
              ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) := fun _ => rfl
      simp only [hcoin, bind_map_left]
      refine (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
        (fun value => ih value cache target hfresh)).trans ?_
      exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    · have hmissAt : ∀ probe : QueryCache HashSpec, probe input = none →
          (KeygenUniform.rom (Sum.inr input)).run probe =
            (fun value => (value, probe.cacheQuery input value)) <$>
              ($ᵗ (OracleWorld.Range (Sum.inr input)) : ProbComp _) := by
        intro probe hprobe
        change (randomOracle input).run probe = _
        rw [QueryImpl.withCaching_run_none _ hprobe]
        simp [uniformSampleImpl]
      have hhitAt : ∀ (probe : QueryCache HashSpec)
          (value : OracleWorld.Range (Sum.inr input)), probe input = some value →
          (KeygenUniform.rom (Sum.inr input)).run probe = pure (value, probe) := by
        intro probe value hprobe
        change (randomOracle input).run probe = _
        rw [QueryImpl.withCaching_run_some _ hprobe]
      by_cases hsame : input = target
      · subst hsame
        simp only [hmissAt cache hfresh, bind_map_left]
        refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ (fun value => ?_)
        simp only [hhitAt (cache.cacheQuery input value) value
          (QueryCache.cacheQuery_self cache input value), pure_bind]
      · cases hlookup : cache input with
        | some cached =>
          simp only [hhitAt cache cached hlookup, pure_bind]
          refine (ih cached cache target hfresh).trans
            (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ (fun value => ?_))
          simp only [hhitAt (cache.cacheQuery target value) cached
            (by rw [QueryCache.cacheQuery_of_ne cache value hsame]; exact hlookup), pure_bind]
        | none =>
          simp only [hmissAt cache hlookup, bind_map_left]
          refine (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _
            (fun value => ih value (cache.cacheQuery input value) target
              (by rw [QueryCache.cacheQuery_of_ne cache value (Ne.symm hsame)];
                  exact hfresh))).trans ?_
          refine (OracleComp.DeferredSampling.evalDist_bind_comm _ _ _).trans ?_
          refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ (fun extra => ?_)
          simp only [hmissAt (cache.cacheQuery target extra)
            (by rw [QueryCache.cacheQuery_of_ne cache extra hsame]; exact hlookup),
            bind_map_left, cacheQuery_comm cache hsame]
          rfl

/-! ## Prepending a traversal, in the game's world

The honest parties' queries form an adaptive traversal: each node's byte input is built from
its children's cells, so it depends on answers given earlier. `worldEvaluate` is that traversal
in the experiment's own monad, and prepending it is free for the same reason prepending one
entry is — each query lands on an input still empty — with the induction peeling one query at
a time because the next input is chosen using the value just drawn. -/

/-- The graph traversal, in the experiment's oracle world. -/
noncomputable def worldEvaluate {State Index : Type} (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State) :
    List Index → State → OracleComp OracleWorld State
  | [], state => pure state
  | node :: nodes, state => do
      let output ← (query (spec := OracleWorld) (Sum.inr (input node state)) :
        OracleComp OracleWorld HashOutput)
      worldEvaluate input step nodes (step node state output)

theorem evalDist_prepend_worldEvaluate {α State Index : Type}
    (computation : OracleComp OracleWorld α) (input : Index → State → Bytes)
    (step : Index → State → HashOutput → State)
    (hseparated : GraphFreshSampling.Separated input) :
    ∀ (nodes : List Index) (state : State) (cache : QueryCache HashSpec), nodes.Nodup →
      GraphFreshSampling.FreshFor input nodes cache →
      𝒟[Prod.fst <$> (simulateQ KeygenUniform.rom computation).run cache] =
        𝒟[Prod.fst <$> (simulateQ KeygenUniform.rom
          (worldEvaluate input step nodes state >>= fun _ => computation)).run cache] := by
  intro nodes
  induction nodes with
  | nil =>
    intro state cache _ _
    rw [worldEvaluate, pure_bind]
  | cons node rest ih =>
    intro state cache hnodup hfresh
    have hnotMem : node ∉ rest := (List.nodup_cons.mp hnodup).1
    have hrest : rest.Nodup := (List.nodup_cons.mp hnodup).2
    have hhead : cache (input node state) = none := hfresh node (by simp) state
    refine (evalDist_prepend_fresh_world computation cache (input node state) hhead).trans ?_
    have hstep : ∀ value : HashOutput,
        𝒟[Prod.fst <$> (simulateQ KeygenUniform.rom computation).run
            (cache.cacheQuery (input node state) value)] =
          𝒟[Prod.fst <$> (simulateQ KeygenUniform.rom
            (worldEvaluate input step rest (step node state value) >>=
              fun _ => computation)).run (cache.cacheQuery (input node state) value)] := by
      intro value
      refine ih (step node state value) (cache.cacheQuery (input node state) value) hrest ?_
      intro other hother otherState
      rw [QueryCache.cacheQuery_of_ne cache value
        (hseparated other node (fun hsame => hnotMem (hsame ▸ hother)) otherState state)]
      exact hfresh other (by simp [hother]) otherState
    refine (OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ hstep).trans ?_
    have hmiss : (KeygenUniform.rom (Sum.inr (input node state))).run cache =
        (fun value => (value, cache.cacheQuery (input node state) value)) <$>
          ($ᵗ (OracleWorld.Range (Sum.inr (input node state))) : ProbComp _) := by
      change (randomOracle (input node state)).run cache = _
      rw [QueryImpl.withCaching_run_none _ hhead]
      simp [uniformSampleImpl]
    have hsim : simulateQ KeygenUniform.rom
        (query (spec := OracleWorld) (Sum.inr (input node state))) =
        KeygenUniform.rom (Sum.inr (input node state)) := by simp
    simp only [worldEvaluate, bind_assoc, simulateQ_bind, hsim,
      StateT.run_bind, map_bind, hmiss, bind_map_left]
    rfl

/-! ## Prepending the warmup

The traversal the experiment's honest parties perform is
`CanonicalGraph.Programming.warmup`, whose coordinates are the structural nodes in rank order.
Every hypothesis of `evalDist_prepend_worldEvaluate` is available for it: the order is
duplicate-free (`order_nodup`), distinct nodes have distinct byte inputs
(`input_separated`), and from the empty cache every input is of course still empty.

So the warmup may be prepended to any computation of the game's world for free — which is what
fixes the honest cells before the adversary runs, since
`GraphFreshSampling.evalDist_evaluate_eq_uniform_program` then turns that traversal into a
uniform table and a programmed cache. -/

/-- The warmup traversal, in the experiment's oracle world. -/
noncomputable def worldWarmup (publicSeed secretSeed : Digest) :
    OracleComp OracleWorld CanonicalGraph.Cells :=
  worldEvaluate (CanonicalGraph.Programming.input publicSeed)
    CanonicalGraph.Programming.assign CanonicalGraph.Programming.order
    (CanonicalGraph.Programming.initialCells secretSeed)

/-- **The warmup may be prepended to any run from the empty cache.** -/
theorem evalDist_prepend_warmup {α : Type} (computation : OracleComp OracleWorld α)
    (publicSeed secretSeed : Digest) :
    𝒟[Prod.fst <$> (simulateQ KeygenUniform.rom computation).run ∅] =
      𝒟[Prod.fst <$> (simulateQ KeygenUniform.rom
        (worldWarmup publicSeed secretSeed >>= fun _ => computation)).run ∅] :=
  evalDist_prepend_worldEvaluate computation _ _
    (CanonicalGraph.Programming.input_separated publicSeed)
    CanonicalGraph.Programming.order
    (CanonicalGraph.Programming.initialCells secretSeed) ∅
    CanonicalGraph.Programming.order_nodup (fun _ _ _ => rfl)

/-! ## Inserting the warmup after the seeds

The experiment does not begin with hash calls: it begins by sampling the three seeds, which
are coin queries. The warmup can only be written down once those seeds exist, so it has to be
inserted *after* them rather than prepended to the whole run.

That is sound because coin queries leave the hash cache alone — `run_liftM_probComp` — so the
run still meets the warmup with an empty cache, which is what `evalDist_prepend_warmup`
requires. -/

/-- Simulating a purely-sampling computation leaves the hash cache untouched.

`rom` is `unifFwdImpl + randomOracle`, so a left-lifted computation simulates through the
left component alone (`simulateQ_add_liftM_left`), and that component never writes to the
cache. -/
theorem run_liftM_probComp {γ : Type} (sample : ProbComp γ) (cache : QueryCache HashSpec) :
    (simulateQ KeygenUniform.rom (liftM sample : OracleComp OracleWorld γ)).run cache =
      (fun value => (value, cache)) <$> sample := by
  rw [show KeygenUniform.rom = unifFwdImpl HashSpec + (randomOracle :
      QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) from rfl,
    QueryImpl.simulateQ_add_liftM_left]
  induction sample using OracleComp.inductionOn generalizing cache with
  | pure value => simp [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind coin next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, ih,
      map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    rfl

/-- **The warmup may be inserted after the seeds are sampled.** -/
theorem evalDist_prepend_warmup_after {α γ : Type} (sample : ProbComp γ)
    (rest : γ → OracleComp OracleWorld α) (publicSeed secretSeed : γ → Digest) :
    𝒟[Prod.fst <$> (simulateQ KeygenUniform.rom
        ((liftM sample : OracleComp OracleWorld γ) >>= rest)).run ∅] =
      𝒟[Prod.fst <$> (simulateQ KeygenUniform.rom
        ((liftM sample : OracleComp OracleWorld γ) >>= fun value =>
          worldWarmup (publicSeed value) (secretSeed value) >>= fun _ => rest value)).run ∅] := by
  simp only [simulateQ_bind, StateT.run_bind, map_bind, run_liftM_probComp, bind_map_left]
  refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ (fun value => ?_)
  simpa only [simulateQ_bind, StateT.run_bind, map_bind] using
    evalDist_prepend_warmup (rest value) (publicSeed value) (secretSeed value)

end SlhDsaSecurity.Presample
