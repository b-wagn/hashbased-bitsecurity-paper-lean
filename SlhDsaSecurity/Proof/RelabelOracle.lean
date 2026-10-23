import Xmss.Statement.RandomOracleModel

/-!
# Relabeling the random oracle's inputs

A lazy random oracle answers a fresh input with a uniform value, whatever the input is. So
asking every hash query at `π x` instead of at `x`, for a fixed bijection `π`, changes nothing
but which cache entries hold the answers. Running the relabeled computation from a cache is
running the original from that cache read through `π`, and the final caches correspond the same
way (`run_relabel`).

This is the atom of a position-hiding argument. Choose `π` to swap the children of a Merkle node
(its address and the order of its two child values) and the honest tree computed under `π` is
the honest tree with those two subtrees exchanged.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.RelabelOracle

open Xmss.RandomOracleModel

variable {Input Output : Type} [DecidableEq Input] [SampleableType Output]

/-- Each hash query asked at `π` of its input; uniform samples unchanged. -/
def relabel (π : Input ≃ Input) :
    QueryImpl (World Input Output) (OracleComp (World Input Output))
  | .inl coin => query (spec := World Input Output) (.inl coin)
  | .inr input => query (spec := World Input Output) (.inr (π input))

/-- A cache read through `π`. -/
def pull (π : Input ≃ Input) (cache : QueryCache (HashSpec Input Output)) :
    QueryCache (HashSpec Input Output) :=
  fun input => cache (π input)

omit [SampleableType Output] in
theorem pull_cacheQuery (π : Input ≃ Input) (cache : QueryCache (HashSpec Input Output))
    (input : Input) (answer : Output) :
    pull π (cache.cacheQuery (π input) answer) = (pull π cache).cacheQuery input answer := by
  funext probe
  by_cases h : probe = input
  · subst h
    simp [pull, QueryCache.cacheQuery]
  · have h' : π probe ≠ π input := fun heq => h (π.injective heq)
    simp [pull, QueryCache.cacheQuery, h, h']

/-- **The oracle at `π input` is the oracle at `input` on the pulled cache.** -/
theorem randomOracle_pull (π : Input ≃ Input) (input : Input)
    (cache : QueryCache (HashSpec Input Output)) :
    evalDist (Prod.map id (pull π) <$>
        ((randomOracle : QueryImpl (HashSpec Input Output)
          (StateT (QueryCache (HashSpec Input Output)) ProbComp)) (π input)).run cache) =
      evalDist (((randomOracle : QueryImpl (HashSpec Input Output)
          (StateT (QueryCache (HashSpec Input Output)) ProbComp)) input).run (pull π cache)) := by
  rw [randomOracle.apply_eq, randomOracle.apply_eq]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  have hpull : pull π cache input = cache (π input) := rfl
  rw [hpull]
  cases hcache : cache (π input) with
  | some answer => simp
  | none =>
    simp only [StateT.run_bind, liftM, StateT.run_monadLift, StateT.run_modifyGet, bind_assoc,
      pure_bind, map_bind, map_pure, Prod.map, id, pull_cacheQuery]

/-- **One relabeled query is one original query at the pulled cache.** -/
theorem step_relabel (π : Input ≃ Input) (queried : (World Input Output).Domain)
    (cache : QueryCache (HashSpec Input Output)) :
    evalDist (Prod.map id (pull π) <$>
        (simulateQ (impl Input Output) (relabel π queried)).run cache) =
      evalDist ((impl Input Output queried).run (pull π cache)) := by
  rcases queried with coin | input
  · simp only [relabel, impl, QueryImpl.add_apply_inl]
    change evalDist (Prod.map id (pull π) <$> (unifFwdImpl (HashSpec Input Output) coin).run cache) =
      evalDist ((unifFwdImpl (HashSpec Input Output) coin).run (pull π cache))
    simp [unifFwdImpl, QueryImpl.liftTarget, HasQuery.toQueryImpl]
  · have hrun : simulateQ (impl Input Output) (relabel π (.inr input)) =
        ((randomOracle : QueryImpl (HashSpec Input Output)
          (StateT (QueryCache (HashSpec Input Output)) ProbComp)) (π input)) := by
      simp [relabel, impl]
    rw [hrun]
    exact randomOracle_pull π input cache

/-- **Relabeling the oracle's inputs is invisible**: the relabeled run from `cache` has the law
of the original run from `pull π cache`, with final caches related by `pull π`. -/
theorem run_relabel (π : Input ≃ Input) {α : Type}
    (computation : OracleComp (World Input Output) α)
    (cache : QueryCache (HashSpec Input Output)) :
    evalDist (Prod.map id (pull π) <$>
        (simulateQ (impl Input Output) (simulateQ (relabel π) computation)).run cache) =
      evalDist ((simulateQ (impl Input Output) computation).run (pull π cache)) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
    simp
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_bind, simulateQ_bind, simulateQ_spec_query,
      simulateQ_spec_query, StateT.run_bind, StateT.run_bind, map_bind, evalDist_bind,
      evalDist_bind, ← step_relabel π queried cache, evalDist_map, bind_map_left]
    refine congrArg _ (funext fun step => ?_)
    exact ih step.1 step.2

end SlhDsaSecurity.RelabelOracle

