import SlhDsaSecurity.Proof.GrowthCharge
import SlhDsaSecurity.Proof.GraphFreshSampling

/-!
# Deferring the seed sample past a seed-derived query

This is the atom of the one step still missing from the input-side charge: the equality
between the experiment that samples the secret seed eagerly at key generation and the one
that samples it lazily, only when something actually needs its value.

The reason such a deferral is available at all is local and does not mention the adversary.
Every use the honest parties make of the seed is as *query-input bytes* — `SK.seed` appears
only inside `PK.seed ‖ ADRS ‖ SK.seed` — and a random oracle's answer at a fresh input is a
uniform value whatever the input is. So the answer can be drawn first and the seed afterwards:
the pair has the same law either way. That is `seed_query_comm` below.

What this does *not* do is iterate the move along a whole execution. The honest computation
makes many seed-derived queries, the adversary interleaves its own, and carrying the deferral
through all of them is what `QueryImpl.Stateful.advantage_le_expectedQuerySlack_plus_probEvent_bad`
would consume. The freshness hypothesis is where that difficulty is concentrated: here it is
assumed, and in the full argument it is exactly the event being charged, since the one way the
seed-derived input can fail to be fresh is that someone has already queried it.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.SeedDeferral

/-- **The seed sample commutes past the query it parameterises.** Querying a seed-derived
input at a cache where that input is fresh, and then continuing, has the same law as drawing
the answer first and the seed afterwards. -/
theorem seed_query_comm {β : Type} (inputOf : Digest → Bytes) (cache : QueryCache HashSpec)
    (hfresh : ∀ secret : Digest, cache (inputOf secret) = none)
    (rest : HashOutput → Digest → QueryCache HashSpec → ProbComp β) :
    𝒟[(do
        let secret ← ($ᵗ Digest : ProbComp Digest)
        let step ← (KeygenUniform.rom (Sum.inr (inputOf secret))).run cache
        rest step.1 secret step.2)] =
      𝒟[(do
        let answer ← ($ᵗ HashOutput : ProbComp HashOutput)
        let secret ← ($ᵗ Digest : ProbComp Digest)
        rest answer secret (cache.cacheQuery (inputOf secret) answer))] := by
  have hrun : ∀ secret : Digest,
      (KeygenUniform.rom (Sum.inr (inputOf secret))).run cache =
        (fun answer => (answer, cache.cacheQuery (inputOf secret) answer)) <$>
          ($ᵗ HashOutput : ProbComp HashOutput) := by
    intro secret
    change (randomOracle (inputOf secret)).run cache = _
    rw [QueryImpl.withCaching_run_none _ (hfresh secret)]
    simp [uniformSampleImpl]
  simp only [hrun, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _

/-- The same statement with the continuation ignoring the cache, which is the shape a
transcript-level argument uses: the seed is drawn after everything the adversary sees. -/
theorem seed_query_comm_transcript {β : Type} (inputOf : Digest → Bytes)
    (cache : QueryCache HashSpec) (hfresh : ∀ secret : Digest, cache (inputOf secret) = none)
    (rest : HashOutput → Digest → ProbComp β) :
    𝒟[(do
        let secret ← ($ᵗ Digest : ProbComp Digest)
        let step ← (KeygenUniform.rom (Sum.inr (inputOf secret))).run cache
        rest step.1 secret)] =
      𝒟[(do
        let answer ← ($ᵗ HashOutput : ProbComp HashOutput)
        let secret ← ($ᵗ Digest : ProbComp Digest)
        rest answer secret)] :=
  seed_query_comm inputOf cache hfresh (fun answer secret _ => rest answer secret)

/-- **The transcript is independent of the seed, one query deep.** Specialising the
continuation to one that does not read the seed: what the adversary learns from a single
seed-derived query has a law that does not involve the seed at all. -/
theorem transcript_indep_of_seed {β : Type} (inputOf : Digest → Bytes)
    (cache : QueryCache HashSpec) (hfresh : ∀ secret : Digest, cache (inputOf secret) = none)
    (view : HashOutput → ProbComp β) :
    𝒟[(do
        let secret ← ($ᵗ Digest : ProbComp Digest)
        let step ← (KeygenUniform.rom (Sum.inr (inputOf secret))).run cache
        view step.1)] =
      𝒟[(do
        let answer ← ($ᵗ HashOutput : ProbComp HashOutput)
        view answer)] := by
  refine (seed_query_comm_transcript inputOf cache hfresh (fun answer _ => view answer)).trans ?_
  refine OracleComp.DeferredSampling.evalDist_bind_congr_left _ _ _ fun answer => ?_
  exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _

/-! ## The honest transcript does not depend on the seed

The single-query move iterates, and `GraphFreshSampling.evaluate_eq_sample` already supplies
the iteration: along a duplicate-free list of separated, fresh coordinates, the real run of a
traversal equals `sample`, which draws one independent uniform answer per coordinate.

The observation that makes this decide the question is visible in `sample`'s definition. Its
state evolves by `step node state output` — the seed-derived byte input appears *only* in the
cache key `cache.cacheQuery (input node state) output`, never in the state. So the traversal's
result is built from the fresh answers alone, and changing the inputs cannot change it. The
two lemmas below say exactly that, and as literal equalities of computations rather than
merely of distributions.

This is the honest half of step 1: whatever the honest parties compute from the seed, what
they hand back is distributed identically for every seed. What is still not covered is the
adversary's interleaved queries, which share the cache and can therefore see the one thing
that does depend on the seed — which keys are present. That is the bad event, and bounding it
is what the identical-until-bad hop does. -/

open GraphFreshSampling

/-- **The sampled traversal's result does not depend on the byte inputs.** They enter only as
cache keys, so two input families give the same result computation. -/
theorem sample_fst_eq {Index State : Type} (input input' : Index → State → Bytes)
    (step : Index → State → HashOutput → State) (nodes : List Index) (state : State)
    (cache cache' : QueryCache HashSpec) :
    Prod.fst <$> sample input step nodes state cache =
      Prod.fst <$> sample input' step nodes state cache' := by
  induction nodes generalizing state cache cache' with
  | nil => simp [sample]
  | cons node nodes ih =>
    simp only [sample, map_bind]
    exact congrArg (Bind.bind ($ᵗ HashOutput : ProbComp HashOutput))
      (funext fun output => ih (step node state output) _ _)

/-- **The honest transcript is independent of the secret seed.** Running a traversal whose
byte inputs are derived from one seed returns the same computation as running it with any
other seed, provided the coordinates are separated and fresh for both. -/
theorem honest_result_indep_of_seed {Index State : Type}
    (inputOf : Digest → Index → State → Bytes)
    (step : Index → State → HashOutput → State) (nodes : List Index) (hnodup : nodes.Nodup)
    (state : State) (cache : QueryCache HashSpec)
    (hseparated : ∀ secret : Digest, Separated (inputOf secret))
    (hfresh : ∀ secret : Digest, FreshFor (inputOf secret) nodes cache)
    (secret secret' : Digest) :
    Prod.fst <$>
        (simulateQ randomOracle (evaluate (inputOf secret) step nodes state)).run cache =
      Prod.fst <$>
        (simulateQ randomOracle (evaluate (inputOf secret') step nodes state)).run cache := by
  rw [evaluate_eq_sample (inputOf secret) step (hseparated secret) nodes hnodup state cache
      (hfresh secret),
    evaluate_eq_sample (inputOf secret') step (hseparated secret') nodes hnodup state cache
      (hfresh secret')]
  exact sample_fst_eq _ _ step nodes state cache cache

/-- The distributional form: the seed may be drawn after the honest traversal has run. -/
theorem honest_result_defer_seed {Index State β : Type}
    (inputOf : Digest → Index → State → Bytes)
    (step : Index → State → HashOutput → State) (nodes : List Index) (hnodup : nodes.Nodup)
    (state : State) (cache : QueryCache HashSpec)
    (hseparated : ∀ secret : Digest, Separated (inputOf secret))
    (hfresh : ∀ secret : Digest, FreshFor (inputOf secret) nodes cache)
    (reference : Digest) (view : State → Digest → ProbComp β) :
    𝒟[(do
        let secret ← ($ᵗ Digest : ProbComp Digest)
        let result ←
          (simulateQ randomOracle (evaluate (inputOf secret) step nodes state)).run cache
        view result.1 secret)] =
      𝒟[(do
        let transcript ←
          Prod.fst <$>
            (simulateQ randomOracle (evaluate (inputOf reference) step nodes state)).run cache
        let secret ← ($ᵗ Digest : ProbComp Digest)
        view transcript secret)] := by
  have hrewrite : ∀ secret : Digest,
      (do
        let result ←
          (simulateQ randomOracle (evaluate (inputOf secret) step nodes state)).run cache
        view result.1 secret) =
      (do
        let transcript ←
          Prod.fst <$>
            (simulateQ randomOracle (evaluate (inputOf reference) step nodes state)).run cache
        view transcript secret) := by
    intro secret
    rw [← honest_result_indep_of_seed inputOf step nodes hnodup state cache hseparated hfresh
      secret reference]
    rw [map_eq_bind_pure_comp, bind_assoc]
    simp only [Function.comp_def, pure_bind]
  simp only [hrewrite]
  exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _

end SlhDsaSecurity.SeedDeferral
