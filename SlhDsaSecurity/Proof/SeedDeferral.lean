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

end SlhDsaSecurity.SeedDeferral
