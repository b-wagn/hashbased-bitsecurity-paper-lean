import SlhDsaSecurity.Proof.GrowthCharge
import SlhDsaSecurity.Proof.GraphFreshSampling
import SlhDsaSecurity.Proof.SecretGuessCharge

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

/-! ## The per-step rate: a fixed input is an honest key with probability `2 ^ -128`

This is the quantitative content of the interleaving step, and the hypothesis that
`QueryImpl.Stateful.advantage_le_expectedQuerySlack_plus_probEvent_bad` takes as its
`querySlack`. Everything above is about laws being equal; this is the one place a number
enters.

The argument is the FIPS 205 byte format rather than anything probabilistic. A tweakable input
carries its address in the clear, so the address field of a candidate input already names the
only coordinate it could possibly be the honest input of — `locate` below. Having fixed that
coordinate, the input determines the seed, because `inputOf · node` is injective. So at most
one seed in `2 ^ 128` makes a given input honest, whatever the adversary chose it to be.

Note where the quantifiers sit: the input is fixed *first* and the seed drawn afterwards. That
is legitimate precisely because of `honest_result_indep_of_seed` — the view from which the
adversary picked its input has a law not involving the seed — and it is why the deferral had
to come first. -/

/-- **A fixed query input is an honest key with probability at most `2 ^ -128`.** -/
theorem prob_honest_key_le {Index : Type} (inputOf : Digest → Index → Bytes)
    (locate : Bytes → Option Index)
    (hlocate : ∀ (secret : Digest) (node : Index), locate (inputOf secret node) = some node)
    (hinj : ∀ node : Index, Function.Injective (fun secret : Digest => inputOf secret node))
    (candidate : Bytes) :
    Pr[fun secret : Digest => ∃ node : Index, inputOf secret node = candidate |
      ($ᵗ Digest : ProbComp Digest)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  by_cases hwitness : ∃ (secret : Digest) (node : Index), inputOf secret node = candidate
  · -- Some seed makes it honest; injectivity says no other one does.
    obtain ⟨witness, node, hnode⟩ := hwitness
    refine le_trans (probEvent_mono (α := Digest)
      (q := fun secret : Digest => witness = secret) ?_) ?_
    · rintro secret - ⟨other, hother⟩
      -- The address field pins the coordinate, so `other = node`.
      have hsame : other = node := by
        have hleft : locate candidate = some other := by rw [← hother]; exact hlocate secret other
        have hright : locate candidate = some node := by rw [← hnode]; exact hlocate witness node
        exact Option.some.inj (hleft.symm.trans hright)
      subst hsame
      -- With the coordinate fixed, the input determines the seed.
      exact (hinj other (hother.trans hnode.symm)).symm
    · exact le_of_eq (SecretGuessCharge.prob_single_guess witness)
  · -- No seed makes it honest at all.
    refine le_of_eq_of_le (b := 0) (probEvent_eq_zero fun secret _ hbad => ?_) (by simp)
    exact hwitness ⟨secret, hbad⟩

/-- The same bound stated as the `querySlack` of the identical-until-bad hop: a run that makes
at most `limit` queries meets an honest key with probability at most `limit / 2 ^ 128`. -/
theorem prob_any_honest_key_le {Index : Type} (inputOf : Digest → Index → Bytes)
    (locate : Bytes → Option Index)
    (hlocate : ∀ (secret : Digest) (node : Index), locate (inputOf secret node) = some node)
    (hinj : ∀ node : Index, Function.Injective (fun secret : Digest => inputOf secret node))
    (candidates : Finset Bytes) :
    Pr[fun secret : Digest =>
        ∃ candidate ∈ candidates, ∃ node : Index, inputOf secret node = candidate |
      ($ᵗ Digest : ProbComp Digest)] ≤
      candidates.card / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (probEvent_exists_finset_le_sum candidates _ _) ?_
  calc ∑ candidate ∈ candidates,
        Pr[fun secret : Digest => ∃ node : Index, inputOf secret node = candidate |
          ($ᵗ Digest : ProbComp Digest)]
      ≤ ∑ _candidate ∈ candidates, 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        Finset.sum_le_sum fun candidate _ =>
          prob_honest_key_le inputOf locate hlocate hinj candidate
    _ = candidates.card * (1 / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ candidates.card / ((2 ^ 128 : Nat) : ℝ≥0∞) := le_of_eq (by rw [mul_one_div])

/-! ## The blind side, closed

In the blind game the adversary never sees a seed-derived cache entry, so its run — and hence
the set of inputs it has queried — does not involve the seed at all. Drawing the seed after
that run is then legitimate, and the chance that any queried input is seed-derived is at most
one per query.

Together with `BlindComparison.prob_touched_eq`, which says the real game touches the
seed-derived keys with exactly the same probability as the blind one, this is the input half
of the budget: `q / 2 ^ 128`, with no slack lost to the comparison. -/

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **A seed-independent run meets a seed-derived key with probability at most one per
query.** -/
theorem prob_run_meets_honest_key_le {α Index : Type} (blindRun : ProbComp (α × Finset Bytes))
    (inputOf : Digest → Index → Bytes) (locate : Bytes → Option Index)
    (hlocate : ∀ (secret : Digest) (node : Index), locate (inputOf secret node) = some node)
    (hinj : ∀ node : Index, Function.Injective fun secret : Digest => inputOf secret node)
    (limit : Nat) (hlimit : ∀ result ∈ support blindRun, (result.2).card ≤ limit) :
    Pr[fun pair : (α × Finset Bytes) × Digest =>
        ∃ candidate ∈ pair.1.2, ∃ node : Index, inputOf pair.2 node = candidate |
      (do
        let result ← blindRun
        let secret ← ($ᵗ Digest : ProbComp Digest)
        pure (result, secret))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [probEvent_bind_eq_tsum]
  calc ∑' result, Pr[= result | blindRun] *
        Pr[fun pair : (α × Finset Bytes) × Digest =>
            ∃ candidate ∈ pair.1.2, ∃ node : Index, inputOf pair.2 node = candidate |
          (do
            let secret ← ($ᵗ Digest : ProbComp Digest)
            pure (result, secret))]
      ≤ ∑' result, Pr[= result | blindRun] * (limit / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        refine ENNReal.tsum_le_tsum fun result => ?_
        by_cases hmem : result ∈ support blindRun
        · refine mul_le_mul' le_rfl ?_
          rw [bind_pure_comp, probEvent_map]
          refine le_trans (prob_any_honest_key_le inputOf locate hlocate hinj (result.2)) ?_
          exact ENNReal.div_le_div_right (Nat.cast_le.mpr (hlimit result hmem)) _
        · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
          simp
    _ = (∑' result, Pr[= result | blindRun]) * (limit / ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
        ENNReal.tsum_mul_right
    _ ≤ 1 * (limit / ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
        mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = _ := one_mul _

end SlhDsaSecurity.SeedDeferral
