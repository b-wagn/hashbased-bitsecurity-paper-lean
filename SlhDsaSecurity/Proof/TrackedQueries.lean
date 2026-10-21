import SlhDsaSecurity.Proof.GrowthCharge
import SlhDsaSecurity.Proof.BlindComparison
import SlhDsaSecurity.Proof.SeedDeferral

/-!
# Carrying the queried set alongside the count

The input half's blind bound, `SeedDeferral.prob_run_meets_honest_key_le`, consumes a
`Finset Bytes` of inputs the run has queried, together with a cap on its size. The flag that
`BlindComparison.tagged` carries is a function of that set but does not determine it, so the
set has to be carried explicitly.

It has to be carried *with the count*, and that is the point of this file. The obvious bound —
the set is no bigger than the cache grew — is **false** here: the blind run starts from a cache
already programmed at every non-seed-bearing canonical input, so a query answered out of that
cache enlarges the set while leaving the cache exactly as it was. What does bound the set is
the charged query count, since all-queries accounting charges repeats and cache hits alike.

So the oracle below carries both, and `card_le_count` is the invariant that makes the cap
available.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.TrackedQueries

/-- The state: the cache, the inputs queried so far, and how many queries were charged. -/
abbrev State := QueryCache HashSpec × Finset Bytes × Nat

open scoped Classical in
/-- The random oracle, recording each hash input and charging it. -/
noncomputable def tracked : QueryImpl OracleWorld (StateT State ProbComp) :=
  fun queried state =>
    match queried with
    | Sum.inl coin => do
        let value ← ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _)
        pure (value, state)
    | Sum.inr input => do
        let step ← (randomOracle input).run state.1
        pure (step.1, (step.2, insert input state.2.1, state.2.2 + 1))

/-- **The queried set is never larger than the charged count.** -/
theorem card_le_count {α : Type} (computation : OracleComp OracleWorld α)
    (initial : State) (result : α × State)
    (hmem : result ∈ support ((simulateQ tracked computation).run initial))
    (hstart : initial.2.1.card ≤ initial.2.2) :
    result.2.2.1.card ≤ result.2.2.2 := by
  classical
  induction computation using OracleComp.inductionOn generalizing initial result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hstart
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine ih step.1 step.2 result hrest ?_
    rcases queried with coin | input
    · have hsame : step.2 = initial := by
        have hform : ∃ value, (value, initial) = step := by
          simpa [tracked, StateT.run] using hstep
        obtain ⟨value, hpair⟩ := hform
        exact (congrArg Prod.snd hpair).symm
      rw [hsame]
      exact hstart
    · have hshape : ∃ answer cache,
          step.2 = (cache, insert input initial.2.1, initial.2.2 + 1) ∧ step.1 = answer := by
        have hcopy := hstep
        simp only [tracked, StateT.run] at hcopy
        rw [mem_support_bind_iff] at hcopy
        obtain ⟨inner, -, hinner⟩ := hcopy
        rw [support_pure, Set.mem_singleton_iff] at hinner
        exact ⟨inner.1, inner.2, congrArg Prod.snd hinner, congrArg Prod.fst hinner⟩
      obtain ⟨answer, cache, hstate, -⟩ := hshape
      rw [hstate]
      exact le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ hstart)

/-! ## The exact comparison, over this oracle

`BlindComparison.prob_touched_eq` is stated over the flag-carrying oracle. The same statement
and the same proof hold here, with "the flag is set" replaced by "the queried set meets `S`",
and that is the form the input half needs — because the set is what the blind bound consumes.

The two cases are unchanged. At a query inside `S` both runs add that input, so both have met
`S` whatever happens next; at a query outside it the two caches agree at that very input, so
the answer distribution is the same and the agreement survives. -/

/-- The queried set has met `S`. -/
def Meets (S : Bytes → Prop) (state : State) : Prop := ∃ input ∈ state.2.1, S input

/-- The queried set only grows. -/
theorem subset_of_run {α : Type} (computation : OracleComp OracleWorld α)
    (initial : State) (result : α × State)
    (hmem : result ∈ support ((simulateQ tracked computation).run initial)) :
    initial.2.1 ⊆ result.2.2.1 := by
  classical
  induction computation using OracleComp.inductionOn generalizing initial result with
  | pure value =>
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    rw [hmem]
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    refine subset_trans ?_ (ih step.1 step.2 result hrest)
    rcases queried with coin | input
    · have hsame : step.2 = initial := by
        have hform : ∃ value, (value, initial) = step := by
          simpa [tracked, StateT.run] using hstep
        obtain ⟨value, hpair⟩ := hform
        exact (congrArg Prod.snd hpair).symm
      rw [hsame]
    · have hcopy := hstep
      simp only [tracked, StateT.run] at hcopy
      rw [mem_support_bind_iff] at hcopy
      obtain ⟨inner, -, hinner⟩ := hcopy
      rw [support_pure, Set.mem_singleton_iff] at hinner
      rw [congrArg Prod.snd hinner]
      exact Finset.subset_insert _ _

/-- Having met `S`, the run has met it. -/
theorem meets_persists {α : Type} (S : Bytes → Prop) (computation : OracleComp OracleWorld α)
    (initial : State) (result : α × State)
    (hmem : result ∈ support ((simulateQ tracked computation).run initial))
    (hmeets : Meets S initial) : Meets S result.2 := by
  obtain ⟨input, hinput, hS⟩ := hmeets
  exact ⟨input, subset_of_run computation initial result hmem hinput, hS⟩

/-- The tracked oracle never fails. -/
theorem tracked_neverFails {α : Type} (computation : OracleComp OracleWorld α)
    (initial : State) :
    Pr[⊥ | (simulateQ tracked computation).run initial] = 0 := by
  induction computation using OracleComp.inductionOn generalizing initial with
  | pure value => rw [simulateQ_pure, StateT.run_pure]; simp
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, probFailure_bind_eq_add_tsum]
    have hstepFails : Pr[⊥ | (tracked queried).run initial] = 0 := by
      rcases queried with coin | input <;> simp [tracked, StateT.run]
    rw [hstepFails, zero_add]
    simp [ih]

/-- Once `S` has been met the event is certain. -/
theorem meets_one {α : Type} (S : Bytes → Prop) (computation : OracleComp OracleWorld α)
    (initial : State) (hmeets : Meets S initial) :
    Pr[fun result : α × State => Meets S result.2 |
      (simulateQ tracked computation).run initial] = 1 :=
  probEvent_eq_one ⟨tracked_neverFails computation initial,
    fun result hmem => meets_persists S computation initial result hmem hmeets⟩

set_option maxHeartbeats 1000000 in
/-- **Two caches agreeing off `S` meet `S` with the same probability**, with the queried set
carried so the blind bound can consume it. -/
theorem prob_meets_eq {α : Type} (S : Bytes → Prop) [DecidablePred S]
    (computation : OracleComp OracleWorld α) :
    ∀ (left right : QueryCache HashSpec) (queried : Finset Bytes) (count : Nat),
      BlindComparison.AgreeOff S left right →
        Pr[fun result : α × State => Meets S result.2 |
            (simulateQ tracked computation).run (left, queried, count)] =
          Pr[fun result : α × State => Meets S result.2 |
            (simulateQ tracked computation).run (right, queried, count)] := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro left right queried count _
    simp [simulateQ_pure, StateT.run_pure, Meets]
  | query_bind queried' next ih =>
    intro left right queried count hagree
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases queried' with coin | input
    · have hcoin : ∀ state : State, (tracked (Sum.inl coin)).run state =
          (fun value => (value, state)) <$>
            ($ᵗ (OracleWorld.Range (Sum.inl coin)) : ProbComp _) := fun _ => rfl
      simp only [hcoin, bind_map_left, probEvent_bind_eq_tsum]
      exact tsum_congr fun value =>
        congrArg _ (ih value left right queried count hagree)
    · have hstepShape : ∀ (cache : QueryCache HashSpec),
          (tracked (Sum.inr input)).run (cache, queried, count) =
            (randomOracle input).run cache >>= fun step =>
              pure (step.1, (step.2, insert input queried, count + 1)) := fun _ => rfl
      by_cases hmember : S input
      · -- Inside `S`: both runs have met it, whatever follows.
        have hone : ∀ cache : QueryCache HashSpec,
            Pr[fun result : α × State => Meets S result.2 |
              (tracked (Sum.inr input)).run (cache, queried, count) >>= fun step =>
                (simulateQ tracked (next step.1)).run step.2] = 1 := by
          intro cache
          rw [probEvent_bind_eq_tsum]
          have hterm : ∀ step ∈ support ((tracked (Sum.inr input)).run (cache, queried, count)),
              Pr[fun result : α × State => Meets S result.2 |
                (simulateQ tracked (next step.1)).run step.2] = 1 := by
            intro step hstep
            refine meets_one S (next step.1) step.2 ?_
            have hcopy := hstep
            rw [hstepShape cache, mem_support_bind_iff] at hcopy
            obtain ⟨inner, -, hinner⟩ := hcopy
            rw [support_pure, Set.mem_singleton_iff] at hinner
            rw [congrArg Prod.snd hinner]
            exact ⟨input, Finset.mem_insert_self _ _, hmember⟩
          calc ∑' step, Pr[= step | (tracked (Sum.inr input)).run (cache, queried, count)] *
                Pr[fun result : α × State => Meets S result.2 |
                  (simulateQ tracked (next step.1)).run step.2]
              = ∑' step, Pr[= step | (tracked (Sum.inr input)).run (cache, queried, count)] := by
                refine tsum_congr fun step => ?_
                by_cases hmem :
                    step ∈ support ((tracked (Sum.inr input)).run (cache, queried, count))
                · rw [hterm step hmem, mul_one]
                · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
            _ = 1 := by
                rw [← probFailure_add_tsum_probOutput
                  ((tracked (Sum.inr input)).run (cache, queried, count))]
                simp [hstepShape cache]
        rw [hone left, hone right]
      · -- Outside `S`: the caches agree at this very input.
        have hsame : left input = right input := hagree input hmember
        cases hlookup : left input with
        | some cached =>
          have hright : right input = some cached := by rw [← hsame, hlookup]
          have hrun : ∀ cache : QueryCache HashSpec, cache input = some cached →
              (tracked (Sum.inr input)).run (cache, queried, count) =
                (pure (cached, (cache, insert input queried, count + 1)) :
                  ProbComp (HashOutput × State)) := by
            intro cache hcache
            rw [hstepShape cache, QueryImpl.withCaching_run_some _ hcache, pure_bind]
          rw [hrun left hlookup, hrun right hright, pure_bind, pure_bind]
          exact ih cached left right _ _ hagree
        | none =>
          have hright : right input = none := by rw [← hsame, hlookup]
          have hrun : ∀ cache : QueryCache HashSpec, cache input = none →
              (tracked (Sum.inr input)).run (cache, queried, count) =
                (fun answer => (answer, (cache.cacheQuery input answer,
                  insert input queried, count + 1))) <$>
                  ($ᵗ HashOutput : ProbComp HashOutput) := by
            intro cache hcache
            rw [hstepShape cache, QueryImpl.withCaching_run_none _ hcache]
            simp only [uniformSampleImpl, map_eq_bind_pure_comp, Function.comp_def,
              bind_assoc, pure_bind]
          rw [hrun left hlookup, hrun right hright, bind_map_left, bind_map_left,
            probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
          exact tsum_congr fun answer =>
            congrArg _ (ih answer _ _ _ _ (hagree.cacheQuery input answer))

/-! ## Transferring the whole experiment to the blind one

`prob_meets_eq` compares two runs at a fixed `S`. In the experiment `S` is the set of
seed-bearing inputs, which depends on the seed, and so does the real cache — but the blind
cache does not. Averaging the comparison over the seed therefore moves the whole experiment to
the blind one, at no cost, and on that side the run no longer involves the seed at all. -/

set_option maxHeartbeats 1000000 in
/-- **The real experiment and the blind one meet the seed-bearing inputs equally often.** -/
theorem prob_meets_real_eq_blind {α : Type} (computation : OracleComp OracleWorld α)
    (realCache : Digest → QueryCache HashSpec) (blindCache : QueryCache HashSpec)
    (seedInput : Digest → Bytes → Prop) [inst : ∀ secret, DecidablePred (seedInput secret)]
    (hagree : ∀ secret,
      BlindComparison.AgreeOff (seedInput secret) (realCache secret) blindCache) :
    Pr[fun pair : Digest × (α × State) => Meets (seedInput pair.1) pair.2.2 |
        (do
          let secret ← ($ᵗ Digest : ProbComp Digest)
          let result ← (simulateQ tracked computation).run (realCache secret, ∅, 0)
          pure (secret, result))] =
      Pr[fun pair : Digest × (α × State) => Meets (seedInput pair.1) pair.2.2 |
        (do
          let secret ← ($ᵗ Digest : ProbComp Digest)
          let result ← (simulateQ tracked computation).run (blindCache, ∅, 0)
          pure (secret, result))] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun secret => congrArg _ ?_
  simp only [bind_pure_comp, probEvent_map]
  exact prob_meets_eq (seedInput secret) computation (realCache secret) blindCache ∅ 0
    (hagree secret)

/-! ## The blind side, bounded

On the blind side the run does not involve the seed, so the seed may be drawn after it. That
is what `SeedDeferral.prob_run_meets_honest_key_le` needs, and the queried set the tracked
oracle carries is what it consumes. -/

set_option maxHeartbeats 1000000 in
/-- **The blind run meets a seed-bearing input at most once per query.** -/
theorem prob_meets_blind_le {α Index : Type} (computation : OracleComp OracleWorld α)
    (blindCache : QueryCache HashSpec) (inputOf : Digest → Index → Bytes)
    (locate : Bytes → Option Index)
    (hlocate : ∀ (secret : Digest) (node : Index), locate (inputOf secret node) = some node)
    (hinj : ∀ node : Index, Function.Injective fun secret : Digest => inputOf secret node)
    (limit : Nat)
    (hcard : ∀ result ∈ support ((simulateQ tracked computation).run (blindCache, ∅, 0)),
      result.2.2.1.card ≤ limit) :
    Pr[fun pair : (α × State) × Digest =>
        ∃ candidate ∈ pair.1.2.2.1, ∃ node : Index, inputOf pair.2 node = candidate |
      (do
        let result ← (simulateQ tracked computation).run (blindCache, ∅, 0)
        let secret ← ($ᵗ Digest : ProbComp Digest)
        pure (result, secret))] ≤
      (limit : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  have hmapped := SeedDeferral.prob_run_meets_honest_key_le
    ((fun result : α × State => (result, result.2.2.1)) <$>
      (simulateQ tracked computation).run (blindCache, ∅, 0))
    inputOf locate hlocate hinj limit ?_
  · rw [probEvent_bind_eq_tsum]
    rw [bind_map_left, probEvent_bind_eq_tsum] at hmapped
    refine le_trans (le_of_eq (tsum_congr fun x => congrArg _ ?_)) hmapped
    simp only [bind_pure_comp, probEvent_map]
    rfl
  · intro result hmem
    rw [support_map] at hmem
    obtain ⟨inner, hinner, hpair⟩ := hmem
    rw [← hpair]
    exact hcard inner hinner

/-! ## The input half

Composing the two: the real experiment meets a seed-bearing input exactly as often as the
blind one, and the blind one at most once per query. Nothing is lost between them, which is
what a budget met with equality requires — and the reason this route was taken over the
identical-until-bad hop, which could not avoid paying `Θ(q / 2 ^ 128)` for the same step. -/

/-- The inputs that carry a given secret. -/
def SeedInputOf {Index : Type} (inputOf : Digest → Index → Bytes) (secret : Digest)
    (input : Bytes) : Prop := ∃ node : Index, inputOf secret node = input

set_option maxHeartbeats 1000000 in
/-- **The input half.** The real experiment meets a seed-bearing input at most once per
charged query. -/
theorem prob_meets_real_le {α Index : Type} (computation : OracleComp OracleWorld α)
    (realCache : Digest → QueryCache HashSpec) (blindCache : QueryCache HashSpec)
    (inputOf : Digest → Index → Bytes) (locate : Bytes → Option Index)
    [inst : ∀ secret, DecidablePred (SeedInputOf inputOf secret)]
    (hlocate : ∀ (secret : Digest) (node : Index), locate (inputOf secret node) = some node)
    (hinj : ∀ node : Index, Function.Injective fun secret : Digest => inputOf secret node)
    (hagree : ∀ secret,
      BlindComparison.AgreeOff (SeedInputOf inputOf secret) (realCache secret) blindCache)
    (limit : Nat)
    (hcard : ∀ result ∈ support ((simulateQ tracked computation).run (blindCache, ∅, 0)),
      result.2.2.1.card ≤ limit) :
    Pr[fun pair : Digest × (α × State) => Meets (SeedInputOf inputOf pair.1) pair.2.2 |
        (do
          let secret ← ($ᵗ Digest : ProbComp Digest)
          let result ← (simulateQ tracked computation).run (realCache secret, ∅, 0)
          pure (secret, result))] ≤
      (limit : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  rw [prob_meets_real_eq_blind computation realCache blindCache
    (SeedInputOf inputOf) hagree]
  have hcomm : 𝒟[(do
        let secret ← ($ᵗ Digest : ProbComp Digest)
        let result ← (simulateQ tracked computation).run (blindCache, ∅, 0)
        pure (secret, result))] =
      𝒟[(do
        let result ← (simulateQ tracked computation).run (blindCache, ∅, 0)
        let secret ← ($ᵗ Digest : ProbComp Digest)
        pure (secret, result))] :=
    OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hcomm]
  refine le_trans (le_of_eq ?_)
    (prob_meets_blind_le computation blindCache inputOf locate hlocate hinj limit hcard)
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine tsum_congr fun result => congrArg _ ?_
  simp only [bind_pure_comp, probEvent_map]
  rfl

end SlhDsaSecurity.TrackedQueries
