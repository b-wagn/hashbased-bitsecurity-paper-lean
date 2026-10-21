import SlhDsaSecurity.Proof.GrowthCharge

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

open OracleComp OracleSpec

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

end SlhDsaSecurity.TrackedQueries
