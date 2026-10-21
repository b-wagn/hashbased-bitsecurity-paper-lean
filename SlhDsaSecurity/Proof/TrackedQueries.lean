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

end SlhDsaSecurity.TrackedQueries
