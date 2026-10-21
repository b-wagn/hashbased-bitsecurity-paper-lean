import SlhDsaSecurity.Proof.FreshHitBound

/-!
# Charging by observable cache growth

`FreshHitBound.prob_hit_le` needs a *syntactic* query bound, but the experiment supplies an
*almost-sure* bound on an instrumented counter (`Security.HasBudget`), and the two do not
match: an adversary meeting the counter bound need not meet a syntactic one.

This file closes that gap without any new instrumentation. Only a cache **miss** draws a
fresh uniform answer, so only a miss can newly hit a target; a replayed query cannot. The
number of misses during a run is exactly the growth of the cache, which is a function of
the observable final state. So the budget can be enforced by the *event* rather than by a
hypothesis on the computation:

  `Pr[Hit targetOf ∧ GrowthAtMost initialCache finalCache limit] ≤ limit / 2 ^ 128`.

`GrowthAtMost` avoids any cardinality notion on the infinite input type: it says no
duplicate-free list of inputs that are absent initially and present finally is longer than
`limit`. Cache monotonicity (`cache_mono`) supplies the "present finally" half for an entry
installed mid-run.

Repeated queries are *not* charged here, which is sound for an upper bound: a replay
returns the already-cached answer and cannot create a new hit. The experiment charges them,
so the experiment's budget dominates the growth, which is what makes this usable.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.GrowthCharge

/-- Cache entries are never removed or overwritten along a run. -/
theorem cache_mono {α : Type} (computation : OracleComp OracleWorld α)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ KeygenUniform.rom computation).run initialCache))
    (input : Bytes) (hpresent : initialCache input ≠ none) : finalCache input ≠ none := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache finalCache result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    exact hmem.2 ▸ hpresent
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
    have hmiddle : middleCache input ≠ none := by
      rcases queried with coin | queried
      · have hcache : middleCache = initialCache := by
          symm
          simpa [KeygenUniform.rom, XmssSecurity.RandomOracleModel.impl, unifFwdImpl] using hquery
        exact hcache ▸ hpresent
      · change (output, middleCache) ∈ support ((randomOracle queried).run initialCache) at hquery
        cases hqueried : initialCache queried with
        | none =>
          rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hquery
          obtain ⟨sampled, _, heq⟩ := hquery
          have hmid : middleCache = initialCache.cacheQuery queried sampled :=
            (Prod.ext_iff.mp heq).2.symm
          rw [hmid]
          by_cases hsame : input = queried
          · subst hsame
            rw [QueryCache.cacheQuery_self]
            simp
          · rw [QueryCache.cacheQuery_of_ne initialCache sampled hsame]
            exact hpresent
        | some cached =>
          rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
            Set.mem_singleton_iff] at hquery
          cases hquery
          exact hpresent
    exact ih output middleCache finalCache result hrest hmiddle

/-- At most `limit` inputs were absent from `initial` and are present in `final`. Stated
without a cardinality on the infinite input type. -/
def GrowthAtMost (initial final : QueryCache HashSpec) (limit : Nat) : Prop :=
  ∀ inputs : List Bytes, inputs.Nodup →
    (∀ input ∈ inputs, initial input = none ∧ final input ≠ none) → inputs.length ≤ limit

/-- An entry installed mid-run consumes one unit of growth budget. -/
theorem GrowthAtMost.pos {initial final : QueryCache HashSpec} {limit : Nat} {input : Bytes}
    (hfresh : initial input = none) (hpresent : final input ≠ none)
    (hgrowth : GrowthAtMost initial final limit) : 1 ≤ limit := by
  simpa using hgrowth [input] (List.nodup_singleton input)
    (by intro i hi; rw [List.mem_singleton.mp hi]; exact ⟨hfresh, hpresent⟩)

/-- Installing an entry decrements the remaining growth budget. -/
theorem GrowthAtMost.cacheQuery {initial final : QueryCache HashSpec} {limit : Nat}
    {input : Bytes} {answer : HashOutput}
    (hfresh : initial input = none) (hpresent : final input ≠ none)
    (hgrowth : GrowthAtMost initial final limit) :
    GrowthAtMost (initial.cacheQuery input answer) final (limit - 1) := by
  intro inputs hnodup hmembers
  have hne : ∀ i ∈ inputs, i ≠ input := by
    intro i hi hsame
    have := (hmembers i hi).1
    rw [hsame, QueryCache.cacheQuery_self] at this
    simp at this
  have hextended : (input :: inputs).length ≤ limit := by
    refine hgrowth (input :: inputs) ?_ ?_
    · refine List.nodup_cons.mpr ⟨?_, hnodup⟩
      intro hmem
      exact hne input hmem rfl
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact ⟨hfresh, hpresent⟩
      · refine ⟨?_, (hmembers i hi).2⟩
        have hentry := (hmembers i hi).1
        rwa [QueryCache.cacheQuery_of_ne initial answer (hne i hi)] at hentry
  simp only [List.length_cons] at hextended
  omega

/-- The event charged by cache growth. -/
def HitWithin {α : Type} (targetOf : Bytes → Option Digest)
    (initialCache : QueryCache HashSpec) (limit : Nat) :
    α × QueryCache HashSpec → Prop := fun result =>
  FreshHitBound.Hit targetOf result ∧ GrowthAtMost initialCache result.2 limit

set_option maxHeartbeats 1000000 in
/-- The linear charge with the budget enforced by observable cache growth instead of by a
syntactic query bound. -/
theorem prob_hitWithin_le {α : Type} (computation : OracleComp OracleWorld α)
    (targetOf : Bytes → Option Digest) (limit : Nat) (initialCache : QueryCache HashSpec)
    (hclean : FreshHitBound.Clean targetOf initialCache) :
    Pr[HitWithin targetOf initialCache limit |
      (simulateQ KeygenUniform.rom computation).run initialCache] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  induction computation using OracleComp.inductionOn generalizing limit initialCache with
  | pure value =>
    refine le_of_eq_of_le (b := 0) ?_ (by simp)
    rw [simulateQ_pure, StateT.run_pure]
    refine probEvent_eq_zero fun result hresult hhit => ?_
    rw [support_pure, Set.mem_singleton_iff] at hresult
    subst hresult
    obtain ⟨⟨input, output, hanswer, htrunc⟩, _⟩ := hhit
    exact hclean input output hanswer htrunc
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases queried with coin | input
    · -- A uniform coin leaves the cache, and hence the growth budget, untouched.
      rw [probEvent_bind_eq_tsum]
      have hstep : ∀ step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run initialCache),
          step.2 = initialCache := by
        intro step hstep
        have hform : ∃ coinValue, (coinValue, initialCache) = step := by
          simpa [KeygenUniform.rom, XmssSecurity.RandomOracleModel.impl, unifFwdImpl] using hstep
        obtain ⟨coinValue, rfl⟩ := hform
        rfl
      calc ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run initialCache] *
            Pr[HitWithin targetOf initialCache limit |
              (simulateQ KeygenUniform.rom (next step.1)).run step.2]
          ≤ ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run initialCache] *
              (limit / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
            refine ENNReal.tsum_le_tsum fun step => ?_
            by_cases hmem : step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run initialCache)
            · refine mul_le_mul' le_rfl ?_
              rw [hstep step hmem]
              exact ih step.1 limit initialCache hclean
            · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
              simp
        _ = (∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run initialCache]) *
              (limit / ((2 ^ 128 : Nat) : ℝ≥0∞)) := ENNReal.tsum_mul_right
        _ ≤ 1 * (limit / ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
            mul_le_mul' tsum_probOutput_le_one le_rfl
        _ = _ := one_mul _
    · cases hcached : initialCache input with
      | some cached =>
        -- A replay returns the cached answer: no new randomness, no growth.
        have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
            (pure (cached, initialCache) :
              ProbComp (HashOutput × QueryCache HashSpec)) := by
          change (randomOracle input).run initialCache = _
          rw [QueryImpl.withCaching_run_some _ hcached]
        rw [hrun, pure_bind]
        exact ih cached limit initialCache hclean
      | none =>
        -- A cache miss: one fresh uniform answer, one unit of growth.
        have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
            (fun answer => (answer, initialCache.cacheQuery input answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput) := by
          change (randomOracle input).run initialCache = _
          rw [QueryImpl.withCaching_run_none _ hcached]
          simp [uniformSampleImpl]
        rw [hrun]
        show Pr[HitWithin targetOf initialCache limit |
          (($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
            (simulateQ KeygenUniform.rom (next answer)).run
              (initialCache.cacheQuery input answer))] ≤ _
        cases limit with
        | zero =>
          -- With no budget the event is unreachable: the installed entry already costs one.
          refine le_of_eq_of_le (b := 0) ?_ (by simp)
          refine probEvent_eq_zero fun result hresult hhit => ?_
          rw [mem_support_bind_iff] at hresult
          obtain ⟨answer, _, hrest⟩ := hresult
          have hpresent : result.2 input ≠ none :=
            cache_mono (next answer) (initialCache.cacheQuery input answer) result.2 result.1
              hrest input (by rw [QueryCache.cacheQuery_self]; simp)
          exact absurd (hhit.2.pos hcached hpresent) (by omega)
        | succ remaining =>
          rw [probEvent_bind_eq_tsum]
          have hpointwise : ∀ answer : HashOutput,
              Pr[HitWithin targetOf initialCache (remaining + 1) |
                  (simulateQ KeygenUniform.rom (next answer)).run
                    (initialCache.cacheQuery input answer)] ≤
                (if some (Hashing.truncate answer) = targetOf input then 1 else 0) +
                  (remaining : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
            intro answer
            by_cases htrunc : some (Hashing.truncate answer) = targetOf input
            · rw [if_pos htrunc]
              exact le_add_right probEvent_le_one
            · rw [if_neg htrunc, zero_add]
              refine le_trans (probEvent_mono ?_)
                (ih answer remaining (initialCache.cacheQuery input answer)
                  (hclean.cacheQuery (Ne.symm htrunc)))
              intro result hresult hhit
              refine ⟨hhit.1, ?_⟩
              have hpresent : result.2 input ≠ none :=
                cache_mono (next answer) (initialCache.cacheQuery input answer) result.2
                  result.1 hresult input
                  (by rw [QueryCache.cacheQuery_self]; simp)
              simpa using hhit.2.cacheQuery hcached hpresent
          calc ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                Pr[HitWithin targetOf initialCache (remaining + 1) |
                  (simulateQ KeygenUniform.rom (next answer)).run
                    (initialCache.cacheQuery input answer)]
              ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  ((if some (Hashing.truncate answer) = targetOf input then 1 else 0) +
                    (remaining : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
                ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hpointwise answer)
            _ = (∑' answer : HashOutput, (if some (Hashing.truncate answer) = targetOf input then
                    Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] else 0)) +
                  (∑' answer : HashOutput,
                      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)]) *
                    ((remaining : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
                rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
                refine tsum_congr fun answer => ?_
                rw [mul_add]
                by_cases htrunc : some (Hashing.truncate answer) = targetOf input <;>
                  simp [htrunc]
            _ ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) +
                  1 * ((remaining : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
                refine add_le_add ?_ (mul_le_mul' tsum_probOutput_le_one le_rfl)
                rw [← probEvent_eq_tsum_ite]
                exact FreshHitBound.prob_target_match_le (targetOf input)
            _ = ((remaining + 1 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
                rw [one_mul, ENNReal.div_add_div_same]
                congr 1
                push_cast
                ring

end SlhDsaSecurity.GrowthCharge
