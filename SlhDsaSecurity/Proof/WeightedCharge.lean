import SlhDsaSecurity.Proof.GrowthCharge
import SlhDsaSecurity.Statement.Security

/-!
# One weighted budget instead of per-class limits

`GrowthCharge.prob_badWithin_le` charges every miss at one rate; `ClassCharge.prob_badWithinClasses_le`
charges two classes at their own rates but takes both limits as fixed numbers, which the game
cannot supply — the class counts are run-dependent, and fixing both at `q` overshoots the
answer side's allowance.

What the game can supply is a single number. Give each charged miss a weight — `2` for a
structural-class input, `1` for a message-class input, in units of `2 ^ -129` — and charge one
weighted budget at a uniform rate. The bound is then `budget * rate`, and the budget is a
quantity the instrumented run actually produces.

This generalises both earlier charges: constant weight `1` recovers `prob_badWithin_le`, and a
two-valued weight recovers the per-class bound with the two limits replaced by their weighted
sum.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.WeightedCharge

open GrowthCharge

/-- The newly installed entries, measured by weight rather than counted. -/
def WeightedGrowthAtMost (weight : Bytes → Nat) (initial final : QueryCache HashSpec)
    (budget : Nat) : Prop :=
  ∀ inputs : List Bytes, inputs.Nodup →
    (∀ input ∈ inputs, initial input = none ∧ final input ≠ none) →
      (inputs.map weight).sum ≤ budget

theorem WeightedGrowthAtMost.mono {weight : Bytes → Nat}
    {initial final : QueryCache HashSpec} {budget budget' : Nat}
    (hgrowth : WeightedGrowthAtMost weight initial final budget) (hle : budget ≤ budget') :
    WeightedGrowthAtMost weight initial final budget' :=
  fun inputs hnodup hmembers => (hgrowth inputs hnodup hmembers).trans hle

/-- An entry installed mid-run consumes its own weight. -/
theorem WeightedGrowthAtMost.pos {weight : Bytes → Nat}
    {initial final : QueryCache HashSpec} {budget : Nat} {input : Bytes}
    (hfresh : initial input = none) (hpresent : final input ≠ none)
    (hgrowth : WeightedGrowthAtMost weight initial final budget) : weight input ≤ budget := by
  simpa using hgrowth [input] (List.nodup_singleton input)
    (by intro i hi; rw [List.mem_singleton.mp hi]; exact ⟨hfresh, hpresent⟩)

/-- Installing an entry decrements the budget by that entry's weight. -/
theorem WeightedGrowthAtMost.cacheQuery {weight : Bytes → Nat}
    {initial final : QueryCache HashSpec} {budget : Nat}
    {input : Bytes} {answer : HashOutput}
    (hfresh : initial input = none) (hpresent : final input ≠ none)
    (hgrowth : WeightedGrowthAtMost weight initial final budget) :
    WeightedGrowthAtMost weight (initial.cacheQuery input answer) final
      (budget - weight input) := by
  intro inputs hnodup hmembers
  have hne : ∀ i ∈ inputs, i ≠ input := by
    intro i hi hsame
    have := (hmembers i hi).1
    rw [hsame, QueryCache.cacheQuery_self] at this
    simp at this
  have hextended : ((input :: inputs).map weight).sum ≤ budget := by
    refine hgrowth (input :: inputs) ?_ ?_
    · exact List.nodup_cons.mpr ⟨fun hmem => hne input hmem rfl, hnodup⟩
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact ⟨hfresh, hpresent⟩
      · refine ⟨?_, (hmembers i hi).2⟩
        have hentry := (hmembers i hi).1
        rwa [QueryCache.cacheQuery_of_ne initial answer (hne i hi)] at hentry
  simp only [List.map_cons, List.sum_cons] at hextended
  omega

/-- Undoing an installation gives back that entry's weight. -/
theorem WeightedGrowthAtMost.add_of_cacheQuery {weight : Bytes → Nat}
    {initial final : QueryCache HashSpec} {budget : Nat}
    {input : Bytes} {answer : HashOutput}
    (hgrowth : WeightedGrowthAtMost weight (initial.cacheQuery input answer) final budget) :
    WeightedGrowthAtMost weight initial final (budget + weight input) := by
  classical
  intro inputs hnodup hmembers
  have hrest : ((inputs.erase input).map weight).sum ≤ budget := by
    refine hgrowth (inputs.erase input) (hnodup.erase input) fun probe hprobe => ?_
    have hmem : probe ∈ inputs := List.mem_of_mem_erase hprobe
    have hne : probe ≠ input := by
      intro hsame
      subst hsame
      exact (hnodup.not_mem_erase) hprobe
    refine ⟨?_, (hmembers probe hmem).2⟩
    rw [QueryCache.cacheQuery_of_ne initial answer hne]
    exact (hmembers probe hmem).1
  have hsplit : (inputs.map weight).sum ≤
      ((inputs.erase input).map weight).sum + weight input := by
    by_cases hpresent : input ∈ inputs
    · have hperm : inputs.Perm (input :: inputs.erase input) :=
        (List.perm_cons_erase hpresent)
      rw [hperm.map weight |>.sum_eq, List.map_cons, List.sum_cons]
      omega
    · rw [List.erase_of_not_mem hpresent]
      omega
  omega

/-- The event, with the weighted budget. -/
def BadWeighted {α : Type} (bad : Bytes → HashOutput → Prop) (weight : Bytes → Nat)
    (initialCache : QueryCache HashSpec) (budget : Nat) :
    α × QueryCache HashSpec → Prop := fun result =>
  Bad bad result ∧ WeightedGrowthAtMost weight initialCache result.2 budget

set_option maxHeartbeats 1000000 in
/-- **The weighted charge.** Each miss is charged at its own weight times the rate, and the
whole run at the budget times the rate. -/
theorem prob_badWeighted_le {α : Type} (computation : OracleComp OracleWorld α)
    (bad : Bytes → HashOutput → Prop) (weight : Bytes → Nat) (rate : ℝ≥0∞) (budget : Nat)
    (initialCache : QueryCache HashSpec)
    (hbad : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ weight input * rate)
    (hclean : CleanBad bad initialCache) :
    Pr[BadWeighted bad weight initialCache budget |
      (simulateQ KeygenUniform.rom computation).run initialCache] ≤ budget * rate := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget initialCache with
  | pure value =>
    refine le_of_eq_of_le (b := 0) ?_ (by simp)
    rw [simulateQ_pure, StateT.run_pure]
    refine probEvent_eq_zero fun result hresult hbadEvent => ?_
    rw [support_pure, Set.mem_singleton_iff] at hresult
    subst hresult
    obtain ⟨⟨input, output, hanswer, hbadness⟩, _⟩ := hbadEvent
    exact hclean input output hanswer hbadness
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases queried with coin | input
    · rw [probEvent_bind_eq_tsum]
      have hstep : ∀ step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run initialCache),
          step.2 = initialCache := by
        intro step hstep
        have hform : ∃ coinValue, (coinValue, initialCache) = step := by
          simpa [KeygenUniform.rom, XmssSecurity.RandomOracleModel.impl, unifFwdImpl] using hstep
        obtain ⟨coinValue, rfl⟩ := hform
        rfl
      calc ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run initialCache] *
            Pr[BadWeighted bad weight initialCache budget |
              (simulateQ KeygenUniform.rom (next step.1)).run step.2]
          ≤ ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run initialCache] *
              (budget * rate) := by
            refine ENNReal.tsum_le_tsum fun step => ?_
            by_cases hmem : step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run initialCache)
            · refine mul_le_mul' le_rfl ?_
              rw [hstep step hmem]
              exact ih step.1 budget initialCache hclean
            · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
              simp
        _ = (∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run initialCache]) *
              (budget * rate) := ENNReal.tsum_mul_right
        _ ≤ 1 * (budget * rate) := mul_le_mul' tsum_probOutput_le_one le_rfl
        _ = _ := one_mul _
    · cases hcached : initialCache input with
      | some cached =>
        have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
            (pure (cached, initialCache) :
              ProbComp (HashOutput × QueryCache HashSpec)) := by
          change (randomOracle input).run initialCache = _
          rw [QueryImpl.withCaching_run_some _ hcached]
        rw [hrun, pure_bind]
        exact ih cached budget initialCache hclean
      | none =>
        have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
            (fun answer => (answer, initialCache.cacheQuery input answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput) := by
          change (randomOracle input).run initialCache = _
          rw [QueryImpl.withCaching_run_none _ hcached]
          simp [uniformSampleImpl]
        rw [hrun]
        show Pr[BadWeighted bad weight initialCache budget |
          (($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
            (simulateQ KeygenUniform.rom (next answer)).run
              (initialCache.cacheQuery input answer))] ≤ _
        by_cases hroom : weight input ≤ budget
        · rw [probEvent_bind_eq_tsum]
          have hpointwise : ∀ answer : HashOutput,
              Pr[BadWeighted bad weight initialCache budget |
                  (simulateQ KeygenUniform.rom (next answer)).run
                    (initialCache.cacheQuery input answer)] ≤
                (if bad input answer then 1 else 0) +
                  (((budget - weight input : Nat) : ℝ≥0∞) * rate) := by
            intro answer
            by_cases hbadness : bad input answer
            · rw [if_pos hbadness]
              exact le_add_right probEvent_le_one
            · rw [if_neg hbadness, zero_add]
              refine le_trans (probEvent_mono ?_)
                (ih answer (budget - weight input) (initialCache.cacheQuery input answer)
                  (hclean.cacheQuery hbadness))
              intro result hresult hbadEvent
              have hpresent : result.2 input ≠ none :=
                cache_mono (next answer) (initialCache.cacheQuery input answer) result.2
                  result.1 hresult input
                  (by rw [QueryCache.cacheQuery_self]; simp)
              exact ⟨hbadEvent.1,
                hbadEvent.2.cacheQuery hcached hpresent⟩
          calc ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                Pr[BadWeighted bad weight initialCache budget |
                  (simulateQ KeygenUniform.rom (next answer)).run
                    (initialCache.cacheQuery input answer)]
              ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  ((if bad input answer then 1 else 0) +
                    (((budget - weight input : Nat) : ℝ≥0∞) * rate)) :=
                ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hpointwise answer)
            _ = (∑' answer : HashOutput, (if bad input answer then
                    Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] else 0)) +
                  (∑' answer : HashOutput,
                      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)]) *
                    (((budget - weight input : Nat) : ℝ≥0∞) * rate) := by
                rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
                refine tsum_congr fun answer => ?_
                rw [mul_add]
                by_cases hbadness : bad input answer <;> simp [hbadness]
            _ ≤ (weight input * rate) + 1 * (((budget - weight input : Nat) : ℝ≥0∞) * rate) := by
                refine add_le_add ?_ (mul_le_mul' tsum_probOutput_le_one le_rfl)
                rw [← probEvent_eq_tsum_ite]
                exact hbad input
            _ = (budget : ℝ≥0∞) * rate := by
                rw [one_mul, ← add_mul]
                congr 1
                rw [show (weight input : ℝ≥0∞) = ((weight input : Nat) : ℝ≥0∞) from rfl,
                  ← Nat.cast_add]
                congr 1
                omega
        · -- No room for this input's weight: the event cannot hold.
          refine le_of_eq_of_le (b := 0) ?_ (by simp)
          refine probEvent_eq_zero fun result hresult hbadEvent => ?_
          rw [mem_support_bind_iff] at hresult
          obtain ⟨answer, _, hrest⟩ := hresult
          have hpresent : result.2 input ≠ none :=
            cache_mono (next answer) (initialCache.cacheQuery input answer) result.2 result.1
              hrest input (by rw [QueryCache.cacheQuery_self]; simp)
          exact hroom (hbadEvent.2.pos hcached hpresent)

/-! ## The coarse bound, from the plain counter

A weighted budget can also be read off the *plain* count, at the cost of the slack. If every
weight is at most `bound`, then a run whose cache grew by at most `limit` entries has weighted
growth at most `bound * limit` — so the existing `countAllHashes` instrumentation already
supports the charge at budget `2 q`, which is exactly the answer side's allowance.

That is enough when there is no defect to pay, which by the dichotomy is precisely the branch
where fewer than sixteen digests were signed. The other branch needs the finer bound
`weighted = 2 q - m`, and so needs the message count as well as the total: one instrumentation
carrying both. -/

theorem weightedGrowth_of_growth {weight : Bytes → Nat} {bound : Nat}
    (hweight : ∀ input, weight input ≤ bound)
    {initial final : QueryCache HashSpec} {limit : Nat}
    (hgrowth : GrowthAtMost initial final limit) :
    WeightedGrowthAtMost weight initial final (bound * limit) := by
  intro inputs hnodup hmembers
  have hlength : inputs.length ≤ limit := hgrowth inputs hnodup hmembers
  have hsum : (inputs.map weight).sum ≤ bound * inputs.length := by
    induction inputs with
    | nil => simp
    | cons input rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hhead := hweight input
      have htail : (rest.map weight).sum ≤ bound * rest.length := by
        refine ih (List.nodup_cons.mp hnodup).2 (fun probe hprobe => hmembers probe (by simp [hprobe]))
          ((hgrowth rest (List.nodup_cons.mp hnodup).2
            (fun probe hprobe => hmembers probe (by simp [hprobe]))))
      nlinarith [hhead, htail]
  exact hsum.trans (Nat.mul_le_mul_left bound hlength)

/-! ## The weighted counter

The charge above consumes a budget; this is the instrumentation that produces one. Each hash
call costs its input's weight and a coin flip costs nothing, so a run's weighted count is
exactly what `prob_badWeighted_le` can be given — and, unlike a pair of class counts, it is a
single number the game emits.

`weightedGrowth_le_count` is the bridge: weighted growth never exceeds the weighted count.
With the budget hypothesis bounding that count, the charge applies to the whole game. -/

/-- A hash call costs its input's weight; coin flips are free. -/
def weightedCost (weight : Bytes → Nat) : OracleWorld.Domain → Nat :=
  fun queried => match queried with
    | Sum.inl _ => 0
    | Sum.inr input => weight input

/-- The run instrumented with the weighted counter. -/
def countWeighted (weight : Bytes → Nat) {α : Type} (computation : OracleComp OracleWorld α) :
    OracleComp OracleWorld (α × Nat) :=
  (fun result => (result.1, Multiplicative.toAdd result.2)) <$>
    (simulateQ (addCostOracle (weightedCost weight)) computation).run

@[simp] theorem countWeighted_pure (weight : Bytes → Nat) {α : Type} (value : α) :
    countWeighted weight (pure value : OracleComp OracleWorld α) = pure (value, 0) := by
  simp [countWeighted]

theorem countWeighted_query_bind (weight : Bytes → Nat) {α : Type}
    (queried : OracleWorld.Domain)
    (next : OracleWorld.Range queried → OracleComp OracleWorld α) :
    countWeighted weight (liftM (OracleWorld.query queried) >>= next) =
      liftM (OracleWorld.query queried) >>= fun answer =>
        (fun result => (result.1, weightedCost weight queried + result.2)) <$>
          countWeighted weight (next answer) := by
  simp only [countWeighted, simulateQ_bind, simulateQ_spec_query, addCostOracle,
    QueryImpl.withAddCost, QueryImpl.withCost]
  simp [Functor.map_map, map_bind, bind_map_left]

/-- **Weighted growth is bounded by the weighted count.** -/
theorem weightedGrowth_le_count (weight : Bytes → Nat) {α : Type}
    (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec)
    (result : (α × Nat) × QueryCache HashSpec)
    (hmem : result ∈
      support ((simulateQ KeygenUniform.rom (countWeighted weight computation)).run
        initialCache)) :
    WeightedGrowthAtMost weight initialCache result.2 result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
    rw [countWeighted_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    subst hmem
    intro inputs _ hmembers
    cases inputs with
    | nil => simp
    | cons input rest =>
      obtain ⟨hnone, hsome⟩ := hmembers input (by simp)
      exact absurd hnone hsome
  | query_bind queried next ih =>
    rw [countWeighted_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨⟨answer, middleCache⟩, hquery, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    have hgrowth := ih answer middleCache inner hinner
    have hfinal : result.2 = inner.2 := by rw [← heq]
    have hcount : result.1.2 = weightedCost weight queried + inner.1.2 := by rw [← heq]
    rcases queried with coin | input
    · have hcache : middleCache = initialCache := by
        symm
        have hform : ∃ coinValue, (coinValue, initialCache) = (answer, middleCache) := by
          simpa [KeygenUniform.rom, XmssSecurity.RandomOracleModel.impl, unifFwdImpl]
            using hquery
        obtain ⟨coinValue, hpair⟩ := hform
        exact congrArg Prod.snd hpair
      rw [hfinal, hcount, weightedCost]
      rw [hcache] at hgrowth
      simpa using hgrowth
    · have hmiddle : middleCache = initialCache.cacheQuery input answer ∨
          middleCache = initialCache := by
        cases hcached : initialCache input with
        | some cached =>
          right
          have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
              (pure (cached, initialCache) :
                ProbComp (HashOutput × QueryCache HashSpec)) := by
            change (randomOracle input).run initialCache = _
            rw [QueryImpl.withCaching_run_some _ hcached]
          rw [hrun, support_pure, Set.mem_singleton_iff] at hquery
          exact congrArg Prod.snd hquery
        | none =>
          left
          have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
              (fun value => (value, initialCache.cacheQuery input value)) <$>
                ($ᵗ HashOutput : ProbComp HashOutput) := by
            change (randomOracle input).run initialCache = _
            rw [QueryImpl.withCaching_run_none _ hcached]
            simp [uniformSampleImpl]
          rw [hrun, support_map] at hquery
          obtain ⟨value, -, hpair⟩ := hquery
          have hvalue : value = answer := congrArg Prod.fst hpair
          rw [← hvalue]
          exact (congrArg Prod.snd hpair).symm
      rw [hfinal, hcount, weightedCost]
      rcases hmiddle with hshape | hshape <;> rw [hshape] at hgrowth
      · exact (WeightedGrowthAtMost.add_of_cacheQuery hgrowth).mono (by omega)
      · exact hgrowth.mono (by omega)

end SlhDsaSecurity.WeightedCharge
