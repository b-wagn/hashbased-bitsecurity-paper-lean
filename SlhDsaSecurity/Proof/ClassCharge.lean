import SlhDsaSecurity.Proof.GrowthCharge

/-!
# Charging each query at its own class rate

`GrowthCharge.prob_badWithin_le` charges every cache miss at the *maximum* per-call rate. That
is enough when the rates agree, but the first-principles budget needs the sharper statement:
the answer-side bad event costs `2 ^ -128` on a structural input and only `2 ^ -129` on a
message input, and `Assembly.le_target_of_classes` needs the two counted separately, because
the one unit of slack per message query is exactly where the load-cap and separation defects
are charged.

So the growth budget is split by class. `GrowthAtMostOn` counts only the newly installed
entries whose input lies in a given class, and the charge below carries one budget for each
side, decrementing whichever the current miss belongs to. The resulting bound is
`insideLimit * insideRate + outsideLimit * outsideRate` rather than
`(insideLimit + outsideLimit) * max`.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.ClassCharge

open GrowthCharge

/-- Growth counted only at inputs of a given class. -/
def GrowthAtMostOn (inClass : Bytes → Prop) (initial final : QueryCache HashSpec)
    (limit : Nat) : Prop :=
  ∀ inputs : List Bytes, inputs.Nodup →
    (∀ input ∈ inputs, inClass input ∧ initial input = none ∧ final input ≠ none) →
      inputs.length ≤ limit

theorem GrowthAtMostOn.mono {inClass : Bytes → Prop} {initial final : QueryCache HashSpec}
    {limit limit' : Nat} (hgrowth : GrowthAtMostOn inClass initial final limit)
    (hle : limit ≤ limit') : GrowthAtMostOn inClass initial final limit' :=
  fun inputs hnodup hmembers => (hgrowth inputs hnodup hmembers).trans hle

/-- An in-class entry installed mid-run consumes one unit of that class's budget. -/
theorem GrowthAtMostOn.pos {inClass : Bytes → Prop} {initial final : QueryCache HashSpec}
    {limit : Nat} {input : Bytes} (hmember : inClass input)
    (hfresh : initial input = none) (hpresent : final input ≠ none)
    (hgrowth : GrowthAtMostOn inClass initial final limit) : 1 ≤ limit := by
  simpa using hgrowth [input] (List.nodup_singleton input)
    (by intro i hi; rw [List.mem_singleton.mp hi]; exact ⟨hmember, hfresh, hpresent⟩)

/-- Installing an in-class entry decrements that class's budget. -/
theorem GrowthAtMostOn.cacheQuery {inClass : Bytes → Prop}
    {initial final : QueryCache HashSpec} {limit : Nat}
    {input : Bytes} {answer : HashOutput} (hmember : inClass input)
    (hfresh : initial input = none) (hpresent : final input ≠ none)
    (hgrowth : GrowthAtMostOn inClass initial final limit) :
    GrowthAtMostOn inClass (initial.cacheQuery input answer) final (limit - 1) := by
  intro inputs hnodup hmembers
  have hne : ∀ i ∈ inputs, i ≠ input := by
    intro i hi hsame
    have := (hmembers i hi).2.1
    rw [hsame, QueryCache.cacheQuery_self] at this
    simp at this
  have hextended : (input :: inputs).length ≤ limit := by
    refine hgrowth (input :: inputs) ?_ ?_
    · exact List.nodup_cons.mpr ⟨fun hmem => hne input hmem rfl, hnodup⟩
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact ⟨hmember, hfresh, hpresent⟩
      · refine ⟨(hmembers i hi).1, ?_, (hmembers i hi).2.2⟩
        have hentry := (hmembers i hi).2.1
        rwa [QueryCache.cacheQuery_of_ne initial answer (hne i hi)] at hentry
  simp only [List.length_cons] at hextended
  omega

/-- Installing an out-of-class entry leaves that class's budget alone. -/
theorem GrowthAtMostOn.cacheQuery_other {inClass : Bytes → Prop}
    {initial final : QueryCache HashSpec} {limit : Nat}
    {input : Bytes} {answer : HashOutput} (hmember : ¬ inClass input)
    (hgrowth : GrowthAtMostOn inClass initial final limit) :
    GrowthAtMostOn inClass (initial.cacheQuery input answer) final limit := by
  intro inputs hnodup hmembers
  refine hgrowth inputs hnodup fun i hi => ?_
  have hne : i ≠ input := by
    intro hsame
    exact hmember (hsame ▸ (hmembers i hi).1)
  refine ⟨(hmembers i hi).1, ?_, (hmembers i hi).2.2⟩
  have hentry := (hmembers i hi).2.1
  rwa [QueryCache.cacheQuery_of_ne initial answer hne] at hentry

/-- Undoing an in-class installation costs one unit of budget: if the extended cache admits a
budget, the original admits one more. -/
theorem GrowthAtMostOn.succ_of_cacheQuery {inClass : Bytes → Prop}
    {initial final : QueryCache HashSpec} {limit : Nat}
    {input : Bytes} {answer : HashOutput}
    (hgrowth : GrowthAtMostOn inClass (initial.cacheQuery input answer) final limit) :
    GrowthAtMostOn inClass initial final (limit + 1) := by
  classical
  intro inputs hnodup hmembers
  have hrest : (inputs.erase input).length ≤ limit := by
    refine hgrowth (inputs.erase input) (hnodup.erase input) fun probe hprobe => ?_
    have hmem : probe ∈ inputs := List.mem_of_mem_erase hprobe
    have hne : probe ≠ input := by
      intro hsame
      subst hsame
      exact (hnodup.not_mem_erase) hprobe
    refine ⟨(hmembers probe hmem).1, ?_, (hmembers probe hmem).2.2⟩
    rw [QueryCache.cacheQuery_of_ne initial answer hne]
    exact (hmembers probe hmem).2.1
  have hlength : inputs.length ≤ (inputs.erase input).length + 1 := by
    by_cases hpresent : input ∈ inputs
    · rw [List.length_erase_of_mem hpresent]
      have := List.length_pos_of_mem hpresent
      omega
    · rw [List.erase_of_not_mem hpresent]
      omega
  omega

/-- An out-of-class installation is invisible to the class budget, in the other direction from
`cacheQuery_other`: a budget for the extended cache is one for the original. -/
theorem GrowthAtMostOn.of_cacheQuery_other {inClass : Bytes → Prop}
    {initial final : QueryCache HashSpec} {limit : Nat}
    {input : Bytes} {answer : HashOutput} (hmember : ¬ inClass input)
    (hgrowth : GrowthAtMostOn inClass (initial.cacheQuery input answer) final limit) :
    GrowthAtMostOn inClass initial final limit := by
  refine fun inputs hnodup hmembers => hgrowth inputs hnodup fun probe hprobe => ?_
  have hne : probe ≠ input := fun hsame => hmember (hsame ▸ (hmembers probe hprobe).1)
  refine ⟨(hmembers probe hprobe).1, ?_, (hmembers probe hprobe).2.2⟩
  rw [QueryCache.cacheQuery_of_ne initial answer hne]
  exact (hmembers probe hprobe).2.1

/-- The event, with a separate growth budget for each class. -/
def BadWithinClasses {α : Type} (bad : Bytes → HashOutput → Prop) (inClass : Bytes → Prop)
    (initialCache : QueryCache HashSpec) (insideLimit outsideLimit : Nat) :
    α × QueryCache HashSpec → Prop := fun result =>
  Bad bad result ∧
    GrowthAtMostOn inClass initialCache result.2 insideLimit ∧
    GrowthAtMostOn (fun input => ¬ inClass input) initialCache result.2 outsideLimit

set_option maxHeartbeats 1000000 in
/-- **The per-class charge.** Each miss is charged at the rate of its own class and
decrements only that class's budget. -/
theorem prob_badWithinClasses_le {α : Type} (computation : OracleComp OracleWorld α)
    (bad : Bytes → HashOutput → Prop) (inClass : Bytes → Prop)
    (insideRate outsideRate : ℝ≥0∞) (insideLimit outsideLimit : Nat)
    (initialCache : QueryCache HashSpec)
    (hinside : ∀ input, inClass input →
      Pr[fun answer : HashOutput => bad input answer |
        ($ᵗ HashOutput : ProbComp HashOutput)] ≤ insideRate)
    (houtside : ∀ input, ¬ inClass input →
      Pr[fun answer : HashOutput => bad input answer |
        ($ᵗ HashOutput : ProbComp HashOutput)] ≤ outsideRate)
    (hclean : CleanBad bad initialCache) :
    Pr[BadWithinClasses bad inClass initialCache insideLimit outsideLimit |
      (simulateQ KeygenUniform.rom computation).run initialCache] ≤
      insideLimit * insideRate + outsideLimit * outsideRate := by
  classical
  induction computation using OracleComp.inductionOn generalizing
      insideLimit outsideLimit initialCache with
  | pure value =>
    refine le_of_eq_of_le (b := 0) ?_ (by simp)
    rw [simulateQ_pure, StateT.run_pure]
    refine probEvent_eq_zero fun result hresult hbad => ?_
    rw [support_pure, Set.mem_singleton_iff] at hresult
    subst hresult
    obtain ⟨⟨input, output, hanswer, hbadness⟩, _⟩ := hbad
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
            Pr[BadWithinClasses bad inClass initialCache insideLimit outsideLimit |
              (simulateQ KeygenUniform.rom (next step.1)).run step.2]
          ≤ ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run initialCache] *
              (insideLimit * insideRate + outsideLimit * outsideRate) := by
            refine ENNReal.tsum_le_tsum fun step => ?_
            by_cases hmem : step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run initialCache)
            · refine mul_le_mul' le_rfl ?_
              rw [hstep step hmem]
              exact ih step.1 insideLimit outsideLimit initialCache hclean
            · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
              simp
        _ = (∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run initialCache]) *
              (insideLimit * insideRate + outsideLimit * outsideRate) := ENNReal.tsum_mul_right
        _ ≤ 1 * (insideLimit * insideRate + outsideLimit * outsideRate) :=
            mul_le_mul' tsum_probOutput_le_one le_rfl
        _ = _ := one_mul _
    · cases hcached : initialCache input with
      | some cached =>
        have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
            (pure (cached, initialCache) :
              ProbComp (HashOutput × QueryCache HashSpec)) := by
          change (randomOracle input).run initialCache = _
          rw [QueryImpl.withCaching_run_some _ hcached]
        rw [hrun, pure_bind]
        exact ih cached insideLimit outsideLimit initialCache hclean
      | none =>
        have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
            (fun answer => (answer, initialCache.cacheQuery input answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput) := by
          change (randomOracle input).run initialCache = _
          rw [QueryImpl.withCaching_run_none _ hcached]
          simp [uniformSampleImpl]
        rw [hrun]
        show Pr[BadWithinClasses bad inClass initialCache insideLimit outsideLimit |
          (($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
            (simulateQ KeygenUniform.rom (next answer)).run
              (initialCache.cacheQuery input answer))] ≤ _
        by_cases hmember : inClass input
        · -- An in-class miss: charge the inside rate and decrement the inside budget.
          cases insideLimit with
          | zero =>
            refine le_of_eq_of_le (b := 0) ?_ (by simp)
            refine probEvent_eq_zero fun result hresult hbad => ?_
            rw [mem_support_bind_iff] at hresult
            obtain ⟨answer, _, hrest⟩ := hresult
            have hpresent : result.2 input ≠ none :=
              cache_mono (next answer) (initialCache.cacheQuery input answer) result.2 result.1
                hrest input (by rw [QueryCache.cacheQuery_self]; simp)
            exact absurd (hbad.2.1.pos hmember hcached hpresent) (by omega)
          | succ remaining =>
            rw [probEvent_bind_eq_tsum]
            have hpointwise : ∀ answer : HashOutput,
                Pr[BadWithinClasses bad inClass initialCache (remaining + 1) outsideLimit |
                    (simulateQ KeygenUniform.rom (next answer)).run
                      (initialCache.cacheQuery input answer)] ≤
                  (if bad input answer then 1 else 0) +
                    (remaining * insideRate + outsideLimit * outsideRate) := by
              intro answer
              by_cases hbadness : bad input answer
              · rw [if_pos hbadness]
                exact le_add_right probEvent_le_one
              · rw [if_neg hbadness, zero_add]
                refine le_trans (probEvent_mono ?_)
                  (ih answer remaining outsideLimit (initialCache.cacheQuery input answer)
                    (hclean.cacheQuery hbadness))
                intro result hresult hbad
                have hpresent : result.2 input ≠ none :=
                  cache_mono (next answer) (initialCache.cacheQuery input answer) result.2
                    result.1 hresult input
                    (by rw [QueryCache.cacheQuery_self]; simp)
                exact ⟨hbad.1,
                  by simpa using hbad.2.1.cacheQuery hmember hcached hpresent,
                  hbad.2.2.cacheQuery_other (by simpa using hmember)⟩
            calc ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  Pr[BadWithinClasses bad inClass initialCache (remaining + 1) outsideLimit |
                    (simulateQ KeygenUniform.rom (next answer)).run
                      (initialCache.cacheQuery input answer)]
                ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                    ((if bad input answer then 1 else 0) +
                      (remaining * insideRate + outsideLimit * outsideRate)) :=
                  ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hpointwise answer)
              _ = (∑' answer : HashOutput, (if bad input answer then
                      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] else 0)) +
                    (∑' answer : HashOutput,
                        Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)]) *
                      (remaining * insideRate + outsideLimit * outsideRate) := by
                  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
                  refine tsum_congr fun answer => ?_
                  rw [mul_add]
                  by_cases hbadness : bad input answer <;> simp [hbadness]
              _ ≤ insideRate + 1 * (remaining * insideRate + outsideLimit * outsideRate) := by
                  refine add_le_add ?_ (mul_le_mul' tsum_probOutput_le_one le_rfl)
                  rw [← probEvent_eq_tsum_ite]
                  exact hinside input hmember
              _ = ((remaining + 1 : Nat) : ℝ≥0∞) * insideRate +
                    outsideLimit * outsideRate := by
                  rw [one_mul]
                  push_cast
                  ring
        · -- An out-of-class miss: charge the outside rate and decrement the outside budget.
          cases outsideLimit with
          | zero =>
            refine le_of_eq_of_le (b := 0) ?_ (by simp)
            refine probEvent_eq_zero fun result hresult hbad => ?_
            rw [mem_support_bind_iff] at hresult
            obtain ⟨answer, _, hrest⟩ := hresult
            have hpresent : result.2 input ≠ none :=
              cache_mono (next answer) (initialCache.cacheQuery input answer) result.2 result.1
                hrest input (by rw [QueryCache.cacheQuery_self]; simp)
            exact absurd (hbad.2.2.pos hmember hcached hpresent) (by omega)
          | succ remaining =>
            rw [probEvent_bind_eq_tsum]
            have hpointwise : ∀ answer : HashOutput,
                Pr[BadWithinClasses bad inClass initialCache insideLimit (remaining + 1) |
                    (simulateQ KeygenUniform.rom (next answer)).run
                      (initialCache.cacheQuery input answer)] ≤
                  (if bad input answer then 1 else 0) +
                    (insideLimit * insideRate + remaining * outsideRate) := by
              intro answer
              by_cases hbadness : bad input answer
              · rw [if_pos hbadness]
                exact le_add_right probEvent_le_one
              · rw [if_neg hbadness, zero_add]
                refine le_trans (probEvent_mono ?_)
                  (ih answer insideLimit remaining (initialCache.cacheQuery input answer)
                    (hclean.cacheQuery hbadness))
                intro result hresult hbad
                have hpresent : result.2 input ≠ none :=
                  cache_mono (next answer) (initialCache.cacheQuery input answer) result.2
                    result.1 hresult input
                    (by rw [QueryCache.cacheQuery_self]; simp)
                exact ⟨hbad.1, hbad.2.1.cacheQuery_other hmember,
                  by simpa using hbad.2.2.cacheQuery hmember hcached hpresent⟩
            calc ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  Pr[BadWithinClasses bad inClass initialCache insideLimit (remaining + 1) |
                    (simulateQ KeygenUniform.rom (next answer)).run
                      (initialCache.cacheQuery input answer)]
                ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                    ((if bad input answer then 1 else 0) +
                      (insideLimit * insideRate + remaining * outsideRate)) :=
                  ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hpointwise answer)
              _ = (∑' answer : HashOutput, (if bad input answer then
                      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] else 0)) +
                    (∑' answer : HashOutput,
                        Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)]) *
                      (insideLimit * insideRate + remaining * outsideRate) := by
                  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
                  refine tsum_congr fun answer => ?_
                  rw [mul_add]
                  by_cases hbadness : bad input answer <;> simp [hbadness]
              _ ≤ outsideRate + 1 * (insideLimit * insideRate + remaining * outsideRate) := by
                  refine add_le_add ?_ (mul_le_mul' tsum_probOutput_le_one le_rfl)
                  rw [← probEvent_eq_tsum_ite]
                  exact houtside input hmember
              _ = insideLimit * insideRate +
                    ((remaining + 1 : Nat) : ℝ≥0∞) * outsideRate := by
                  rw [one_mul]
                  push_cast
                  ring

end SlhDsaSecurity.ClassCharge
