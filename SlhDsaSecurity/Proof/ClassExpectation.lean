import SlhDsaSecurity.Proof.ClassGrowth

/-!
# The per-class charge, before the uniform bound is taken

`ClassCharge.prob_badWithinClasses_le` carries its budget *through* the induction: the budget is
a conjunct of the event, it is decremented at every in-class miss, and the base of that
recursion proves the event impossible once the budget runs out. So there is no expectation
hiding inside it, and the uniform limit cannot simply be moved to the end the way
`SensitiveExpectation` moves the input half's.

What makes the expectation form worth proving rather than working around is that it needs less,
not more. Stated against the *count* of in-class queries rather than the *growth* of the class,
the `GrowthAtMostOn` bookkeeping disappears along with the decrementing and the impossibility
case: a coin and a cache hit leave the count alone, and a miss contributes its own rate plus the
tail. What replaces the bookkeeping is expectation algebra at the bind, which is where this kind
of proof goes wrong, so the two identities it turns on — a bind and a constant shift — are
proved separately rather than reached for.

The constant shift is the one that needs the run's total mass, and that is why `neverFails` is
here: without it a step would only give `mass + expected`, which is the wrong direction. Nothing
in the proof needs the count to be bounded, so the uniform limit is not smuggled back in.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ClassExpectation

open Security GrowthCharge ClassGrowth

/-! ## Expectations of a count -/

/-- The expected value of a count over a run. -/
noncomputable def expected {β : Type} (run : ProbComp β) (count : β → Nat) : ℝ≥0∞ :=
  ∑' value, Pr[= value | run] * ((count value : Nat) : ℝ≥0∞)

theorem expected_pure {β : Type} (value : β) (count : β → Nat) :
    expected (pure value : ProbComp β) count = ((count value : Nat) : ℝ≥0∞) := by
  classical
  rw [expected, tsum_eq_single value fun other hother => by
      rw [probOutput_eq_zero_of_not_mem_support (by simp [hother]), zero_mul],
    probOutput_pure_self, one_mul]

/-- **An expectation splits along a bind.** -/
theorem expected_bind {β γ : Type} (run : ProbComp β) (next : β → ProbComp γ)
    (count : γ → Nat) :
    expected (run >>= next) count =
      ∑' value, Pr[= value | run] * expected (next value) count := by
  rw [expected]
  calc ∑' output, Pr[= output | run >>= next] * ((count output : Nat) : ℝ≥0∞)
      = ∑' output, (∑' value, Pr[= value | run] * Pr[= output | next value]) *
          ((count output : Nat) : ℝ≥0∞) :=
        tsum_congr fun output => by rw [probOutput_bind_eq_tsum]
    _ = ∑' output, ∑' value, Pr[= value | run] * Pr[= output | next value] *
          ((count output : Nat) : ℝ≥0∞) :=
        tsum_congr fun output => ENNReal.tsum_mul_right.symm
    _ = ∑' value, ∑' output, Pr[= value | run] *
          (Pr[= output | next value] * ((count output : Nat) : ℝ≥0∞)) := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun value => tsum_congr fun output => by ring
    _ = ∑' value, Pr[= value | run] * expected (next value) count :=
        tsum_congr fun value => ENNReal.tsum_mul_left

/-- **An expectation splits along a map.** -/
theorem expected_map {β γ : Type} [DecidableEq γ] (run : ProbComp β) (reshape : β → γ)
    (count : γ → Nat) :
    expected (reshape <$> run) count = expected run (fun value => count (reshape value)) := by
  rw [expected, expected]
  calc ∑' output, Pr[= output | reshape <$> run] * ((count output : Nat) : ℝ≥0∞)
      = ∑' output, (∑' value, if output = reshape value then Pr[= value | run] else 0) *
          ((count output : Nat) : ℝ≥0∞) :=
        tsum_congr fun output => by rw [probOutput_map_eq_tsum_ite]
    _ = ∑' output, ∑' value,
          (if output = reshape value then Pr[= value | run] else 0) *
            ((count output : Nat) : ℝ≥0∞) :=
        tsum_congr fun output => ENNReal.tsum_mul_right.symm
    _ = ∑' value, ∑' output,
          (if output = reshape value then Pr[= value | run] else 0) *
            ((count output : Nat) : ℝ≥0∞) := ENNReal.tsum_comm
    _ = ∑' value, Pr[= value | run] * ((count (reshape value) : Nat) : ℝ≥0∞) := by
        refine tsum_congr fun value => ?_
        rw [tsum_eq_single (reshape value)
          (fun other hother => by rw [if_neg hother, zero_mul]), if_pos rfl]

/-- **A constant shift of the count shifts the expectation**, the run's mass being one. -/
theorem expected_const_add {β : Type} (run : ProbComp β) (hmass : Pr[⊥ | run] = 0)
    (shift : Nat) (count : β → Nat) :
    expected run (fun value => shift + count value) =
      ((shift : Nat) : ℝ≥0∞) + expected run count := by
  rw [expected, expected]
  calc ∑' value, Pr[= value | run] * (((shift + count value : Nat)) : ℝ≥0∞)
      = ∑' value, (Pr[= value | run] * ((shift : Nat) : ℝ≥0∞) +
          Pr[= value | run] * ((count value : Nat) : ℝ≥0∞)) := by
        refine tsum_congr fun value => ?_
        push_cast
        ring
    _ = (∑' value, Pr[= value | run] * ((shift : Nat) : ℝ≥0∞)) +
          ∑' value, Pr[= value | run] * ((count value : Nat) : ℝ≥0∞) := ENNReal.tsum_add
    _ = ((shift : Nat) : ℝ≥0∞) + ∑' value, Pr[= value | run] *
          ((count value : Nat) : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' hmass, one_mul]

theorem expected_mono {β : Type} (run : ProbComp β) (count other : β → Nat)
    (hle : ∀ value ∈ support run, count value ≤ other value) :
    expected run count ≤ expected run other := by
  refine ENNReal.tsum_le_tsum fun value => ?_
  by_cases hmem : value ∈ support run
  · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (hle value hmem))
  · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]

/-! ## The run's mass -/

/-- **A run of the shared oracle never fails**, which is what lets a step contribute a whole
unit rather than the mass that survives it. -/
theorem run_neverFails {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    Pr[⊥ | (simulateQ KeygenUniform.rom computation).run cache] = 0 := by
  simp

/-! ## The charge -/

open scoped Classical in
/-- The shape one step leaves: the step's own charge added to the tail's count. -/
theorem event_map_eq {α : Type} (bad : Bytes → HashOutput → Prop) (shift : Counts)
    (run : ProbComp ((α × Counts) × QueryCache HashSpec)) :
    Pr[Bad bad | (fun result : (α × Counts) × QueryCache HashSpec =>
        ((result.1.1, shift + result.1.2), result.2)) <$> run] = Pr[Bad bad | run] := by
  rw [probEvent_map]
  rfl

open scoped Classical in
theorem count_map_eq {α : Type} (shift : Counts)
    (run : ProbComp ((α × Counts) × QueryCache HashSpec)) (hmass : Pr[⊥ | run] = 0) :
    expected ((fun result : (α × Counts) × QueryCache HashSpec =>
          ((result.1.1, shift + result.1.2), result.2)) <$> run)
        (fun result => (result.1.2) .hash) =
      ((shift .hash : Nat) : ℝ≥0∞) +
        expected run (fun result => (result.1.2) .hash) := by
  rw [expected_map]
  exact expected_const_add run hmass (shift .hash) (fun result => (result.1.2) .hash)

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The per-class charge, as an expectation.** A run ends holding an answer bad for its own
input with probability at most its expected number of in-class queries, times the rate. The
count is read off each run; nothing here bounds it. -/
theorem prob_bad_le_expected (inClass : Bytes → Prop) (bad : Bytes → HashOutput → Prop)
    (rate : ℝ≥0∞)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ rate)
    (hclass : ∀ input answer, bad input answer → inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (initialCache : QueryCache HashSpec), CleanBad bad initialCache →
      Pr[Bad bad | (simulateQ KeygenUniform.rom
          (countQueries (classCost inClass) computation)).run initialCache] ≤
        expected ((simulateQ KeygenUniform.rom
            (countQueries (classCost inClass) computation)).run initialCache)
          (fun result => (result.1.2) .hash) * rate := by
  classical
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro initialCache hclean
    refine le_of_eq_of_le (b := 0) ?_ (by simp)
    rw [VerificationBudget.countQueries_pure, simulateQ_pure, StateT.run_pure]
    refine probEvent_eq_zero fun result hresult hbad => ?_
    rw [support_pure, Set.mem_singleton_iff] at hresult
    subst hresult
    obtain ⟨input, output, hanswer, hbadness⟩ := hbad
    exact hclean input output hanswer hbadness
  | query_bind queried next ih =>
    intro initialCache hclean
    rw [WarmedSplit.countQueries_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind]
    simp only [simulateQ_map, StateT.run_map]
    rcases queried with coin | input
    · -- A uniform coin costs nothing and leaves the cache alone.
      rw [probEvent_bind_eq_tsum, expected_bind, ← ENNReal.tsum_mul_right]
      have hstep : ∀ step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run initialCache),
          step.2 = initialCache := by
        intro step hstep
        have hform : step ∈
            Set.range (fun value : OracleWorld.Range (Sum.inl coin) => (value, initialCache)) := by
          simpa [KeygenUniform.rom, XmssSecurity.RandomOracleModel.impl, unifFwdImpl] using hstep
        obtain ⟨value, hvalue⟩ := hform
        rw [← hvalue]
      refine ENNReal.tsum_le_tsum fun step => ?_
      by_cases hmem : step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run initialCache)
      · rw [event_map_eq, count_map_eq _ _ (run_neverFails _ _), classCost_inl,
          hstep step hmem, mul_assoc]
        refine mul_le_mul' le_rfl ?_
        rw [show ((0 : Counts) .hash : Nat) = 0 from rfl, Nat.cast_zero, zero_add]
        exact ih step.1 initialCache hclean
      · rw [probOutput_eq_zero_of_not_mem_support hmem]
        simp
    · cases hcached : initialCache input with
      | some cached =>
        have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
            (pure (cached, initialCache) :
              ProbComp (HashOutput × QueryCache HashSpec)) := by
          change (randomOracle input).run initialCache = _
          rw [QueryImpl.withCaching_run_some _ hcached]
        rw [hrun]
        show Pr[Bad bad | (fun result : (α × Counts) × QueryCache HashSpec =>
              ((result.1.1, classCost inClass (Sum.inr input) + result.1.2), result.2)) <$>
            (simulateQ KeygenUniform.rom
              (countQueries (classCost inClass) (next cached))).run initialCache] ≤
          expected ((fun result : (α × Counts) × QueryCache HashSpec =>
              ((result.1.1, classCost inClass (Sum.inr input) + result.1.2), result.2)) <$>
            (simulateQ KeygenUniform.rom
              (countQueries (classCost inClass) (next cached))).run initialCache)
            (fun result => (result.1.2) .hash) * rate
        rw [event_map_eq, count_map_eq _ _ (run_neverFails _ _)]
        refine le_trans (ih cached initialCache hclean) ?_
        exact mul_le_mul' le_add_self le_rfl
      | none =>
        have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
            (fun answer => (answer, initialCache.cacheQuery input answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput) := by
          change (randomOracle input).run initialCache = _
          rw [QueryImpl.withCaching_run_none _ hcached]
          simp [uniformSampleImpl]
        rw [hrun]
        show Pr[Bad bad | ($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
            (fun result : (α × Counts) × QueryCache HashSpec =>
                ((result.1.1, classCost inClass (Sum.inr input) + result.1.2), result.2)) <$>
              (simulateQ KeygenUniform.rom
                (countQueries (classCost inClass) (next answer))).run
                (initialCache.cacheQuery input answer)] ≤
          expected (($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
            (fun result : (α × Counts) × QueryCache HashSpec =>
                ((result.1.1, classCost inClass (Sum.inr input) + result.1.2), result.2)) <$>
              (simulateQ KeygenUniform.rom
                (countQueries (classCost inClass) (next answer))).run
                (initialCache.cacheQuery input answer))
            (fun result => (result.1.2) .hash) * rate
        rw [probEvent_bind_eq_tsum, expected_bind]
        simp only [event_map_eq, count_map_eq _ _ (run_neverFails _ _), classCost_inr_hash]
        have hpointwise : ∀ answer : HashOutput,
            Pr[Bad bad | (simulateQ KeygenUniform.rom
                (countQueries (classCost inClass) (next answer))).run
                (initialCache.cacheQuery input answer)] ≤
              (if bad input answer then 1 else 0) + expected ((simulateQ KeygenUniform.rom
                (countQueries (classCost inClass) (next answer))).run
                (initialCache.cacheQuery input answer)) (fun result => (result.1.2) .hash) * rate := by
          intro answer
          by_cases hbadness : bad input answer
          · rw [if_pos hbadness]
            exact le_add_right probEvent_le_one
          · rw [if_neg hbadness, zero_add]
            exact ih answer (initialCache.cacheQuery input answer) (hclean.cacheQuery hbadness)
        have hsplit : ∑' answer : HashOutput,
              Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                ((if bad input answer then 1 else 0) + expected ((simulateQ KeygenUniform.rom
                (countQueries (classCost inClass) (next answer))).run
                (initialCache.cacheQuery input answer)) (fun result => (result.1.2) .hash) * rate) =
            Pr[fun answer : HashOutput => bad input answer |
              ($ᵗ HashOutput : ProbComp HashOutput)] +
              (∑' answer : HashOutput,
                Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] * expected ((simulateQ KeygenUniform.rom
                (countQueries (classCost inClass) (next answer))).run
                (initialCache.cacheQuery input answer)) (fun result => (result.1.2) .hash)) * rate := by
          rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
          refine tsum_congr fun answer => ?_
          rw [mul_add, mul_assoc]
          by_cases hbadness : bad input answer <;> simp [hbadness]
        refine le_trans (le_trans (ENNReal.tsum_le_tsum fun answer =>
          mul_le_mul' le_rfl (hpointwise answer)) (le_of_eq hsplit)) ?_
        by_cases hmember : inClass input
        · simp only [if_pos hmember]
          have hdistrib : ∀ answer : HashOutput,
              Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  (((1 : Nat) : ℝ≥0∞) + expected ((simulateQ KeygenUniform.rom
                (countQueries (classCost inClass) (next answer))).run
                (initialCache.cacheQuery input answer)) (fun result => (result.1.2) .hash)) =
                Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] +
                  Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] * expected ((simulateQ KeygenUniform.rom
                (countQueries (classCost inClass) (next answer))).run
                (initialCache.cacheQuery input answer)) (fun result => (result.1.2) .hash) := by
            intro answer
            rw [mul_add, Nat.cast_one, mul_one]
          rw [tsum_congr hdistrib, ENNReal.tsum_add, tsum_probOutput_eq_one' (by simp),
            add_mul, one_mul]
          exact add_le_add (hrate input) le_rfl
        · simp only [if_neg hmember, Nat.cast_zero, zero_add]
          have hzero : Pr[fun answer : HashOutput => bad input answer |
              ($ᵗ HashOutput : ProbComp HashOutput)] = 0 :=
            probEvent_eq_zero fun answer _ hbadness => hmember (hclass input answer hbadness)
          rw [hzero, zero_add]

end SlhDsaSecurity.ClassExpectation
