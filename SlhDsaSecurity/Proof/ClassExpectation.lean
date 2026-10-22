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

/-! ## Two charges on one budget

The record's entries and the signer's in-class answers are the two kinds of chance the budget
pays for, and they add: on each run the two counts together stay inside the budget, so the two
expectations together do. Neither charge has a budget of its own, and the per-request terms
cancel inside the pathwise inequality rather than after a uniform bound has been taken. -/

/-- Counts add under the expectation. -/
theorem expected_add {β : Type} (run : ProbComp β) (count other : β → Nat) :
    expected run (fun value => count value + other value) =
      expected run count + expected run other := by
  rw [expected, expected, expected, ← ENNReal.tsum_add]
  refine tsum_congr fun value => ?_
  push_cast
  ring

/-- A count bounded on every supported run has a bounded expectation. -/
theorem expected_le_of_le {β : Type} (run : ProbComp β) (count : β → Nat) (bound : Nat)
    (hle : ∀ value ∈ support run, count value ≤ bound) :
    expected run count ≤ ((bound : Nat) : ℝ≥0∞) := by
  calc expected run count
      ≤ ∑' value, Pr[= value | run] * ((bound : Nat) : ℝ≥0∞) := by
        refine ENNReal.tsum_le_tsum fun value => ?_
        by_cases hmem : value ∈ support run
        · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (hle value hmem))
        · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]
    _ = (∑' value, Pr[= value | run]) * ((bound : Nat) : ℝ≥0∞) := ENNReal.tsum_mul_right
    _ ≤ 1 * ((bound : Nat) : ℝ≥0∞) := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = _ := one_mul _

/-- **Two charges share one budget.** Each is bounded by its own expected number of chances, and
on every supported run the two counts together stay inside the budget — so the two charges
together cost what one budget buys, not two. -/
theorem add_le_of_shared_budget {β : Type} (run : ProbComp β)
    (firstCharge secondCharge : ℝ≥0∞) (firstChances secondChances : β → Nat) (budget : Nat)
    (hfirst : firstCharge ≤ expected run firstChances / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hsecond : secondCharge ≤ expected run secondChances / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hshare : ∀ value ∈ support run, firstChances value + secondChances value ≤ budget) :
    firstCharge + secondCharge ≤ ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_trans (add_le_add hfirst hsecond) ?_
  rw [ENNReal.div_add_div_same, ← expected_add]
  exact ENNReal.div_le_div_right
    (expected_le_of_le run (fun value => firstChances value + secondChances value) budget hshare) _

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
/-- The same shift, read at an arbitrary slot of the counter. -/
theorem count_map_eq_slot {α : Type} (slot : QueryKind) (shift : Counts)
    (run : ProbComp ((α × Counts) × QueryCache HashSpec)) (hmass : Pr[⊥ | run] = 0) :
    expected ((fun result : (α × Counts) × QueryCache HashSpec =>
          ((result.1.1, shift + result.1.2), result.2)) <$> run)
        (fun result => (result.1.2) slot) =
      ((shift slot : Nat) : ℝ≥0∞) +
        expected run (fun result => (result.1.2) slot) := by
  rw [expected_map]
  exact expected_const_add run hmass (shift slot) (fun result => (result.1.2) slot)

open scoped Classical in
theorem count_map_eq {α : Type} (shift : Counts)
    (run : ProbComp ((α × Counts) × QueryCache HashSpec)) (hmass : Pr[⊥ | run] = 0) :
    expected ((fun result : (α × Counts) × QueryCache HashSpec =>
          ((result.1.1, shift + result.1.2), result.2)) <$> run)
        (fun result => (result.1.2) .hash) =
      ((shift .hash : Nat) : ℝ≥0∞) +
        expected run (fun result => (result.1.2) .hash) :=
  count_map_eq_slot .hash shift run hmass

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The per-class charge, as an expectation, at an arbitrary counter.** A run ends holding an
answer bad for its own input with probability at most the expected value of `slot` on the run's
own counter, times the rate — provided the counter charges at least one unit of `slot` to every
in-class hash call. The count is read off each run; nothing here bounds it.

Keeping the counter and the slot free is what lets the two sides of one class split be read off
*one* run: `splitCost` charges the class to one slot and its complement to another, and both
charges are then stated against the same instrumented run, so their counts add pathwise rather
than each being bounded on its own. -/
theorem prob_bad_le_expected_cost (inClass : Bytes → Prop) (bad : Bytes → HashOutput → Prop)
    (rate : ℝ≥0∞) (cost : OracleWorld.Domain → Counts) (slot : QueryKind)
    (hcost : ∀ input, inClass input → 1 ≤ cost (Sum.inr input) slot)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ rate)
    (hclass : ∀ input answer, bad input answer → inClass input)
    {α : Type} (computation : OracleComp OracleWorld α) :
    ∀ (initialCache : QueryCache HashSpec), CleanBad bad initialCache →
      Pr[Bad bad | (simulateQ KeygenUniform.rom
          (countQueries cost computation)).run initialCache] ≤
        expected ((simulateQ KeygenUniform.rom
            (countQueries cost computation)).run initialCache)
          (fun result => (result.1.2) slot) * rate := by
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
    · -- A uniform coin leaves the cache alone, and whatever it costs only helps.
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
      · rw [event_map_eq, count_map_eq_slot _ _ _ (run_neverFails _ _), hstep step hmem,
          mul_assoc]
        refine mul_le_mul' le_rfl ?_
        exact le_trans (ih step.1 initialCache hclean) (mul_le_mul' le_add_self le_rfl)
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
              ((result.1.1, cost (Sum.inr input) + result.1.2), result.2)) <$>
            (simulateQ KeygenUniform.rom
              (countQueries cost (next cached))).run initialCache] ≤
          expected ((fun result : (α × Counts) × QueryCache HashSpec =>
              ((result.1.1, cost (Sum.inr input) + result.1.2), result.2)) <$>
            (simulateQ KeygenUniform.rom
              (countQueries cost (next cached))).run initialCache)
            (fun result => (result.1.2) slot) * rate
        rw [event_map_eq, count_map_eq_slot _ _ _ (run_neverFails _ _)]
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
                ((result.1.1, cost (Sum.inr input) + result.1.2), result.2)) <$>
              (simulateQ KeygenUniform.rom
                (countQueries cost (next answer))).run
                (initialCache.cacheQuery input answer)] ≤
          expected (($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
            (fun result : (α × Counts) × QueryCache HashSpec =>
                ((result.1.1, cost (Sum.inr input) + result.1.2), result.2)) <$>
              (simulateQ KeygenUniform.rom
                (countQueries cost (next answer))).run
                (initialCache.cacheQuery input answer))
            (fun result => (result.1.2) slot) * rate
        rw [probEvent_bind_eq_tsum, expected_bind]
        simp only [event_map_eq, count_map_eq_slot _ _ _ (run_neverFails _ _)]
        have hpointwise : ∀ answer : HashOutput,
            Pr[Bad bad | (simulateQ KeygenUniform.rom
                (countQueries cost (next answer))).run
                (initialCache.cacheQuery input answer)] ≤
              (if bad input answer then 1 else 0) + expected ((simulateQ KeygenUniform.rom
                (countQueries cost (next answer))).run
                (initialCache.cacheQuery input answer))
                (fun result => (result.1.2) slot) * rate := by
          intro answer
          by_cases hbadness : bad input answer
          · rw [if_pos hbadness]
            exact le_add_right probEvent_le_one
          · rw [if_neg hbadness, zero_add]
            exact ih answer (initialCache.cacheQuery input answer) (hclean.cacheQuery hbadness)
        have hsplit : ∑' answer : HashOutput,
              Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                ((if bad input answer then 1 else 0) + expected ((simulateQ KeygenUniform.rom
                (countQueries cost (next answer))).run
                (initialCache.cacheQuery input answer))
                (fun result => (result.1.2) slot) * rate) =
            Pr[fun answer : HashOutput => bad input answer |
              ($ᵗ HashOutput : ProbComp HashOutput)] +
              (∑' answer : HashOutput,
                Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  expected ((simulateQ KeygenUniform.rom
                (countQueries cost (next answer))).run
                (initialCache.cacheQuery input answer))
                (fun result => (result.1.2) slot)) * rate := by
          rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
          refine tsum_congr fun answer => ?_
          rw [mul_add, mul_assoc]
          by_cases hbadness : bad input answer <;> simp [hbadness]
        refine le_trans (le_trans (ENNReal.tsum_le_tsum fun answer =>
          mul_le_mul' le_rfl (hpointwise answer)) (le_of_eq hsplit)) ?_
        -- The step's own charge is a constant shift of the tail's expectation.
        have hrhs : (∑' answer : HashOutput,
              Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                (((cost (Sum.inr input) slot : Nat) : ℝ≥0∞) +
                  expected ((simulateQ KeygenUniform.rom
                    (countQueries cost (next answer))).run
                    (initialCache.cacheQuery input answer))
                    (fun result => (result.1.2) slot))) =
            ((cost (Sum.inr input) slot : Nat) : ℝ≥0∞) +
              ∑' answer : HashOutput,
                Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  expected ((simulateQ KeygenUniform.rom
                    (countQueries cost (next answer))).run
                    (initialCache.cacheQuery input answer))
                    (fun result => (result.1.2) slot) := by
          calc ∑' answer : HashOutput,
                Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  (((cost (Sum.inr input) slot : Nat) : ℝ≥0∞) +
                    expected ((simulateQ KeygenUniform.rom
                      (countQueries cost (next answer))).run
                      (initialCache.cacheQuery input answer))
                      (fun result => (result.1.2) slot))
              = ∑' answer : HashOutput,
                  (Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                      ((cost (Sum.inr input) slot : Nat) : ℝ≥0∞) +
                    Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                      expected ((simulateQ KeygenUniform.rom
                        (countQueries cost (next answer))).run
                        (initialCache.cacheQuery input answer))
                        (fun result => (result.1.2) slot)) :=
                tsum_congr fun answer => mul_add _ _ _
            _ = (∑' answer : HashOutput,
                  Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                    ((cost (Sum.inr input) slot : Nat) : ℝ≥0∞)) +
                ∑' answer : HashOutput,
                  Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                    expected ((simulateQ KeygenUniform.rom
                      (countQueries cost (next answer))).run
                      (initialCache.cacheQuery input answer))
                      (fun result => (result.1.2) slot) := ENNReal.tsum_add
            _ = _ := by
                rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]
        rw [hrhs, add_mul]
        by_cases hmember : inClass input
        · -- An in-class call is charged at least one unit of the slot, which pays the rate.
          refine add_le_add (le_trans (hrate input) ?_) le_rfl
          calc rate = 1 * rate := (one_mul rate).symm
            _ ≤ ((cost (Sum.inr input) slot : Nat) : ℝ≥0∞) * rate :=
                mul_le_mul' (by exact_mod_cast hcost input hmember) le_rfl
        · -- Off the class the answer cannot be bad at all, so the step costs nothing.
          have hzero : Pr[fun answer : HashOutput => bad input answer |
              ($ᵗ HashOutput : ProbComp HashOutput)] = 0 :=
            probEvent_eq_zero fun answer _ hbadness => hmember (hclass input answer hbadness)
          rw [hzero, zero_add]
          exact le_add_self

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
          (fun result => (result.1.2) .hash) * rate :=
  prob_bad_le_expected_cost inClass bad rate (classCost inClass) .hash
    (fun input hmember => by rw [classCost_inr_hash, if_pos hmember]) hrate hclass computation


/-! ## The two classes, added before the uniform bound is taken

Two charges on the two sides of one split, combined against one budget. What makes this an
addition rather than a doubling is that the two counts are counts of the *same* run — the
split-counted run, which `ClassGrowth.run_splitCost_eq_map` identifies with the plain one — so
the budget's pathwise inequality on the total is available before either charge has been
bounded uniformly.

Taking the uniform bound first is what costs the second budget. Each charge's limit is chosen
by the adversary, run by run, and the only number that bounds either on *every* run is the
whole budget; so a pair of fixed limits can only be `budget, budget`, which is the target twice
over. Here the two expectations are added first and the one uniform bound is taken at the end,
where the per-run split cancels inside the pathwise inequality rather than after it. -/

/-- **Two charges and a constant share one budget.** Each charge is bounded by its own expected
number of chances on one run, one of them with a constant beside it, and on every supported run
the two counts together stay inside the budget — so the two charges together cost what one
budget buys. -/
theorem add_le_of_shared_budget_const {β : Type} (run : ProbComp β)
    (firstCharge secondCharge constant : ℝ≥0∞)
    (firstChances secondChances : β → Nat) (budget : Nat)
    (hfirst : firstCharge ≤ expected run firstChances / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hsecond : secondCharge ≤
      constant + expected run secondChances / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hshare : ∀ value ∈ support run, firstChances value + secondChances value ≤ budget) :
    firstCharge + secondCharge ≤
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + constant := by
  calc firstCharge + secondCharge
      ≤ expected run firstChances / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          (constant + expected run secondChances / ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
        add_le_add hfirst hsecond
    _ = constant + (expected run firstChances / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          expected run secondChances / ((2 ^ 128 : Nat) : ℝ≥0∞)) := add_left_comm _ _ _
    _ = constant +
          expected run (fun value => firstChances value + secondChances value) /
            ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        rw [ENNReal.div_add_div_same, expected_add]
    _ ≤ constant + ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
        add_le_add le_rfl (ENNReal.div_le_div_right
          (expected_le_of_le run (fun value => firstChances value + secondChances value) budget
            hshare) _)
    _ = _ := add_comm _ _

open scoped Classical in
/-- **The charge on the outside class, stated at the plain run.** The structural half of a
split: the bad answer is witnessed only outside the class, so only the outside slot pays for
it, and the count is read off the split-counted run rather than bounded in advance. -/
theorem prob_bad_le_expected_outside (inClass : Bytes → Prop)
    {inside outside : QueryKind} (hne : inside ≠ outside)
    (bad : Bytes → HashOutput → Prop) (rate : ℝ≥0∞)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ rate)
    (hclass : ∀ input answer, bad input answer → ¬ inClass input)
    {α : Type} (computation : OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec) (hclean : CleanBad bad initialCache) :
    Pr[Bad bad |
        (simulateQ KeygenUniform.rom (countAllHashes computation)).run initialCache] ≤
      expected ((simulateQ KeygenUniform.rom
          (countQueries (splitCost inClass inside outside) computation)).run initialCache)
        (fun result => (result.1.2) outside) * rate := by
  classical
  rw [probEvent_splitCost inClass hne computation initialCache (Bad bad)]
  exact prob_bad_le_expected_cost (fun input => ¬ inClass input) bad rate
    (splitCost inClass inside outside) outside
    (fun input hmember => by rw [splitCost_outside inClass inside outside input hmember])
    hrate hclass computation initialCache hclean

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The two-class bound.** One budget, two charges, and no `qs + qm ≤ budget` left to
discharge: the structural charge is paid by the outside slot and the coverage charge by the
inside slot of one and the same counter, and the budget bounds their sum on every run.

The coverage charge enters in expectation form — `constant + expected inside count / 2 ^ 128` —
because that is the only form in which it can be added to the other without spending a second
budget. A coverage charge stated at a *fixed* limit cannot be put in this form by averaging:
`Pr[cov] ≤ constant + limit / 2 ^ 128` holding for every limit says nothing about
`constant + expected count / 2 ^ 128`, because the per-run weight has already been spent inside
the fixed-limit bound.

`inClass` is left free. Nothing below reads the class, so the bound survives the class being
narrowed; an instantiated counter would not. -/
theorem prob_bad_or_coverage_le (inClass : Bytes → Prop)
    {inside outside : QueryKind} (hne : inside ≠ outside)
    (bad : Bytes → HashOutput → Prop)
    (hrate : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (hclass : ∀ input answer, bad input answer → ¬ inClass input)
    {α : Type} (computation : OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec) (hclean : CleanBad bad initialCache)
    (coverage : (α × Nat) × QueryCache HashSpec → Prop) (constant : ℝ≥0∞)
    (hcoverage : Pr[coverage |
        (simulateQ KeygenUniform.rom (countAllHashes computation)).run initialCache] ≤
      constant + expected ((simulateQ KeygenUniform.rom
          (countQueries (splitCost inClass inside outside) computation)).run initialCache)
        (fun result => (result.1.2) inside) / ((2 ^ 128 : Nat) : ℝ≥0∞))
    (budget : Nat)
    (hbudget : ∀ result ∈ support ((simulateQ KeygenUniform.rom
      (countAllHashes computation)).run initialCache), result.1.2 ≤ budget) :
    Pr[fun result : (α × Nat) × QueryCache HashSpec => Bad bad result ∨ coverage result |
        (simulateQ KeygenUniform.rom (countAllHashes computation)).run initialCache] ≤
      ((budget : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + constant := by
  classical
  refine le_trans (probEvent_or_le _ _ _) ?_
  refine add_le_of_shared_budget_const
    ((simulateQ KeygenUniform.rom
      (countQueries (splitCost inClass inside outside) computation)).run initialCache)
    _ _ constant (fun result => (result.1.2) outside) (fun result => (result.1.2) inside)
    budget ?_ hcoverage ?_
  · rw [← mul_one_div]
    exact prob_bad_le_expected_outside inClass hne bad _ hrate hclass computation initialCache
      hclean
  · intro result hmem
    have hplain : result.1.2 inside + result.1.2 outside ≤ budget :=
      hbudget _ (mem_support_countAllHashes_of_splitCost inClass hne computation
        initialCache result hmem)
    omega

end SlhDsaSecurity.ClassExpectation
