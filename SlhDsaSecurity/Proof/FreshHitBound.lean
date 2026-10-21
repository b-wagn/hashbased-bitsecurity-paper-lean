import SlhDsaSecurity.Proof.CollisionCharge
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Linear charge for hitting a fixed digest with a hash call

A computation over the shared world makes free uniform-coin queries and charged hash
queries. If its hash queries are bounded by `count`, and the starting cache holds no
answer whose sixteen-byte truncation equals `target`, then the probability that the run
ends with *any* cached answer truncating to `target` is at most `count / 2 ^ 128`.

Because the starting cache is clean, such an answer must have been installed during the
run, so this is the union bound over cache misses: each miss draws a fresh uniform 30-byte
answer whose truncation is uniform on 128 bits, costing `2 ^ -128`. The bound is linear in
the query count rather than quadratic, which is what the target `q / 2 ^ 127` requires.

Uniform-coin queries are free: they never touch the cache and never consume budget.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.FreshHitBound

/-- The charged queries: those addressed to the shared hash oracle. -/
def HashQuery : OracleWorld.Domain → Prop := fun query => query.isRight = true

instance : DecidablePred HashQuery := fun _ => inferInstanceAs (Decidable (_ = _))

/-- The final cache holds an answer truncating to `target`. -/
def Hit {α : Type} (target : Digest) : α × QueryCache HashSpec → Prop := fun result =>
  ∃ input output, result.2 input = some output ∧ Hashing.truncate output = target

/-- A cache holding no answer that truncates to `target`. -/
def Clean (target : Digest) (cache : QueryCache HashSpec) : Prop :=
  ∀ input output, cache input = some output → Hashing.truncate output ≠ target

theorem Clean.cacheQuery {target : Digest} {cache : QueryCache HashSpec}
    (hclean : Clean target cache) {input : Bytes} {output : HashOutput}
    (hmiss : Hashing.truncate output ≠ target) :
    Clean target (cache.cacheQuery input output) := by
  intro queried answer hanswer
  by_cases heq : queried = input
  · subst heq
    rw [QueryCache.cacheQuery_self] at hanswer
    cases hanswer
    exact hmiss
  · rw [QueryCache.cacheQuery_of_ne cache output heq] at hanswer
    exact hclean queried answer hanswer

/-- One fresh hash answer truncates to a value fixed in advance with probability `2 ^ -128`. -/
theorem prob_truncate_eq (target : Digest) :
    Pr[fun output : HashOutput => Hashing.truncate output = target |
      ($ᵗ HashOutput : ProbComp HashOutput)] = 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hmap : Pr[fun output : HashOutput => Hashing.truncate output = target |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      Pr[fun digest : Digest => digest = target |
        (Hashing.truncate <$> ($ᵗ HashOutput : ProbComp HashOutput))] := by
    rw [probEvent_map]
    rfl
  rw [hmap, probEvent_congr' (fun _ _ => Iff.rfl) KeygenUniform.truncate_uniform,
    probEvent_eq_eq_probOutput]
  simp [probOutput_uniformSample, Digest, n]

set_option maxHeartbeats 1000000 in
/-- The linear union bound over charged cache misses. -/
theorem prob_hit_le {α : Type} (computation : OracleComp OracleWorld α) (target : Digest)
    (count : Nat) (initialCache : QueryCache HashSpec)
    (hbound : computation.IsQueryBoundP HashQuery count)
    (hclean : Clean target initialCache) :
    Pr[Hit target | (simulateQ KeygenUniform.rom computation).run initialCache] ≤
      count / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  induction computation using OracleComp.inductionOn generalizing count initialCache with
  | pure value =>
    refine le_of_eq_of_le (b := 0) ?_ (by simp)
    rw [simulateQ_pure, StateT.run_pure]
    refine probEvent_eq_zero fun result hresult hhit => ?_
    rw [support_pure, Set.mem_singleton_iff] at hresult
    subst hresult
    obtain ⟨input, output, hanswer, htrunc⟩ := hhit
    exact hclean input output hanswer htrunc
  | query_bind queried next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
    obtain ⟨hvalid, hrest⟩ := hbound
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases queried with coin | input
    · -- A uniform coin: the cache is untouched and no budget is consumed.
      have hnotHash : ¬ HashQuery (Sum.inl coin) := by simp [HashQuery]
      rw [probEvent_bind_eq_tsum]
      have hstep : ∀ step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run initialCache),
          step.2 = initialCache := by
        intro step hstep
        have hform : ∃ coinValue, (coinValue, initialCache) = step := by
          simpa [KeygenUniform.rom, XmssSecurity.RandomOracleModel.impl, unifFwdImpl] using hstep
        obtain ⟨coinValue, rfl⟩ := hform
        rfl
      calc ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run initialCache] *
            Pr[Hit target | (simulateQ KeygenUniform.rom (next step.1)).run step.2]
          ≤ ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run initialCache] *
              (count / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
            refine ENNReal.tsum_le_tsum fun step => ?_
            by_cases hmem : step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run initialCache)
            · refine mul_le_mul' le_rfl ?_
              rw [hstep step hmem]
              simpa [hnotHash] using ih step.1 count initialCache (hrest step.1) hclean
            · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
              simp
        _ = (∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run initialCache]) *
              (count / ((2 ^ 128 : Nat) : ℝ≥0∞)) := ENNReal.tsum_mul_right
        _ ≤ 1 * (count / ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
            mul_le_mul' tsum_probOutput_le_one le_rfl
        _ = _ := one_mul _
    · -- A charged hash query.
      have hisHash : HashQuery (Sum.inr input) := by simp [HashQuery]
      have hpos : 0 < count := by
        rcases hvalid with hno | hpos
        · exact absurd hisHash hno
        · exact hpos
      have hrest' : ∀ answer, (next answer).IsQueryBoundP HashQuery (count - 1) := by
        intro answer
        simpa [hisHash] using hrest answer
      have hsub : ((count - 1 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) ≤
          (count : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        gcongr
        exact_mod_cast Nat.sub_le count 1
      cases hcached : initialCache input with
      | some cached =>
        -- Already cached: the answer is replayed and the cache is untouched.
        have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
            (pure (cached, initialCache) :
              ProbComp (HashOutput × QueryCache HashSpec)) := by
          change (randomOracle input).run initialCache = _
          rw [QueryImpl.withCaching_run_some _ hcached]
        rw [hrun, pure_bind]
        exact (ih cached (count - 1) initialCache (hrest' cached) hclean).trans hsub
      | none =>
        -- A cache miss: a fresh uniform answer is installed.
        have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
            (fun answer => (answer, initialCache.cacheQuery input answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput) := by
          change (randomOracle input).run initialCache = _
          rw [QueryImpl.withCaching_run_none _ hcached]
          simp [uniformSampleImpl]
        rw [hrun]
        show Pr[Hit target | (($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
          (simulateQ KeygenUniform.rom (next answer)).run
            (initialCache.cacheQuery input answer))] ≤ _
        rw [probEvent_bind_eq_tsum]
        -- Each answer either truncates to the target, costing at most one, or leaves a
        -- clean cache, where the remaining budget applies.
        have hpointwise : ∀ answer : HashOutput,
            Pr[Hit target | (simulateQ KeygenUniform.rom (next answer)).run
                (initialCache.cacheQuery input answer)] ≤
              (if Hashing.truncate answer = target then 1 else 0) +
                ((count - 1 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
          intro answer
          by_cases htrunc : Hashing.truncate answer = target
          · rw [if_pos htrunc]
            exact le_add_right probEvent_le_one
          · rw [if_neg htrunc, zero_add]
            exact ih answer (count - 1) (initialCache.cacheQuery input answer)
              (hrest' answer) (hclean.cacheQuery htrunc)
        calc ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
              Pr[Hit target | (simulateQ KeygenUniform.rom (next answer)).run
                (initialCache.cacheQuery input answer)]
            ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                ((if Hashing.truncate answer = target then 1 else 0) +
                  ((count - 1 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) :=
              ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hpointwise answer)
          _ = (∑' answer : HashOutput, (if Hashing.truncate answer = target then
                  Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] else 0)) +
                (∑' answer : HashOutput,
                    Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)]) *
                  (((count - 1 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
              rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
              refine tsum_congr fun answer => ?_
              rw [mul_add]
              by_cases htrunc : Hashing.truncate answer = target <;> simp [htrunc]
          _ ≤ 1 / ((2 ^ 128 : Nat) : ℝ≥0∞) +
                1 * (((count - 1 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
              refine add_le_add (le_of_eq ?_)
                (mul_le_mul' tsum_probOutput_le_one le_rfl)
              rw [← probEvent_eq_tsum_ite]
              exact prob_truncate_eq target
          _ = (count : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
              rw [one_mul, ENNReal.div_add_div_same]
              congr 1
              have hnat : 1 + (count - 1) = count := by omega
              calc (1 : ℝ≥0∞) + ((count - 1 : Nat) : ℝ≥0∞)
                  = ((1 + (count - 1) : Nat) : ℝ≥0∞) := by push_cast; ring
                _ = (count : ℝ≥0∞) := by rw [hnat]

end SlhDsaSecurity.FreshHitBound
