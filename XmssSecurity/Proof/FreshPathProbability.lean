import XmssSecurity.Proof.AdaptiveFreshTarget
import XmssSecurity.Proof.EncodingOracleSimulation

/-! Exact collision probabilities along a path of separately addressed hash calls. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Rom

/-- Follow a sequence of hash addresses, retaining the low digest of each answer. -/
def hashPath (inputs : ℕ → Digest → HashInput) (start : ℕ) : ℕ → Digest → OracleComp HashSpec Digest
  | 0, value => pure value
  | steps + 1, value => do
      let output ← liftM (HashSpec.query (inputs start value))
      hashPath inputs (start + 1) steps (truncateHash output)

theorem hashPath_run_succ (inputs : ℕ → Digest → HashInput) (start steps : ℕ)
    (value : Digest) (cache : QueryCache HashSpec) :
    (simulateQ randomOracle (hashPath inputs start (steps + 1) value)).run cache =
      (randomOracle (inputs start value)).run cache >>= fun result =>
        (simulateQ randomOracle
          (hashPath inputs (start + 1) steps (truncateHash result.1))).run result.2 := by
  simp only [hashPath, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

theorem uniform_truncate_miss_probability (target : Digest) :
    Pr[fun output : HashOutput => truncateHash output ≠ target | $ᵗ HashOutput] =
      1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ := by
  apply ENNReal.eq_sub_of_add_eq (by finiteness)
  simpa only [uniform_truncate_probability, probFailure_uniformSample, tsub_zero, add_comm] using
    probEvent_compl ($ᵗ HashOutput) (fun output => truncateHash output = target)

/-- If the cache contains just the honest input at each path address, a different starting
value misses the honest path with probability `(1 - 2^-128)^steps`. Once the two paths meet,
the cached honest answers keep them together. -/
theorem hashPath_miss_probability (inputs : ℕ → Digest → HashInput) (honest : ℕ → Digest)
    (start steps : ℕ) (value : Digest) (cache : QueryCache HashSpec)
    (hseparate : ∀ i, start ≤ i → i < start + steps →
      ∀ j, start ≤ j → j < start + steps → i ≠ j →
        ∀ left right, inputs i left ≠ inputs j right)
    (hhonest : ∀ i, start ≤ i → i < start + steps →
      ∃ output, cache (inputs i (honest i)) = some output ∧ truncateHash output = honest (i + 1))
    (hfresh : ∀ i, start ≤ i → i < start + steps →
      ∀ other, other ≠ honest i → cache (inputs i other) = none) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 ≠ honest (start + steps) |
      (simulateQ randomOracle (hashPath inputs start steps value)).run cache] =
      if value = honest start then 0 else (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ steps := by
  classical
  induction steps generalizing start value cache with
  | zero => simp [hashPath]
  | succ steps ih =>
      rw [hashPath_run_succ]
      have hsep : ∀ i, start + 1 ≤ i → i < start + 1 + steps →
          ∀ j, start + 1 ≤ j → j < start + 1 + steps → i ≠ j →
            ∀ left right, inputs i left ≠ inputs j right := by
        intro i hi hi' j hj hj' hij
        exact hseparate i (by omega) (by omega) j (by omega) (by omega) hij
      by_cases hvalue : value = honest start
      · rw [if_pos hvalue]
        obtain ⟨output, hcached, houtput⟩ := hhonest start le_rfl (by omega)
        rw [hvalue, randomOracle, QueryImpl.withCaching_run_some _ hcached, pure_bind, houtput]
        have h := ih (start + 1) (honest (start + 1)) cache hsep
          (fun i hi hi' => hhonest i (by omega) (by omega))
          (fun i hi hi' => hfresh i (by omega) (by omega))
        simpa only [show start + 1 + steps = start + (steps + 1) by omega,
          if_pos rfl, if_true] using h
      · rw [if_neg hvalue, randomOracle_run_none_eq_uniformHashOutput _ _
          (hfresh start le_rfl (by omega) value hvalue), uniformHashOutput, bind_map_left]
        have htail (output : HashOutput) :
            Pr[fun result : Digest × QueryCache HashSpec => result.1 ≠ honest (start + (steps + 1)) |
              (simulateQ randomOracle
                (hashPath inputs (start + 1) steps (truncateHash output))).run
                  (cache.cacheQuery (inputs start value) output)] =
              if truncateHash output = honest (start + 1) then 0
              else (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ steps := by
          have h := ih (start + 1) (truncateHash output)
            (cache.cacheQuery (inputs start value) output) hsep ?_ ?_
          · simpa only [show start + 1 + steps = start + (steps + 1) by omega] using h
          · intro i hi hi'
            obtain ⟨answer, hanswer, htarget⟩ := hhonest i (by omega) (by omega)
            refine ⟨answer, ?_, htarget⟩
            rw [QueryCache.cacheQuery_of_ne]
            · exact hanswer
            · exact hseparate i (by omega) (by omega) start le_rfl (by omega) (by omega) _ _
          · intro i hi hi' other hother
            rw [QueryCache.cacheQuery_of_ne]
            · exact hfresh i (by omega) (by omega) other hother
            · exact hseparate i (by omega) (by omega) start le_rfl (by omega) (by omega) _ _
        rw [probEvent_bind_eq_tsum]
        simp_rw [htail]
        calc
          _ = Pr[fun output : HashOutput => truncateHash output ≠ honest (start + 1) | $ᵗ HashOutput] *
              (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ steps := by
            rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
            apply tsum_congr
            intro output
            by_cases h : truncateHash output = honest (start + 1)
            · rw [if_pos h, if_neg (not_not_intro h), mul_zero, zero_mul]
            · rw [if_neg h, if_pos h]
          _ = _ := by rw [uniform_truncate_miss_probability, pow_succ]; ac_rfl

theorem hashPath_hit_probability (inputs : ℕ → Digest → HashInput) (honest : ℕ → Digest)
    (start steps : ℕ) (value : Digest) (cache : QueryCache HashSpec)
    (hseparate : ∀ i, start ≤ i → i < start + steps →
      ∀ j, start ≤ j → j < start + steps → i ≠ j →
        ∀ left right, inputs i left ≠ inputs j right)
    (hhonest : ∀ i, start ≤ i → i < start + steps →
      ∃ output, cache (inputs i (honest i)) = some output ∧ truncateHash output = honest (i + 1))
    (hfresh : ∀ i, start ≤ i → i < start + steps →
      ∀ other, other ≠ honest i → cache (inputs i other) = none) :
    Pr[fun result : Digest × QueryCache HashSpec => result.1 = honest (start + steps) |
      (simulateQ randomOracle (hashPath inputs start steps value)).run cache] =
      if value = honest start then 1 else 1 - (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ steps := by
  have hmiss := hashPath_miss_probability inputs honest start steps value cache hseparate hhonest hfresh
  have hsum := probEvent_compl
    ((simulateQ randomOracle (hashPath inputs start steps value)).run cache)
    (fun result => result.1 = honest (start + steps))
  rw [probFailure_of_liftM_PMF, tsub_zero] at hsum
  have heq := ENNReal.eq_sub_of_add_eq probEvent_ne_top hsum
  rw [hmiss] at heq
  split_ifs at heq ⊢ <;> simpa only [tsub_zero] using heq

/-- Sample a changed starting value and retain it to exclude an unchanged signature. -/
noncomputable def randomHashPath (inputs : ℕ → Digest → HashInput) (start steps : ℕ)
    (cache : QueryCache HashSpec) : ProbComp (Digest × (Digest × QueryCache HashSpec)) := do
  let value ← $ᵗ Digest
  let result ← (simulateQ randomOracle (hashPath inputs start steps value)).run cache
  return (value, result)

/-- The first factor excludes an unchanged starting value; the second is the probability
that the altered path meets the honest path during verification. -/
theorem randomHashPath_distinct_hit_probability
    (inputs : ℕ → Digest → HashInput) (honest : ℕ → Digest)
    (start steps : ℕ) (cache : QueryCache HashSpec)
    (hseparate : ∀ i, start ≤ i → i < start + steps →
      ∀ j, start ≤ j → j < start + steps → i ≠ j →
        ∀ left right, inputs i left ≠ inputs j right)
    (hhonest : ∀ i, start ≤ i → i < start + steps →
      ∃ output, cache (inputs i (honest i)) = some output ∧ truncateHash output = honest (i + 1))
    (hfresh : ∀ i, start ≤ i → i < start + steps →
      ∀ other, other ≠ honest i → cache (inputs i other) = none) :
    Pr[fun result => result.1 ≠ honest start ∧ result.2.1 = honest (start + steps) |
      randomHashPath inputs start steps cache] =
      (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) *
        (1 - (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ steps) := by
  classical
  have huniform : Pr[fun value : Digest => value ≠ honest start | $ᵗ Digest] =
      1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ := by
    have htarget : Pr[fun value : Digest => value = honest start | $ᵗ Digest] =
        ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ := by simp
    apply ENNReal.eq_sub_of_add_eq (by finiteness)
    simpa only [htarget, probFailure_uniformSample, tsub_zero, add_comm] using
      probEvent_compl ($ᵗ Digest) (fun value => value = honest start)
  unfold randomHashPath
  rw [probEvent_bind_eq_tsum]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  calc
    _ = Pr[fun value : Digest => value ≠ honest start | $ᵗ Digest] *
        (1 - (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ steps) := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro value
      by_cases hvalue : value = honest start
      · simp [hvalue]
      · simp only [ne_eq, hvalue, not_false_eq_true, true_and, if_true]
        rw [hashPath_hit_probability inputs honest start steps value cache hseparate hhonest hfresh,
          if_neg hvalue]
    _ = _ := by rw [huniform]

/-- info: 'XmssSecurity.Rom.randomHashPath_distinct_hit_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms randomHashPath_distinct_hit_probability

end XmssSecurity.Rom
