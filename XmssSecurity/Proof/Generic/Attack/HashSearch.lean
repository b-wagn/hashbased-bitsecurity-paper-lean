import XmssSecurity.Proof.Generic.FreshPathProbability
import XmssSecurity.Proof.Generic.CacheQuerySupport

/-! Bounded hash search, with exact fresh-input failure probability and cached-hit success. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Generic.Attack

variable [Code]

/-- Search consecutive candidates, stopping at the first acceptable hash output. -/
def findHash (inputs : ℕ → HashInput) (accept : Digest → Prop) [DecidablePred accept]
    (start : ℕ) : ℕ → OracleComp HashSpec (Option (ℕ × Digest))
  | 0 => pure none
  | steps + 1 => do
      let output ← liftM (HashSpec.query (inputs start))
      if accept output then pure (some (start, output))
      else findHash inputs accept (start + 1) steps

theorem findHash_run_succ (inputs : ℕ → HashInput) (accept : Digest → Prop) [DecidablePred accept]
    (start steps : ℕ) (cache : QueryCache HashSpec) :
    (simulateQ randomOracle (findHash inputs accept start (steps + 1))).run cache =
      (randomOracle (inputs start)).run cache >>= fun result =>
        (simulateQ randomOracle (if accept result.1 then pure (some (start, result.1))
          else findHash inputs accept (start + 1) steps)).run result.2 := by
  simp only [findHash, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

theorem findHash_queryBound (inputs : ℕ → HashInput) (accept : Digest → Prop) [DecidablePred accept]
    (start steps : ℕ) : (findHash inputs accept start steps).IsQueryBoundP (fun _ => True) steps := by
  induction steps generalizing start with
  | zero => simp [findHash]
  | succ steps ih =>
      rw [findHash, OracleComp.isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr (by omega), ?_⟩
      intro output
      simp only [if_true, Nat.add_sub_cancel]
      split
      · exact OracleComp.isQueryBoundP_pure _ _ _
      · exact ih (start + 1)

theorem findHash_queryBound_zero
    (inputs : ℕ → HashInput) (accept : Digest → Prop) [DecidablePred accept]
    (start steps : ℕ) (predicate : HashInput → Prop) [DecidablePred predicate]
    (hother : ∀ i, start ≤ i → i < start + steps → ¬predicate (inputs i)) :
    (findHash inputs accept start steps).IsQueryBoundP predicate 0 := by
  induction steps generalizing start with
  | zero => simp [findHash]
  | succ steps ih =>
      rw [findHash, OracleComp.isQueryBoundP_query_bind_iff]
      have hne := hother start le_rfl (by omega)
      refine ⟨Or.inl hne, ?_⟩
      intro output
      simp only [if_neg hne]
      split
      · exact OracleComp.isQueryBoundP_pure _ _ _
      · exact ih (start + 1) (fun i hi hiEnd => hother i (by omega) (by omega))

theorem findHash_queryBound_zero_at_other_input
    (inputs : ℕ → HashInput) (accept : Digest → Prop) [DecidablePred accept]
    (start steps : ℕ) (target : HashInput)
    (hother : ∀ i, start ≤ i → i < start + steps → inputs i ≠ target) :
    (findHash inputs accept start steps).IsQueryBoundP (· = target) 0 :=
  findHash_queryBound_zero inputs accept start steps (· = target) hother

theorem findHash_preserves_unqueriedInput
    (inputs : ℕ → HashInput) (accept : Digest → Prop) [DecidablePred accept]
    (start steps : ℕ) (target : HashInput)
    (hother : ∀ i, start ≤ i → i < start + steps → inputs i ≠ target)
    (initialCache finalCache : QueryCache HashSpec) (result : Option (ℕ × Digest))
    (hmem : (result, finalCache) ∈ support
      ((simulateQ randomOracle (findHash inputs accept start steps)).run initialCache)) :
    finalCache target = initialCache target := by
  cases hcached : initialCache target with
  | none =>
      exact Concrete.CacheReplay.cache_none_of_zero_query_bound _ target initialCache finalCache result
        (findHash_queryBound_zero_at_other_input inputs accept start steps target hother) hcached hmem
  | some output =>
      exact Concrete.CacheReplay.randomOracle_cache_le _ initialCache (result, finalCache) hmem hcached

theorem findHash_failure_fresh (inputs : ℕ → HashInput) (accept : Digest → Prop) [DecidablePred accept]
    (start steps : ℕ) (cache : QueryCache HashSpec)
    (hseparate : ∀ i, start ≤ i → i < start + steps →
      ∀ j, start ≤ j → j < start + steps → i ≠ j → inputs i ≠ inputs j)
    (hfresh : ∀ i, start ≤ i → i < start + steps → cache (inputs i) = none) :
    Pr[fun result => result.1 = none | (simulateQ randomOracle (findHash inputs accept start steps)).run cache] =
      (Pr[fun output : Digest => ¬accept output | $ᵗ Digest]) ^ steps := by
  induction steps generalizing start cache with
  | zero => simp only [findHash, simulateQ_pure, StateT.run_pure, probEvent_pure, pow_zero, if_true]
  | succ steps ih =>
      rw [findHash_run_succ, randomOracle_run_none_eq_uniformHashOutput _ _ (hfresh start le_rfl (by omega))]
      simp only [uniformHashOutput, bind_map_left]
      have htail : ∀ output : Digest,
          Pr[fun result => result.1 = none |
            (simulateQ randomOracle (if accept output then pure (some (start, output))
              else findHash inputs accept (start + 1) steps)).run
                (cache.cacheQuery (inputs start) output)] =
            if accept output then 0 else
              (Pr[fun answer : Digest => ¬accept answer | $ᵗ Digest]) ^ steps := by
        intro output
        by_cases haccept : accept output
        · simp [haccept]
        · rw [if_neg haccept, if_neg haccept]
          apply ih (start + 1)
          · intro i hi hiEnd j hj hjEnd hne
            exact hseparate i (by omega) (by omega) j (by omega) (by omega) hne
          · intro i hi hiEnd
            rw [QueryCache.cacheQuery_of_ne]
            · exact hfresh i (by omega) (by omega)
            · exact hseparate i (by omega) (by omega) start le_rfl (by omega) (by omega)
      rw [probEvent_bind_eq_tsum]
      simp_rw [htail]
      calc
        _ = Pr[fun output : Digest => ¬accept output | $ᵗ Digest] *
            (Pr[fun output : Digest => ¬accept output | $ᵗ Digest]) ^ steps := by
          rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
          apply tsum_congr
          intro output
          by_cases haccept : accept output <;> simp [haccept]
        _ = _ := by rw [pow_succ]; ac_rfl

theorem findHash_failure_zero_of_cached_hit
    (inputs : ℕ → HashInput) (accept : Digest → Prop) [DecidablePred accept]
    (start steps : ℕ) (cache : QueryCache HashSpec)
    (position : ℕ) (hstart : start ≤ position) (hend : position < start + steps)
    (output : Digest) (hcached : cache (inputs position) = some output) (haccept : accept output) :
    Pr[fun result => result.1 = none |
      (simulateQ randomOracle (findHash inputs accept start steps)).run cache] = 0 := by
  induction steps generalizing start cache with
  | zero => omega
  | succ steps ih =>
      rw [findHash_run_succ]
      by_cases hposition : position = start
      · subst position
        rw [QueryImpl.withCaching_run_some _ hcached]
        simp [haccept]
      · rw [probEvent_bind_eq_tsum]
        apply ENNReal.tsum_eq_zero.mpr
        rintro ⟨answer, nextCache⟩
        by_cases hmem : (answer, nextCache) ∈ support ((randomOracle (inputs start)).run cache)
        · have hle : cache ≤ nextCache :=
            QueryImpl.withCaching_cache_le uniformSampleImpl (inputs start) cache (answer, nextCache) hmem
          by_cases hanswer : accept answer
          · simp [hanswer]
          · rw [if_neg hanswer, ih (start + 1) nextCache (by omega) (by omega) (hle hcached)]
            simp
        · rw [probOutput_eq_zero_of_not_mem_support hmem]
          simp

theorem findHash_success_cached (inputs : ℕ → HashInput) (accept : Digest → Prop) [DecidablePred accept]
    (start steps : ℕ) (initialCache finalCache : QueryCache HashSpec) (position : ℕ) (output : Digest)
    (hmem : (some (position, output), finalCache) ∈ support
      ((simulateQ randomOracle (findHash inputs accept start steps)).run initialCache)) :
    start ≤ position ∧ position < start + steps ∧ accept output ∧ finalCache (inputs position) = some output := by
  induction steps generalizing start initialCache with
  | zero => simp [findHash] at hmem
  | succ steps ih =>
      rw [findHash_run_succ, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, middleCache⟩, hquery, htail⟩ := hmem
      by_cases hanswer : accept answer
      · rw [if_pos hanswer] at htail
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, Option.some.injEq] at htail
        obtain ⟨⟨hposition, houtput⟩, hcache⟩ := htail
        subst position
        subst output
        subst finalCache
        exact ⟨le_rfl, by omega, hanswer,
          Concrete.CacheReplay.randomOracle_query_caches _ _ _ _ hquery⟩
      · rw [if_neg hanswer] at htail
        obtain ⟨hstart, hend, haccept, hcached⟩ := ih (start + 1) middleCache htail
        exact ⟨by omega, by omega, haccept, hcached⟩

/-- info: 'XmssSecurity.Generic.Attack.findHash_failure_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms findHash_failure_fresh

/-- info: 'XmssSecurity.Generic.Attack.findHash_failure_zero_of_cached_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms findHash_failure_zero_of_cached_hit

/-- info: 'XmssSecurity.Generic.Attack.findHash_success_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms findHash_success_cached

end XmssSecurity.Generic.Attack
