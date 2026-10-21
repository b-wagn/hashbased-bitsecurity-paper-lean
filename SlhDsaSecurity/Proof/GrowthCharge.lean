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

/-- Cache entries are never *overwritten* either: an installed answer persists verbatim.

This is the strengthening of `cache_mono` that the partial-random-function invariant needs.
It is what makes a run started from the **empty** cache enough, where the `FreshFor`
hypothesis of the fresh-sampling results — freshness at the moment of the query — is not
available in the experiment, because the adversary may query a signer's input first. Once an
answer is installed, whoever installed it, every later query returns that same answer. -/
theorem cache_value_persists {α : Type} (computation : OracleComp OracleWorld α)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ KeygenUniform.rom computation).run initialCache))
    (input : Bytes) (output : HashOutput) (hentry : initialCache input = some output) :
    finalCache input = some output := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache finalCache result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    exact hmem.2 ▸ hentry
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨answer, middleCache⟩, hquery, hrest⟩ := hmem
    have hmiddle : middleCache input = some output := by
      rcases queried with coin | queried
      · have hcache : middleCache = initialCache := by
          symm
          simpa [KeygenUniform.rom, XmssSecurity.RandomOracleModel.impl, unifFwdImpl] using hquery
        exact hcache ▸ hentry
      · change (answer, middleCache) ∈ support ((randomOracle queried).run initialCache) at hquery
        cases hqueried : initialCache queried with
        | none =>
          rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hquery
          obtain ⟨sampled, _, hpair⟩ := hquery
          have hmid : middleCache = initialCache.cacheQuery queried sampled :=
            (Prod.ext_iff.mp hpair).2.symm
          rw [hmid]
          have hne : input ≠ queried := by
            intro hsame
            rw [hsame, hqueried] at hentry
            simp at hentry
          rw [QueryCache.cacheQuery_of_ne initialCache sampled hne]
          exact hentry
        | some cached =>
          rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
            Set.mem_singleton_iff] at hquery
          have hmid : middleCache = initialCache := (Prod.ext_iff.mp hquery).2
          exact hmid ▸ hentry
    exact ih answer middleCache finalCache result hrest hmiddle

/-! ## Pinning one coordinate

With `cache_value_persists`, the answer recorded at a given input is decided by whichever
query first missed on it, and never changes afterwards. That yields a bound charging only
**that one** miss, rather than every miss as `prob_badWithin_le` does: the cache value at a
fixed input hits a fixed target with probability at most `2 ^ -240`, independently of how
many queries the run makes.

Freshness is required only of the **starting** cache, which the experiment provides (it
begins empty). This is the point where the `FreshFor` obstruction — freshness at the moment
of the query, which adaptive prequeries deny — is avoided, and it is the single-coordinate
case of the partial-random-function invariant that the disclosure load cap needs.
-/

set_option maxHeartbeats 1000000 in
theorem prob_cache_value_le {α : Type} (computation : OracleComp OracleWorld α)
    (input : Bytes) (target : HashOutput) (cache : QueryCache HashSpec)
    (hfresh : cache input = none) :
    Pr[fun result : α × QueryCache HashSpec => result.2 input = some target |
      (simulateQ KeygenUniform.rom computation).run cache] ≤
      1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
    refine le_of_eq_of_le (b := 0) ?_ (by simp)
    rw [simulateQ_pure, StateT.run_pure]
    refine probEvent_eq_zero fun result hresult hvalue => ?_
    rw [support_pure, Set.mem_singleton_iff] at hresult
    subst hresult
    have hvalue' : cache input = some target := hvalue
    rw [hfresh] at hvalue'
    simp at hvalue'
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases queried with coin | queried
    · -- A uniform coin leaves the cache alone.
      rw [probEvent_bind_eq_tsum]
      have hstep : ∀ step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run cache),
          step.2 = cache := by
        intro step hstep
        have hform : ∃ coinValue, (coinValue, cache) = step := by
          simpa [KeygenUniform.rom, XmssSecurity.RandomOracleModel.impl, unifFwdImpl] using hstep
        obtain ⟨coinValue, rfl⟩ := hform
        rfl
      calc ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run cache] *
            Pr[fun result : α × QueryCache HashSpec => result.2 input = some target |
              (simulateQ KeygenUniform.rom (next step.1)).run step.2]
          ≤ ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run cache] *
              (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) := by
            refine ENNReal.tsum_le_tsum fun step => ?_
            by_cases hmem : step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run cache)
            · refine mul_le_mul' le_rfl ?_
              rw [hstep step hmem]
              exact ih step.1 cache hfresh
            · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
              simp
        _ = (∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run cache]) *
              (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) := ENNReal.tsum_mul_right
        _ ≤ 1 * (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) :=
            mul_le_mul' tsum_probOutput_le_one le_rfl
        _ = _ := one_mul _
    · by_cases hsame : queried = input
      · -- The query is at the pinned input, and the cache is fresh there, so it misses.
        subst hsame
        have hrun : (KeygenUniform.rom (Sum.inr queried)).run cache =
            (fun answer => (answer, cache.cacheQuery queried answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput) := by
          change (randomOracle queried).run cache = _
          rw [QueryImpl.withCaching_run_none _ hfresh]
          simp [uniformSampleImpl]
        rw [hrun]
        show Pr[fun result : α × QueryCache HashSpec => result.2 queried = some target |
          (($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
            (simulateQ KeygenUniform.rom (next answer)).run
              (cache.cacheQuery queried answer))] ≤ _
        rw [probEvent_bind_eq_tsum]
        have hpointwise : ∀ answer : HashOutput,
            Pr[fun result : α × QueryCache HashSpec => result.2 queried = some target |
                (simulateQ KeygenUniform.rom (next answer)).run
                  (cache.cacheQuery queried answer)] ≤
              (if answer = target then 1 else 0) := by
          intro answer
          by_cases hanswer : answer = target
          · rw [if_pos hanswer]
            exact probEvent_le_one
          · rw [if_neg hanswer]
            refine le_of_eq_of_le (b := 0) ?_ le_rfl
            refine probEvent_eq_zero fun result hresult hvalue => ?_
            have hpinned : result.2 queried = some answer :=
              cache_value_persists (next answer) (cache.cacheQuery queried answer) result.2
                result.1 hresult queried answer (by rw [QueryCache.cacheQuery_self])
            rw [hpinned] at hvalue
            exact hanswer (Option.some.inj hvalue)
        calc ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
              Pr[fun result : α × QueryCache HashSpec => result.2 queried = some target |
                (simulateQ KeygenUniform.rom (next answer)).run
                  (cache.cacheQuery queried answer)]
            ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                (if answer = target then 1 else 0) :=
              ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hpointwise answer)
          _ = Pr[= target | ($ᵗ HashOutput : ProbComp HashOutput)] := by
              rw [tsum_eq_single target (by intro other hother; simp [hother])]
              simp
          _ = _ := by simp [probOutput_uniformSample]
      · -- A query elsewhere leaves the pinned input absent.
        rw [probEvent_bind_eq_tsum]
        have hstep : ∀ step ∈ support ((KeygenUniform.rom (Sum.inr queried)).run cache),
            step.2 input = none := by
          intro step hstep
          change step ∈ support ((randomOracle queried).run cache) at hstep
          cases hqueried : cache queried with
          | none =>
            rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hstep
            obtain ⟨sampled, _, hpair⟩ := hstep
            have hmid : step.2 = cache.cacheQuery queried sampled :=
              (Prod.ext_iff.mp hpair).2.symm
            rw [hmid, QueryCache.cacheQuery_of_ne cache sampled (Ne.symm hsame)]
            exact hfresh
          | some cached =>
            rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
              Set.mem_singleton_iff] at hstep
            have hmid : step.2 = cache := (Prod.ext_iff.mp hstep).2
            rw [hmid]
            exact hfresh
        calc ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inr queried)).run cache] *
              Pr[fun result : α × QueryCache HashSpec => result.2 input = some target |
                (simulateQ KeygenUniform.rom (next step.1)).run step.2]
            ≤ ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inr queried)).run cache] *
                (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) := by
              refine ENNReal.tsum_le_tsum fun step => ?_
              by_cases hmem : step ∈ support ((KeygenUniform.rom (Sum.inr queried)).run cache)
              · exact mul_le_mul' le_rfl (ih step.1 step.2 (hstep step hmem))
              · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
                simp
          _ = (∑' step, Pr[= step | (KeygenUniform.rom (Sum.inr queried)).run cache]) *
                (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) := ENNReal.tsum_mul_right
          _ ≤ 1 * (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) :=
              mul_le_mul' tsum_probOutput_le_one le_rfl
          _ = _ := one_mul _

/-! ## Pinning many coordinates: the partial-random-function invariant

Generalising `prob_cache_value_le` from one coordinate to a finite set gives the invariant
the disclosure load cap needs: along any run started from a cache that is absent on a finite
set of inputs, the answers eventually recorded at those inputs behave as independent uniform
draws. Concretely, hitting one prescribed assignment costs `|HashOutput| ^ -|pinned|`.

Summing over a set of assignments then bounds any event defined by the recorded answers, in
particular "the FORS instances of the signed digests violate the load cap". The bound is an
inequality rather than an exact law, which is what makes it robust: the adversary may fail,
and distinct coordinates may be queried in any order and by either party.
-/

set_option maxHeartbeats 1000000 in
theorem prob_cache_values_le {α : Type} (computation : OracleComp OracleWorld α)
    (targets : Bytes → HashOutput) (pinned : Finset Bytes) (cache : QueryCache HashSpec)
    (hfresh : ∀ x ∈ pinned, cache x = none) :
    Pr[fun result : α × QueryCache HashSpec => ∀ x ∈ pinned, result.2 x = some (targets x) |
      (simulateQ KeygenUniform.rom computation).run cache] ≤
      (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ pinned.card := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache pinned with
  | pure value =>
    rcases Finset.eq_empty_or_nonempty pinned with rfl | ⟨witness, hwitness⟩
    · simpa using probEvent_le_one
    · refine le_of_eq_of_le (b := 0) ?_ (by simp)
      rw [simulateQ_pure, StateT.run_pure]
      refine probEvent_eq_zero fun result hresult hvalues => ?_
      rw [support_pure, Set.mem_singleton_iff] at hresult
      subst hresult
      have hvalue : cache witness = some (targets witness) := hvalues witness hwitness
      rw [hfresh witness hwitness] at hvalue
      simp at hvalue
  | query_bind queried next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases queried with coin | queried
    · rw [probEvent_bind_eq_tsum]
      have hstep : ∀ step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run cache),
          step.2 = cache := by
        intro step hstep
        have hform : ∃ coinValue, (coinValue, cache) = step := by
          simpa [KeygenUniform.rom, XmssSecurity.RandomOracleModel.impl, unifFwdImpl] using hstep
        obtain ⟨coinValue, rfl⟩ := hform
        rfl
      calc ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run cache] *
            Pr[fun result : α × QueryCache HashSpec =>
                ∀ x ∈ pinned, result.2 x = some (targets x) |
              (simulateQ KeygenUniform.rom (next step.1)).run step.2]
          ≤ ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run cache] *
              ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ pinned.card) := by
            refine ENNReal.tsum_le_tsum fun step => ?_
            by_cases hmem : step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run cache)
            · refine mul_le_mul' le_rfl ?_
              rw [hstep step hmem]
              exact ih step.1 pinned cache hfresh
            · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
              simp
        _ = (∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run cache]) *
              ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ pinned.card) :=
            ENNReal.tsum_mul_right
        _ ≤ 1 * ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ pinned.card) :=
            mul_le_mul' tsum_probOutput_le_one le_rfl
        _ = _ := one_mul _
    · by_cases hmem : queried ∈ pinned
      · -- The query is at a pinned coordinate, so it misses and fixes that answer.
        have hcached : cache queried = none := hfresh queried hmem
        have hrun : (KeygenUniform.rom (Sum.inr queried)).run cache =
            (fun answer => (answer, cache.cacheQuery queried answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput) := by
          change (randomOracle queried).run cache = _
          rw [QueryImpl.withCaching_run_none _ hcached]
          simp [uniformSampleImpl]
        rw [hrun]
        show Pr[fun result : α × QueryCache HashSpec =>
            ∀ x ∈ pinned, result.2 x = some (targets x) |
          (($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
            (simulateQ KeygenUniform.rom (next answer)).run
              (cache.cacheQuery queried answer))] ≤ _
        rw [probEvent_bind_eq_tsum]
        have hcard : pinned.card = (pinned.erase queried).card + 1 := by
          rw [Finset.card_erase_of_mem hmem]
          have := Finset.card_pos.mpr ⟨queried, hmem⟩
          omega
        have hpointwise : ∀ answer : HashOutput,
            Pr[fun result : α × QueryCache HashSpec =>
                ∀ x ∈ pinned, result.2 x = some (targets x) |
                (simulateQ KeygenUniform.rom (next answer)).run
                  (cache.cacheQuery queried answer)] ≤
              (if answer = targets queried then
                (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ (pinned.erase queried).card
                else 0) := by
          intro answer
          by_cases hanswer : answer = targets queried
          · rw [if_pos hanswer]
            refine le_trans (probEvent_mono ?_)
              (ih answer (pinned.erase queried) (cache.cacheQuery queried answer) ?_)
            · intro result _ hvalues x hx
              exact hvalues x (Finset.mem_of_mem_erase hx)
            · intro x hx
              rw [QueryCache.cacheQuery_of_ne cache answer (Finset.ne_of_mem_erase hx)]
              exact hfresh x (Finset.mem_of_mem_erase hx)
          · rw [if_neg hanswer]
            refine le_of_eq_of_le (b := 0) ?_ le_rfl
            refine probEvent_eq_zero fun result hresult hvalues => ?_
            have hpinnedValue : result.2 queried = some answer :=
              cache_value_persists (next answer) (cache.cacheQuery queried answer) result.2
                result.1 hresult queried answer (by rw [QueryCache.cacheQuery_self])
            have hvalue := hvalues queried hmem
            rw [hpinnedValue] at hvalue
            exact hanswer (Option.some.inj hvalue)
        calc ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
              Pr[fun result : α × QueryCache HashSpec =>
                  ∀ x ∈ pinned, result.2 x = some (targets x) |
                (simulateQ KeygenUniform.rom (next answer)).run
                  (cache.cacheQuery queried answer)]
            ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                (if answer = targets queried then
                  (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ (pinned.erase queried).card
                  else 0) :=
              ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hpointwise answer)
          _ = Pr[= targets queried | ($ᵗ HashOutput : ProbComp HashOutput)] *
                (1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ (pinned.erase queried).card := by
              rw [tsum_eq_single (targets queried) (by intro other hother; simp [hother])]
              simp
          _ = _ := by
              rw [probOutput_uniformSample, hcard, pow_succ]
              rw [one_div]
              ring
      · -- A query at an unpinned coordinate leaves every pinned coordinate absent.
        rw [probEvent_bind_eq_tsum]
        have hstep : ∀ step ∈ support ((KeygenUniform.rom (Sum.inr queried)).run cache),
            ∀ x ∈ pinned, step.2 x = none := by
          intro step hstep x hx
          change step ∈ support ((randomOracle queried).run cache) at hstep
          have hne : x ≠ queried := fun hsame => hmem (hsame ▸ hx)
          cases hqueried : cache queried with
          | none =>
            rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hstep
            obtain ⟨sampled, _, hpair⟩ := hstep
            have hmid : step.2 = cache.cacheQuery queried sampled :=
              (Prod.ext_iff.mp hpair).2.symm
            rw [hmid, QueryCache.cacheQuery_of_ne cache sampled hne]
            exact hfresh x hx
          | some cached =>
            rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
              Set.mem_singleton_iff] at hstep
            have hmid : step.2 = cache := (Prod.ext_iff.mp hstep).2
            rw [hmid]
            exact hfresh x hx
        calc ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inr queried)).run cache] *
              Pr[fun result : α × QueryCache HashSpec =>
                  ∀ x ∈ pinned, result.2 x = some (targets x) |
                (simulateQ KeygenUniform.rom (next step.1)).run step.2]
            ≤ ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inr queried)).run cache] *
                ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ pinned.card) := by
              refine ENNReal.tsum_le_tsum fun step => ?_
              by_cases hstepMem :
                  step ∈ support ((KeygenUniform.rom (Sum.inr queried)).run cache)
              · exact mul_le_mul' le_rfl (ih step.1 pinned step.2 (hstep step hstepMem))
              · rw [probOutput_eq_zero_of_not_mem_support hstepMem, zero_mul]
                simp
          _ = (∑' step, Pr[= step | (KeygenUniform.rom (Sum.inr queried)).run cache]) *
                ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ pinned.card) :=
              ENNReal.tsum_mul_right
          _ ≤ 1 * ((1 / ((Fintype.card HashOutput : Nat) : ℝ≥0∞)) ^ pinned.card) :=
              mul_le_mul' tsum_probOutput_le_one le_rfl
          _ = _ := one_mul _

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

/-! ## The general charge

The charge does not depend on the bad event being "the answer truncates to a target": all it
needs is that each individual fresh answer is bad for its own input with probability at most
`p`. Stating it that way lets the same lemma carry both the structural term (bad = the answer
truncates to the canonical cell of the queried node) and the FORS coverage term (bad = the
answer parses to a digest whose fourteen FORS positions are all already disclosed).
-/

/-- Some cached answer is bad for its own input. -/
def Bad {α : Type} (bad : Bytes → HashOutput → Prop) :
    α × QueryCache HashSpec → Prop := fun result =>
  ∃ input output, result.2 input = some output ∧ bad input output

/-- The cache holds no answer that is bad for its own input. -/
def CleanBad (bad : Bytes → HashOutput → Prop) (cache : QueryCache HashSpec) : Prop :=
  ∀ input output, cache input = some output → ¬ bad input output

theorem CleanBad.cacheQuery {bad : Bytes → HashOutput → Prop} {cache : QueryCache HashSpec}
    (hclean : CleanBad bad cache) {input : Bytes} {output : HashOutput}
    (hmiss : ¬ bad input output) : CleanBad bad (cache.cacheQuery input output) := by
  intro queried answer hanswer
  by_cases heq : queried = input
  · subst heq
    rw [QueryCache.cacheQuery_self] at hanswer
    cases hanswer
    exact hmiss
  · rw [QueryCache.cacheQuery_of_ne cache output heq] at hanswer
    exact hclean queried answer hanswer

def BadWithin {α : Type} (bad : Bytes → HashOutput → Prop)
    (initialCache : QueryCache HashSpec) (limit : Nat) :
    α × QueryCache HashSpec → Prop := fun result =>
  Bad bad result ∧ GrowthAtMost initialCache result.2 limit

set_option maxHeartbeats 1000000 in
/-- **The general linear charge.** If each fresh answer is bad for its own input with
probability at most `p`, then a run whose cache grows by at most `limit` ends with a bad
cached answer with probability at most `limit * p`. -/
theorem prob_badWithin_le {α : Type} (computation : OracleComp OracleWorld α)
    (bad : Bytes → HashOutput → Prop) (p : ℝ≥0∞) (limit : Nat)
    (initialCache : QueryCache HashSpec)
    (hbad : ∀ input, Pr[fun answer : HashOutput => bad input answer |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ p)
    (hclean : CleanBad bad initialCache) :
    Pr[BadWithin bad initialCache limit |
      (simulateQ KeygenUniform.rom computation).run initialCache] ≤ limit * p := by
  classical
  induction computation using OracleComp.inductionOn generalizing limit initialCache with
  | pure value =>
    refine le_of_eq_of_le (b := 0) ?_ (by simp)
    rw [simulateQ_pure, StateT.run_pure]
    refine probEvent_eq_zero fun result hresult hhit => ?_
    rw [support_pure, Set.mem_singleton_iff] at hresult
    subst hresult
    obtain ⟨⟨input, output, hanswer, hbadness⟩, _⟩ := hhit
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
            Pr[BadWithin bad initialCache limit |
              (simulateQ KeygenUniform.rom (next step.1)).run step.2]
          ≤ ∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run initialCache] *
              (limit * p) := by
            refine ENNReal.tsum_le_tsum fun step => ?_
            by_cases hmem : step ∈ support ((KeygenUniform.rom (Sum.inl coin)).run initialCache)
            · refine mul_le_mul' le_rfl ?_
              rw [hstep step hmem]
              exact ih step.1 limit initialCache hclean
            · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
              simp
        _ = (∑' step, Pr[= step | (KeygenUniform.rom (Sum.inl coin)).run initialCache]) *
              (limit * p) := ENNReal.tsum_mul_right
        _ ≤ 1 * (limit * p) := mul_le_mul' tsum_probOutput_le_one le_rfl
        _ = _ := one_mul _
    · cases hcached : initialCache input with
      | some cached =>
        have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
            (pure (cached, initialCache) :
              ProbComp (HashOutput × QueryCache HashSpec)) := by
          change (randomOracle input).run initialCache = _
          rw [QueryImpl.withCaching_run_some _ hcached]
        rw [hrun, pure_bind]
        exact ih cached limit initialCache hclean
      | none =>
        have hrun : (KeygenUniform.rom (Sum.inr input)).run initialCache =
            (fun answer => (answer, initialCache.cacheQuery input answer)) <$>
              ($ᵗ HashOutput : ProbComp HashOutput) := by
          change (randomOracle input).run initialCache = _
          rw [QueryImpl.withCaching_run_none _ hcached]
          simp [uniformSampleImpl]
        rw [hrun]
        show Pr[BadWithin bad initialCache limit |
          (($ᵗ HashOutput : ProbComp HashOutput) >>= fun answer =>
            (simulateQ KeygenUniform.rom (next answer)).run
              (initialCache.cacheQuery input answer))] ≤ _
        cases limit with
        | zero =>
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
              Pr[BadWithin bad initialCache (remaining + 1) |
                  (simulateQ KeygenUniform.rom (next answer)).run
                    (initialCache.cacheQuery input answer)] ≤
                (if bad input answer then 1 else 0) + (remaining : ℝ≥0∞) * p := by
            intro answer
            by_cases hbadness : bad input answer
            · rw [if_pos hbadness]
              exact le_add_right probEvent_le_one
            · rw [if_neg hbadness, zero_add]
              refine le_trans (probEvent_mono ?_)
                (ih answer remaining (initialCache.cacheQuery input answer)
                  (hclean.cacheQuery hbadness))
              intro result hresult hhit
              refine ⟨hhit.1, ?_⟩
              have hpresent : result.2 input ≠ none :=
                cache_mono (next answer) (initialCache.cacheQuery input answer) result.2
                  result.1 hresult input
                  (by rw [QueryCache.cacheQuery_self]; simp)
              simpa using hhit.2.cacheQuery hcached hpresent
          calc ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                Pr[BadWithin bad initialCache (remaining + 1) |
                  (simulateQ KeygenUniform.rom (next answer)).run
                    (initialCache.cacheQuery input answer)]
              ≤ ∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
                  ((if bad input answer then 1 else 0) + (remaining : ℝ≥0∞) * p) :=
                ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (hpointwise answer)
            _ = (∑' answer : HashOutput, (if bad input answer then
                    Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] else 0)) +
                  (∑' answer : HashOutput,
                      Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)]) *
                    ((remaining : ℝ≥0∞) * p) := by
                rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
                refine tsum_congr fun answer => ?_
                rw [mul_add]
                by_cases hbadness : bad input answer <;> simp [hbadness]
            _ ≤ p + 1 * ((remaining : ℝ≥0∞) * p) := by
                refine add_le_add ?_ (mul_le_mul' tsum_probOutput_le_one le_rfl)
                rw [← probEvent_eq_tsum_ite]
                exact hbad input
            _ = ((remaining + 1 : Nat) : ℝ≥0∞) * p := by
                rw [one_mul]
                push_cast
                ring

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
