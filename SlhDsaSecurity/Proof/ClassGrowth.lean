import SlhDsaSecurity.Proof.AdversaryQueries
import SlhDsaSecurity.Proof.ClassCharge

/-!
# Growth inside one class never exceeds that class's own queries

`ClassCharge.prob_badWithinClasses_le` charges a bad answer at the rate of its own class and
spends only that class's growth budget. To use it, that budget has to be bounded, and bounding
it by the whole growth throws away everything the class was for: the `PRF_msg` class is where a
single defect lives, while the total growth is a whole half of the target.

What bounds it is the obvious thing, proved the same way `GrowthBudget.growth_le_count` proves
its unrestricted form: a cache entry is only ever created by a query at its own input, so an
entry inside the class is created by a query inside the class. Reading the class's queries off
the same `Security.countQueries` instrumentation the rest of the accounting uses keeps the
counter in a form the phase-by-phase arguments already know how to split.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.ClassGrowth

open Security GrowthCharge ClassCharge

open scoped Classical in
/-- One unit for a hash call at an input of the class, nothing for anything else. -/
noncomputable def classCost (inClass : Bytes → Prop) : OracleWorld.Domain → Counts
  | .inl _ => 0
  | .inr input => if inClass input then Counts.single .hash 1 else 0

open scoped Classical in
theorem classCost_inl (inClass : Bytes → Prop) (coin : unifSpec.Domain) :
    classCost inClass (Sum.inl coin) = 0 := rfl

open scoped Classical in
theorem classCost_inr_hash (inClass : Bytes → Prop) (input : Bytes) :
    (classCost inClass (Sum.inr input)) .hash = if inClass input then 1 else 0 := by
  classical
  rw [classCost]
  split
  · exact Pi.single_eq_same _ _
  · rfl

open scoped Classical in
/-- **One hash call, at the clean type.** A call installs at most one entry, and it is inside
the class only when the call itself is. -/
theorem growthOn_step (inClass : Bytes → Prop) (input : Bytes)
    (initialCache middleCache finalCache : QueryCache HashSpec) (limit : Nat)
    (answer : HashOutput)
    (hquery : (answer, middleCache) ∈ support ((randomOracle input).run initialCache))
    (hgrowth : GrowthAtMostOn inClass middleCache finalCache limit) :
    GrowthAtMostOn inClass initialCache finalCache
      ((if inClass input then 1 else 0) + limit) := by
  classical
  cases hcached : initialCache input with
  | some cached =>
    rw [QueryImpl.withCaching_run_some _ hcached, support_pure, Set.mem_singleton_iff] at hquery
    rw [show middleCache = initialCache from (Prod.ext_iff.mp hquery).2] at hgrowth
    exact GrowthAtMostOn.mono hgrowth (by split <;> omega)
  | none =>
    rw [QueryImpl.withCaching_run_none _ hcached, support_map] at hquery
    obtain ⟨sampled, -, hpair⟩ := hquery
    rw [show middleCache = initialCache.cacheQuery input sampled from
      (Prod.ext_iff.mp hpair).2.symm] at hgrowth
    by_cases hmember : inClass input
    · rw [if_pos hmember, Nat.add_comm]
      exact GrowthAtMostOn.succ_of_cacheQuery hgrowth
    · rw [if_neg hmember, Nat.zero_add]
      exact GrowthAtMostOn.of_cacheQuery_other hmember hgrowth

set_option maxHeartbeats 1000000 in
/-- **A class's growth never exceeds that class's own query count.** -/
theorem growthOn_le_classCount (inClass : Bytes → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec)
    (result : (α × Counts) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (countQueries (classCost inClass) computation)).run initialCache)) :
    GrowthAtMostOn inClass initialCache result.2 (result.1.2 .hash) := by
  classical
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
    rw [VerificationBudget.countQueries_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    subst hmem
    intro inputs _ hmembers
    cases inputs with
    | nil => simp
    | cons input rest =>
      obtain ⟨-, hnone, hsome⟩ := hmembers input (by simp)
      exact absurd hnone hsome
  | query_bind queried next ih =>
    rw [WarmedSplit.countQueries_query_bind, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨answer, middleCache⟩, hquery, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    have hgrowth := ih answer middleCache inner hinner
    have hfinal : result.2 = inner.2 := by rw [← heq]
    have hcount : result.1.2 .hash =
        (classCost inClass queried) .hash + inner.1.2 .hash := by rw [← heq]; rfl
    rcases queried with coin | input
    · -- A uniform coin costs nothing and leaves the cache alone.
      have hform : (answer, middleCache) ∈
          Set.range (fun value : OracleWorld.Range (Sum.inl coin) => (value, initialCache)) := by
        simpa [KeygenUniform.rom, XmssSecurity.RandomOracleModel.impl, unifFwdImpl] using hquery
      obtain ⟨value, hvalue⟩ := hform
      rw [show middleCache = initialCache from (Prod.ext_iff.mp hvalue).2.symm] at hgrowth
      rw [hfinal, hcount, classCost_inl]
      exact GrowthAtMostOn.mono hgrowth (by simp)
    · -- A hash call installs at most one entry, and charges the class exactly when it is in it.
      rw [hfinal, hcount, classCost_inr_hash]
      exact growthOn_step inClass input initialCache middleCache inner.2 (inner.1.2 .hash)
        answer hquery hgrowth

end SlhDsaSecurity.ClassGrowth
