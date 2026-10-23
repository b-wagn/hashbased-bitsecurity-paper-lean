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

/-! ## Both sides of one split, on one counter

`classCost` counts one class and discards the other, so the two sides of a split can only be
read off two differently instrumented runs — and counts on two different runs do not add
pathwise. `splitCost` charges the class to one slot of the counter and its complement to
another, so a single run carries both, and the sum of the two slots is the run's own hash
count. That sum is what one budget pays for.

The two slots are parameters rather than a fixed pair: nothing here reads a slot's name, and
leaving them free keeps the counter usable whichever two the caller has to spare. -/

open scoped Classical in
/-- **The two-slot class counter.** One unit of `inside` for a hash call at an input of the
class, one unit of `outside` for a hash call anywhere else, nothing for a coin. -/
noncomputable def splitCost (inClass : Bytes → Prop) (inside outside : QueryKind) :
    OracleWorld.Domain → Counts
  | .inl _ => 0
  | .inr input => if inClass input then Counts.single inside 1 else Counts.single outside 1

open scoped Classical in
theorem splitCost_inl (inClass : Bytes → Prop) (inside outside : QueryKind)
    (coin : unifSpec.Domain) : splitCost inClass inside outside (Sum.inl coin) = 0 := rfl

open scoped Classical in
/-- An in-class call is charged one unit of the inside slot. -/
theorem splitCost_inside (inClass : Bytes → Prop) (inside outside : QueryKind) (input : Bytes)
    (hmember : inClass input) :
    (splitCost inClass inside outside (Sum.inr input)) inside = 1 := by
  classical
  rw [splitCost, if_pos hmember]
  exact Pi.single_eq_same _ _

open scoped Classical in
/-- An out-of-class call is charged one unit of the outside slot. -/
theorem splitCost_outside (inClass : Bytes → Prop) (inside outside : QueryKind) (input : Bytes)
    (hmember : ¬ inClass input) :
    (splitCost inClass inside outside (Sum.inr input)) outside = 1 := by
  classical
  rw [splitCost, if_neg hmember]
  exact Pi.single_eq_same _ _

open scoped Classical in
/-- **The two slots add to the hash cost.** Every hash call is charged exactly one unit, to
exactly one of the two slots, and a coin is charged nothing — so the two class counts of a run
add to that run's own hash-query count rather than each equalling it. -/
theorem splitCost_add_eq_hashCost (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside) (queried : OracleWorld.Domain) :
    (splitCost inClass inside outside queried) inside +
        (splitCost inClass inside outside queried) outside = hashCost queried := by
  classical
  rcases queried with coin | input
  · rw [splitCost_inl]
    rfl
  · rw [splitCost]
    by_cases hmember : inClass input
    · rw [if_pos hmember, Counts.single, Pi.single_eq_same, Pi.single_eq_of_ne hne.symm]
      rfl
    · rw [if_neg hmember, Counts.single, Pi.single_eq_of_ne hne, Pi.single_eq_same]
      rfl

/-- **One hash call, at the clean type.** A call installs at most one entry, and it is inside
the class only when the call itself is — so any charge that pays a unit for an in-class call
pays for the entry it may install. -/
theorem growthOn_step_of_charge (inClass : Bytes → Prop) (input : Bytes)
    (initialCache middleCache finalCache : QueryCache HashSpec) (limit charge : Nat)
    (answer : HashOutput)
    (hcharge : inClass input → 1 ≤ charge)
    (hquery : (answer, middleCache) ∈ support ((randomOracle input).run initialCache))
    (hgrowth : GrowthAtMostOn inClass middleCache finalCache limit) :
    GrowthAtMostOn inClass initialCache finalCache (charge + limit) := by
  classical
  cases hcached : initialCache input with
  | some cached =>
    rw [QueryImpl.withCaching_run_some _ hcached, support_pure, Set.mem_singleton_iff] at hquery
    rw [show middleCache = initialCache from (Prod.ext_iff.mp hquery).2] at hgrowth
    exact GrowthAtMostOn.mono hgrowth (by omega)
  | none =>
    rw [QueryImpl.withCaching_run_none _ hcached, support_map] at hquery
    obtain ⟨sampled, -, hpair⟩ := hquery
    rw [show middleCache = initialCache.cacheQuery input sampled from
      (Prod.ext_iff.mp hpair).2.symm] at hgrowth
    by_cases hmember : inClass input
    · exact GrowthAtMostOn.mono (GrowthAtMostOn.succ_of_cacheQuery hgrowth)
        (by have := hcharge hmember; omega)
    · exact GrowthAtMostOn.mono (GrowthAtMostOn.of_cacheQuery_other hmember hgrowth) (by omega)

open scoped Classical in
/-- The same step at the single-class counter. -/
theorem growthOn_step (inClass : Bytes → Prop) (input : Bytes)
    (initialCache middleCache finalCache : QueryCache HashSpec) (limit : Nat)
    (answer : HashOutput)
    (hquery : (answer, middleCache) ∈ support ((randomOracle input).run initialCache))
    (hgrowth : GrowthAtMostOn inClass middleCache finalCache limit) :
    GrowthAtMostOn inClass initialCache finalCache
      ((if inClass input then 1 else 0) + limit) :=
  growthOn_step_of_charge inClass input initialCache middleCache finalCache limit _ answer
    (fun hmember => by rw [if_pos hmember]) hquery hgrowth

set_option maxHeartbeats 1000000 in
/-- **A class's growth never exceeds what the counter charges that class.** Stated at an
arbitrary counter and slot, so one run's counter can answer for a class and for its
complement at once. -/
theorem growthOn_le_count (inClass : Bytes → Prop) (cost : OracleWorld.Domain → Counts)
    (slot : QueryKind) (hcost : ∀ input, inClass input → 1 ≤ cost (Sum.inr input) slot)
    {α : Type} (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec)
    (result : (α × Counts) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (countQueries cost computation)).run initialCache)) :
    GrowthAtMostOn inClass initialCache result.2 (result.1.2 slot) := by
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
    have hcount : result.1.2 slot =
        (cost queried) slot + inner.1.2 slot := by rw [← heq]; rfl
    rcases queried with coin | input
    · -- A uniform coin leaves the cache alone, so whatever it costs is slack.
      have hform : (answer, middleCache) ∈
          Set.range (fun value : OracleWorld.Range (Sum.inl coin) => (value, initialCache)) := by
        simpa [KeygenUniform.rom, Xmss.RandomOracleModel.impl, unifFwdImpl] using hquery
      obtain ⟨value, hvalue⟩ := hform
      rw [show middleCache = initialCache from (Prod.ext_iff.mp hvalue).2.symm] at hgrowth
      rw [hfinal, hcount]
      exact GrowthAtMostOn.mono hgrowth (by omega)
    · -- A hash call installs at most one entry, and the counter pays for it when it is in class.
      rw [hfinal, hcount]
      exact growthOn_step_of_charge inClass input initialCache middleCache inner.2
        (inner.1.2 slot) _ answer (hcost input) hquery hgrowth

open scoped Classical in
/-- **A class's growth never exceeds that class's own query count.** -/
theorem growthOn_le_classCount (inClass : Bytes → Prop) {α : Type}
    (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec)
    (result : (α × Counts) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (countQueries (classCost inClass) computation)).run initialCache)) :
    GrowthAtMostOn inClass initialCache result.2 (result.1.2 .hash) :=
  growthOn_le_count inClass (classCost inClass) .hash
    (fun input hmember => by rw [classCost_inr_hash, if_pos hmember]) computation initialCache
    result hmem

open scoped Classical in
/-- **The inside slot pays for the class's growth.** -/
theorem growthOn_le_splitCount_inside (inClass : Bytes → Prop) (inside outside : QueryKind)
    {α : Type} (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec)
    (result : (α × Counts) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (countQueries (splitCost inClass inside outside) computation)).run initialCache)) :
    GrowthAtMostOn inClass initialCache result.2 (result.1.2 inside) :=
  growthOn_le_count inClass (splitCost inClass inside outside) inside
    (fun input hmember => by rw [splitCost_inside inClass inside outside input hmember])
    computation initialCache result hmem

open scoped Classical in
/-- **The outside slot pays for the complement's growth.** -/
theorem growthOn_le_splitCount_outside (inClass : Bytes → Prop) (inside outside : QueryKind)
    {α : Type} (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec)
    (result : (α × Counts) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (countQueries (splitCost inClass inside outside) computation)).run initialCache)) :
    GrowthAtMostOn (fun input => ¬ inClass input) initialCache result.2 (result.1.2 outside) :=
  growthOn_le_count (fun input => ¬ inClass input) (splitCost inClass inside outside) outside
    (fun input hmember => by rw [splitCost_outside inClass inside outside input hmember])
    computation initialCache result hmem

/-! ## The split counter is the total counter

The two class counts are only worth separating if their *sum* is something the budget already
speaks about. It is: every query is charged its hash cost, split between the two slots, so any
linear readout of the split counter that recovers the hash cost run for run recovers
`countAllHashes`. `GrowthBudget.countAllHashes_eq_component` is the single-slot case of the
same statement.

This is the step that keeps the split honest. The split-counted run is not a new experiment —
it is the all-hashes-counted run with its count resolved into two parts, so whatever bounds the
total bounds the two parts together, with no second budget anywhere. -/

/-- **A linear readout that recovers the hash cost recovers the total count.** -/
theorem countAllHashes_eq_readOff {α : Type} (cost : OracleWorld.Domain → Counts)
    (readOff : Counts → Nat) (hzero : readOff 0 = 0)
    (hadd : ∀ left right : Counts, readOff (left + right) = readOff left + readOff right)
    (hcost : ∀ input, readOff (cost input) = hashCost input)
    (computation : OracleComp OracleWorld α) :
    (fun result : α × Counts => (result.1, readOff result.2)) <$>
        countQueries cost computation = countAllHashes computation := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    rw [VerificationBudget.countQueries_pure, GrowthBudget.countAllHashes_pure, map_pure, hzero]
  | query_bind queried next ih =>
    rw [WarmedSplit.countQueries_query_bind, GrowthBudget.countAllHashes_query_bind, map_bind]
    refine congrArg (fun step => liftM (OracleWorld.query queried) >>= step) ?_
    funext answer
    rw [← ih answer, Functor.map_map, Functor.map_map]
    refine congrArg (fun step => step <$> countQueries cost (next answer)) ?_
    funext inner
    simp only [hadd, hcost]

/-- **The split-counted run is the all-hashes-counted run.** Summing the two class slots turns
one into the other, so an event about the plain run is an event about the split-counted one and
the plain run's budget is a budget for the two counts together. -/
theorem run_countQueries_eq_map_readOff {α : Type} (cost : OracleWorld.Domain → Counts)
    (readOff : Counts → Nat) (hzero : readOff 0 = 0)
    (hadd : ∀ left right : Counts, readOff (left + right) = readOff left + readOff right)
    (hcost : ∀ input, readOff (cost input) = hashCost input)
    (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec) :
    (fun result : (α × Counts) × QueryCache HashSpec =>
          ((result.1.1, readOff result.1.2), result.2)) <$>
        (simulateQ KeygenUniform.rom (countQueries cost computation)).run initialCache =
      (simulateQ KeygenUniform.rom (countAllHashes computation)).run initialCache := by
  rw [← countAllHashes_eq_readOff cost readOff hzero hadd hcost computation, simulateQ_map,
    StateT.run_map]

open scoped Classical in
/-- The sum of the two class slots is a readout of the kind `countAllHashes_eq_readOff` wants. -/
theorem splitSum_add (inside outside : QueryKind) (left right : Counts) :
    (left + right) inside + (left + right) outside =
      (left inside + left outside) + (right inside + right outside) := by
  simp only [Pi.add_apply]
  omega

open scoped Classical in
/-- **The split-counted run, read as the plain run.** -/
theorem run_splitCost_eq_map (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside) {α : Type} (computation : OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec) :
    (fun result : (α × Counts) × QueryCache HashSpec =>
          ((result.1.1, result.1.2 inside + result.1.2 outside), result.2)) <$>
        (simulateQ KeygenUniform.rom
          (countQueries (splitCost inClass inside outside) computation)).run initialCache =
      (simulateQ KeygenUniform.rom (countAllHashes computation)).run initialCache :=
  run_countQueries_eq_map_readOff (splitCost inClass inside outside)
    (fun counts => counts inside + counts outside) rfl (splitSum_add inside outside)
    (splitCost_add_eq_hashCost inClass hne) computation initialCache

open scoped Classical in
/-- **An event about the plain run is an event about the split-counted one.** -/
theorem probEvent_splitCost (inClass : Bytes → Prop) {inside outside : QueryKind}
    (hne : inside ≠ outside) {α : Type} (computation : OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec) (event : (α × Nat) × QueryCache HashSpec → Prop) :
    Pr[event |
        (simulateQ KeygenUniform.rom (countAllHashes computation)).run initialCache] =
      Pr[fun result : (α × Counts) × QueryCache HashSpec =>
          event ((result.1.1, result.1.2 inside + result.1.2 outside), result.2) |
        (simulateQ KeygenUniform.rom
          (countQueries (splitCost inClass inside outside) computation)).run initialCache] := by
  rw [← run_splitCost_eq_map inClass hne computation initialCache, probEvent_map]
  rfl

open scoped Classical in
/-- **The two class counts of a split-counted run are the plain run's own count.** Whatever
bounds the plain run's count therefore bounds the two class counts together — one budget, two
charges. -/
theorem mem_support_countAllHashes_of_splitCost (inClass : Bytes → Prop)
    {inside outside : QueryKind} (hne : inside ≠ outside) {α : Type}
    (computation : OracleComp OracleWorld α) (initialCache : QueryCache HashSpec)
    (result : (α × Counts) × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom
      (countQueries (splitCost inClass inside outside) computation)).run initialCache)) :
    ((result.1.1, result.1.2 inside + result.1.2 outside), result.2) ∈
      support ((simulateQ KeygenUniform.rom (countAllHashes computation)).run initialCache) := by
  rw [← run_splitCost_eq_map inClass hne computation initialCache, support_map]
  exact ⟨result, hmem, rfl⟩

end SlhDsaSecurity.ClassGrowth
