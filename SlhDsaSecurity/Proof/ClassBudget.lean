import SlhDsaSecurity.Proof.ClassCharge
import SlhDsaSecurity.Proof.GrowthBudget
import SlhDsaSecurity.Proof.QueryCached

/-!
# Counting a run's queries one class at a time

`GrowthBudget.growth_le_count` bounds a run's total cache growth by its total hash count, and
that is what feeds `GrowthCharge.prob_badWithin_le`. The per-class charge needs the same fact
once per class: the growth *at in-class inputs* is at most the number of *in-class queries*.

The split matters because the two classes have different rates, `2 ^ -128` structurally and
`2 ^ -129` on a message input, so charging both budgets at the total `q` would cost
`3q / 2 ^ 129` where the target allows `2 qs + qm`. Counting them separately is what buys the
one unit of slack per message query that `Assembly.le_target_of_classes` spends on the
load-cap defect.

Nothing here is specific to the message class: `classCost` takes an arbitrary predicate on
byte inputs and charges one unit per in-class hash call, so the same lemma serves both
budgets — once for the class and once for its complement, whose counts sum to the total.
-/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.ClassBudget

open ClassCharge GrowthCharge GrowthBudget

/-- One unit per hash call whose input lies in the class; coin flips and out-of-class calls
are free. -/
def classCost (inClass : Bytes → Prop) [DecidablePred inClass] :
    OracleWorld.Domain → Nat :=
  fun queried => match queried with
    | Sum.inl _ => 0
    | Sum.inr input => if inClass input then 1 else 0

/-- The run instrumented with the class counter. -/
def countClass (inClass : Bytes → Prop) [DecidablePred inClass] {α : Type}
    (computation : OracleComp OracleWorld α) : OracleComp OracleWorld (α × Nat) :=
  (fun result => (result.1, Multiplicative.toAdd result.2)) <$>
    (simulateQ (addCostOracle (classCost inClass)) computation).run

@[simp] theorem countClass_pure (inClass : Bytes → Prop) [DecidablePred inClass] {α : Type}
    (value : α) : countClass inClass (pure value : OracleComp OracleWorld α) =
      pure (value, 0) := by
  simp [countClass]

theorem countClass_query_bind (inClass : Bytes → Prop) [DecidablePred inClass] {α : Type}
    (queried : OracleWorld.Domain)
    (next : OracleWorld.Range queried → OracleComp OracleWorld α) :
    countClass inClass (liftM (OracleWorld.query queried) >>= next) =
      liftM (OracleWorld.query queried) >>= fun answer =>
        (fun result => (result.1, classCost inClass queried + result.2)) <$>
          countClass inClass (next answer) := by
  simp only [countClass, simulateQ_bind, simulateQ_spec_query, addCostOracle,
    QueryImpl.withAddCost, QueryImpl.withCost]
  simp [Functor.map_map, map_bind, bind_map_left]

/-- **In-class growth is bounded by the in-class count.** -/
theorem growthOn_le_count (inClass : Bytes → Prop) [DecidablePred inClass] {α : Type}
    (computation : OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec) (result : (α × Nat) × QueryCache HashSpec)
    (hmem : result ∈
      support ((simulateQ KeygenUniform.rom (countClass inClass computation)).run
        initialCache)) :
    GrowthAtMostOn inClass initialCache result.2 result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
    rw [countClass_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hmem
    subst hmem
    intro inputs _ hmembers
    cases inputs with
    | nil => simp
    | cons input rest =>
      obtain ⟨-, hnone, hsome⟩ := hmembers input (by simp)
      exact absurd hnone hsome
  | query_bind queried next ih =>
    rw [countClass_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hmem
    obtain ⟨⟨answer, middleCache⟩, hquery, hrest⟩ := hmem
    rw [simulateQ_map, StateT.run_map, support_map] at hrest
    obtain ⟨inner, hinner, heq⟩ := hrest
    have hgrowth := ih answer middleCache inner hinner
    have hfinal : result.2 = inner.2 := by rw [← heq]
    have hcount : result.1.2 = classCost inClass queried + inner.1.2 := by rw [← heq]
    rcases queried with coin | input
    · -- A coin flip leaves the cache alone and costs nothing.
      have hcache : middleCache = initialCache := by
        symm
        have hform : ∃ coinValue, (coinValue, initialCache) = (answer, middleCache) := by
          simpa [KeygenUniform.rom, XmssSecurity.RandomOracleModel.impl, unifFwdImpl]
            using hquery
        obtain ⟨coinValue, hpair⟩ := hform
        exact congrArg Prod.snd hpair
      rw [hfinal, hcount, classCost]
      rw [hcache] at hgrowth
      simpa using hgrowth
    · -- A hash call. Either branch of the oracle leaves the cache in one of two shapes.
      have hmiddle : middleCache = initialCache.cacheQuery input answer ∨
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
      by_cases hmember : inClass input
      · -- In class: one unit is charged, and the budget may grow by one.
        rw [hfinal, hcount, classCost, if_pos hmember]
        rcases hmiddle with hshape | hshape <;> rw [hshape] at hgrowth
        · exact (GrowthAtMostOn.succ_of_cacheQuery hgrowth).mono (by omega)
        · exact hgrowth.mono (by omega)
      · -- Out of class: nothing is charged, and the class budget is untouched.
        rw [hfinal, hcount, classCost, if_neg hmember, Nat.zero_add]
        rcases hmiddle with hshape | hshape <;> rw [hshape] at hgrowth
        · exact GrowthAtMostOn.of_cacheQuery_other hmember hgrowth
        · exact hgrowth

end SlhDsaSecurity.ClassBudget
