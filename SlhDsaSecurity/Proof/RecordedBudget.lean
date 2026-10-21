import SlhDsaSecurity.Proof.RecordedQueries
import SlhDsaSecurity.Proof.WarmedCharges

/-!
# The budget, carried to the recorded game

`RecordedQueries.card_toFinset_le` bounds the recorded set by whatever bound is available on the
work this run charges. `Security.HasTotalBudget` is such a bound, but it speaks about
`Security.runAll` — the unwarmed, unstripped, uninstrumented game. This file carries it across
the three steps that separate them.

Each step is a transfer of an almost-sure property across equal laws, and none of them touches
the counters: warming changes the cache and not the outcome, stripping changes what the honest
phase asks and not what the outcome reports, and the recording is invisible. That the `Outcome`
survives all three unchanged is exactly why the work budget — rather than the total hash count,
which stripping does lower — is the quantity to carry.

The one small gap to bridge is that `WarmedGame.tail` is counted while the stripped and recorded
games are not. `map_countAllHashes` closes it: the counter only decorates the value, so
forgetting it returns the computation itself, and a supported uncounted run therefore has a
supported counted counterpart.
-/

open OracleComp OracleSpec

namespace SlhDsaSecurity.RecordedBudget

open Security WarmedGame

/-- **Forgetting the count returns the computation.** -/
theorem map_countAllHashes {α : Type} (computation : OracleComp OracleWorld α) :
    Prod.fst <$> countAllHashes computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rw [GrowthBudget.countAllHashes_pure, map_pure]
  | query_bind queried next ih =>
    rw [GrowthBudget.countAllHashes_query_bind, map_bind]
    exact congrArg (Bind.bind _) (funext fun answer => by
      rw [Functor.map_map]
      exact ih answer)

/-- Every supported uncounted run has a supported counted counterpart. -/
theorem mem_support_countAllHashes {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (result : α × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ KeygenUniform.rom computation).run cache)) :
    ∃ count : Nat, ((result.1, count), result.2) ∈
      support ((simulateQ KeygenUniform.rom (countAllHashes computation)).run cache) := by
  rw [← map_countAllHashes computation, simulateQ_map, StateT.run_map, support_map] at hmem
  obtain ⟨inner, hinner, heq⟩ := hmem
  refine ⟨inner.1.2, ?_⟩
  rw [show result.1 = inner.1.1 from by rw [← heq], show result.2 = inner.2 from by rw [← heq]]
  exact hinner

attribute [local irreducible] WarmedGame.afterSeeds StrippedGame.strippedAfterSeeds
  RecordedQueries.recordedAfterSeeds Scheme.verify Scheme.keygenInternal Security.countQueries

/-- **The budget bounds the work the warmed tail charges.** -/
theorem work_le_of_budget_tail {adversary : Adversary} {q : Nat}
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (tail adversary walk)) :
    result.1.1.counts.work ≤ q :=
  le_trans (AdversaryQueries.work_le_total adversary walk.1.1 walk.2 result hresult)
    (WarmedCharges.count_le_of_budget_tail hbudget hwalk hresult)

/-- **The budget bounds the work the recorded game charges.** -/
theorem work_le_of_budget_recorded {adversary : Adversary} {q : Nat}
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Multiset Bytes) × QueryCache HashSpec}
    (hresult : result ∈ support ((simulateQ KeygenUniform.rom
      (RecordedQueries.recordedAfterSeeds adversary walk.1.1 walk.2)).run walk.2)) :
    result.1.1.counts.work ≤ q := by
  -- The recording is invisible.
  have hstripped : (result.1.1, result.2) ∈ support ((simulateQ KeygenUniform.rom
      (StrippedGame.strippedAfterSeeds adversary walk.1.1 walk.2)).run walk.2) := by
    rw [← RecordedQueries.map_recordedAfterSeeds, simulateQ_map, StateT.run_map, support_map]
    exact ⟨result, hresult, rfl⟩
  -- Stripping the honest phase leaves the law alone.
  rw [Averaging.support_eq_of_evalDist_eq (StrippedGame.evalDist_run_strippedAfterSeeds
    adversary walk.1.1 walk.2 walk.2 (StrippedGame.Extends.refl walk.2))] at hstripped
  -- A supported uncounted run has a supported counted counterpart.
  obtain ⟨count, hcounted⟩ :=
    mem_support_countAllHashes _ walk.2 (result.1.1, result.2) hstripped
  exact work_le_of_budget_tail hbudget hwalk hcounted

/-- **The adversary and the verifier between them ask about at most `q` inputs.** -/
theorem card_toFinset_le_of_budget {adversary : Adversary} {q : Nat}
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Multiset Bytes) × QueryCache HashSpec}
    (hresult : result ∈ support ((simulateQ KeygenUniform.rom
      (RecordedQueries.recordedAfterSeeds adversary walk.1.1 walk.2)).run walk.2)) :
    (Multiset.toFinset result.1.2).card ≤ q :=
  RecordedQueries.card_toFinset_le adversary walk.1.1 walk.2 walk.2 q result hresult
    (work_le_of_budget_recorded hbudget hwalk hresult)

end SlhDsaSecurity.RecordedBudget
