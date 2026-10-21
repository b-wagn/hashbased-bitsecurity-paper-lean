import SlhDsaSecurity.Proof.RecordedQueries
import SlhDsaSecurity.Proof.WarmedCharges
import SlhDsaSecurity.Proof.HonestGrowth
import SlhDsaSecurity.Proof.GraphStakes

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

/-! ## Reserving what key generation spent

Key generation's hash calls are charged to the budget and counted in neither `.hash` nor
`.verification`, so the work the game charges leaves that much of the budget unspent. Reserving
it rather than discarding it is what pays for the forgery's own claimed cells: the input half
records one candidate per claimed cell, a constant `GraphStakes.claimedCount = 259` of them,
against the `2 ^ subtreeHeight = 512` key generation puts back. -/

/-- **The budget bounds the work, with key generation's spend reserved.** -/
theorem work_add_pow_le_of_budget_tail {adversary : Adversary} {q : Nat}
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (tail adversary walk)) :
    result.1.1.counts.work + 2 ^ subtreeHeight ≤ q := by
  obtain ⟨keygenCount, keys, keyCache, hkeys, hbound⟩ :=
    AdversaryQueries.work_add_keygen_le_total adversary walk.1.1 walk.2 result hresult
  have hpow : (2 : Nat) ^ subtreeHeight ≤ keygenCount :=
    HonestGrowth.pow_le_count_keygen walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2
      ⟨⟨keys, keygenCount⟩, keyCache⟩ hkeys
  have htotal := WarmedCharges.count_le_of_budget_tail hbudget hwalk hresult
  omega

/-- The same at the stripped game, which is where a presentation with a table in its state runs:
the recording is one more layer on top, and the work the outcome reports is the same either
way. -/
theorem work_add_pow_le_of_budget_stripped {adversary : Adversary} {q : Nat}
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : Outcome × QueryCache HashSpec}
    (hresult : result ∈ support ((simulateQ KeygenUniform.rom
      (StrippedGame.strippedAfterSeeds adversary walk.1.1 walk.2)).run walk.2)) :
    result.1.counts.work + 2 ^ subtreeHeight ≤ q := by
  rw [Averaging.support_eq_of_evalDist_eq (StrippedGame.evalDist_run_strippedAfterSeeds
    adversary walk.1.1 walk.2 walk.2 (StrippedGame.Extends.refl walk.2))] at hresult
  obtain ⟨count, hcounted⟩ := mem_support_countAllHashes _ walk.2 result hresult
  exact work_add_pow_le_of_budget_tail hbudget hwalk hcounted

/-- The same at the recorded game. -/
theorem work_add_pow_le_of_budget_recorded {adversary : Adversary} {q : Nat}
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Multiset Bytes) × QueryCache HashSpec}
    (hresult : result ∈ support ((simulateQ KeygenUniform.rom
      (RecordedQueries.recordedAfterSeeds adversary walk.1.1 walk.2)).run walk.2)) :
    result.1.1.counts.work + 2 ^ subtreeHeight ≤ q := by
  have hstripped : (result.1.1, result.2) ∈ support ((simulateQ KeygenUniform.rom
      (StrippedGame.strippedAfterSeeds adversary walk.1.1 walk.2)).run walk.2) := by
    rw [← RecordedQueries.map_recordedAfterSeeds, simulateQ_map, StateT.run_map, support_map]
    exact ⟨result, hresult, rfl⟩
  exact work_add_pow_le_of_budget_stripped hbudget hwalk hstripped

/-- **The record, with the forgery's claimed cells appended, fits the budget.** The queries cost
the work the game charged, which the budget bounds by `q` less key generation's spend; the claims
cost their own number, which is a constant. -/
theorem card_toFinset_append_le_of_budget {adversary : Adversary} {q : Nat}
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Multiset Bytes) × QueryCache HashSpec}
    (hresult : result ∈ support ((simulateQ KeygenUniform.rom
      (RecordedQueries.recordedAfterSeeds adversary walk.1.1 walk.2)).run walk.2))
    (claimed : List Bytes) :
    (Multiset.toFinset (result.1.2 + (claimed : Multiset Bytes))).card ≤
      (q - 2 ^ subtreeHeight) + claimed.length := by
  classical
  have hwork := RecordedQueries.card_toFinset_le_work adversary walk.1.1 walk.2 walk.2 result
    hresult
  have hbound := work_add_pow_le_of_budget_recorded hbudget hwalk hresult
  calc (Multiset.toFinset (result.1.2 + (claimed : Multiset Bytes))).card
      ≤ (Multiset.toFinset result.1.2).card +
          (Multiset.toFinset (claimed : Multiset Bytes)).card := by
        rw [Multiset.toFinset_add]
        exact Finset.card_union_le _ _
    _ ≤ (q - 2 ^ subtreeHeight) + claimed.length := by
        refine Nat.add_le_add (by omega) ?_
        exact claimed.toFinset_card_le

/-- **The record at the forgery's own claimed cells, in numbers.** Two hundred and fifty-nine
claims against the five hundred and twelve key generation puts back. -/
theorem card_toFinset_claimed_le_of_budget [HasQuery HashSpec Id] {adversary : Adversary}
    {q : Nat} (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × CanonicalGraph.Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Multiset Bytes) × QueryCache HashSpec}
    (hresult : result ∈ support ((simulateQ KeygenUniform.rom
      (RecordedQueries.recordedAfterSeeds adversary walk.1.1 walk.2)).run walk.2))
    (forsKey : CanonicalGraph.ForsKey) (indices : SlhDsaSecurity.Fors.Indices)
    (signature : Signature) (keyAt : Fin layers → CanonicalGraph.WotsKey)
    (stepAt : Fin layers → Fin chains → Fin (w - 1)) :
    (Multiset.toFinset (result.1.2 +
      ((GraphStakes.claimedCandidates walk.1.1.2.2 forsKey indices signature keyAt stepAt :
        List Bytes) : Multiset Bytes))).card ≤ (q - 2 ^ subtreeHeight) + 259 := by
  have hbound := card_toFinset_append_le_of_budget hbudget hwalk hresult
    (GraphStakes.claimedCandidates walk.1.1.2.2 forsKey indices signature keyAt stepAt)
  rwa [GraphStakes.length_claimedCandidates, GraphStakes.claimedCount] at hbound

end SlhDsaSecurity.RecordedBudget
