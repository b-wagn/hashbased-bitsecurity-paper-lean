import SlhDsaSecurity.Proof.HonestGrowth

/-!
# A budget that admits an adversary at all is at least what key generation spends

The accounting subtracts `2 ^ subtreeHeight` from the budget before handing the remainder to
the charges, and reads `q - 2 ^ subtreeHeight` as a count of hash calls the adversary still
has. On `Nat` that subtraction truncates, so the reading is only honest once `q` is known to
be at least `512`; otherwise the term is `0` and the accounting would be claiming the
adversary has no calls left while the budget says it has some.

The fact is not an assumption about adversaries but a consequence of the budget's own shape.
`HasTotalBudget adversary q` asserts that the count stays within `q` with probability one, and
every run of the game begins by building the top subtree, whose `2 ^ subtreeHeight` compression
calls are charged like any other. So a budget below `512` would be exceeded on every run the
game has — and a probability-one event that holds nowhere forces the support to be empty,
which makes that same probability zero rather than one. Both horns are closed by the one
argument, and in particular nothing here needs the support to be nonempty: if an adversary
always fails, it has no budget to speak of, and the statement holds of it vacuously.

The route to the count is the warmed presentation, where key generation is already isolated:
`HonestGrowth.growth_le_count_sub_keygen` splits a tail's total at the end of key generation
and `HonestGrowth.pow_le_count_keygen` bounds that part below. `WarmedGame.evalDist_outcome`
carries the conclusion back to the unwarmed run the budget is stated against, in the direction
opposite to the one the charges use it in.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.KeygenBudget

open Security WarmedGame CanonicalGraph

attribute [local irreducible] WarmedGame.afterSeeds Scheme.keygenInternal Scheme.verify
  Scheme.sign Security.signingOracle Security.countQueries

set_option maxHeartbeats 1000000 in
/-- **Every warmed tail is charged at least `2 ^ subtreeHeight`.** -/
theorem pow_le_count_tail (adversary : Adversary)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (tail adversary walk)) :
    2 ^ subtreeHeight ≤ result.1.2 := by
  obtain ⟨keygenCount, keys, hkeys, hle, -⟩ :=
    HonestGrowth.growth_le_count_sub_keygen adversary hwalk hresult
  exact le_trans (HonestGrowth.pow_le_count_keygen walk.1.1.1 walk.1.1.2.1 walk.1.1.2.2 walk.2
    ⟨⟨keys, keygenCount⟩, walk.2⟩ hkeys) hle

/-- **Every run the game has is charged at least `2 ^ subtreeHeight`.** -/
theorem pow_le_count_of_mem_support (adversary : Adversary) {outcome : Outcome × Nat}
    (hmem : outcome ∈ support (runAll adversary)) : 2 ^ subtreeHeight ≤ outcome.2 := by
  have hinstrumented : outcome ∈
      support (Prod.fst <$> WholeGameStructural.instrumentedRun adversary) := by
    rw [support_map]
    unfold runAll Xmss.RandomOracleModel.run at hmem
    rw [StateT.run'_eq, support_map] at hmem
    exact hmem
  rw [← Averaging.support_eq_of_evalDist_eq (evalDist_outcome adversary), warmedRun_eq,
    support_map, support_map] at hinstrumented
  obtain ⟨pair, hpair, hvalue⟩ := hinstrumented
  obtain ⟨joined, hjoined, rfl⟩ := hpair
  obtain ⟨walk, hwalk, hrest⟩ := support_bind_exists hjoined
  obtain ⟨result, hresult, hpure⟩ := support_bind_exists hrest
  rw [support_pure, Set.mem_singleton_iff] at hpure
  subst hpure
  rw [← hvalue]
  exact pow_le_count_tail adversary hwalk hresult

/-- **A budget is at least what key generation spends.** This is what makes the accounting's
`q - 2 ^ subtreeHeight` the number of hash calls the adversary has left rather than a
truncation. -/
theorem pow_le_of_budget (q : Nat) (adversary : Adversary) (hbudget : HasTotalBudget adversary q) :
    2 ^ subtreeHeight ≤ q := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  refine one_ne_zero (α := ℝ≥0∞) (hbudget.symm.trans (probEvent_eq_zero ?_))
  rintro outcome hmem ⟨-, hcount⟩
  exact absurd (le_trans (pow_le_count_of_mem_support adversary hmem) hcount) (Nat.not_le.mpr hlt)

end SlhDsaSecurity.KeygenBudget
