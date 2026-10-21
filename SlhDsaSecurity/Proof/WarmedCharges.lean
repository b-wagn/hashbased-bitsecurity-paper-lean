import SlhDsaSecurity.Proof.WarmedGame
import SlhDsaSecurity.Proof.StructuralTerm
import SlhDsaSecurity.Proof.GrowthBudget

/-!
# The charges, at the walk's own cells

With the game split into `WarmedGame.graphWalk` and `WarmedGame.tail`, each charge now applies
to the tail with the cells the walk produced — which is the whole point of walking first. Two
facts are needed to invoke one, and both are about the walk rather than the charge:

* the tail starts from the walk's cache, which carries the canonical entries of those cells
  and nothing else (`CanonicalGraph.Programming.cacheFrom_empty_canonical`), so the
  cleanliness hypothesis every charge takes is discharged;
* the tail's cache growth is bounded by its own charged count, and that count is bounded by
  `q` — which has to be *imported* from the unwarmed game, since `Security.HasTotalBudget`
  speaks about `Security.runAll`. `count_le_of_budget_tail` is that import, and it goes
  through `WarmedGame.evalDist_outcome`: the outcome's law is unchanged by warming, so a
  property holding almost surely there holds on every supported tail here.

`prob_deviatingCollision_tail_le` is the first charge in this form. It is the structural
half of the answer side, now stated against *this run's* honest key rather than an arbitrary
fixed one.
-/

open OracleComp OracleSpec ENNReal

set_option linter.constructorNameAsVariable false
namespace SlhDsaSecurity.WarmedCharges

open Security CanonicalGraph WarmedGame

/-! `afterSeeds` is the whole game after key generation's seeds are drawn, and unfolding it is
never useful here — every statement below treats it as an opaque computation. Left reducible it
is worse than useless: a defeq check as trivial as matching a hypothesis against a syntactically
identical goal unfolds it and does not terminate. -/

attribute [local irreducible] WarmedGame.afterSeeds

/-- A tail result belongs to the warmed run. -/
theorem mem_support_warmedRun {adversary : Adversary}
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (tail adversary walk)) :
    ((walk.1, result.1), result.2) ∈ support (warmedRun adversary) := by
  rw [warmedRun_eq, support_map]
  exact ⟨(walk, result), by
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop]
    exact ⟨walk, hwalk, result, hresult, rfl⟩, rfl⟩

/-- **The budget bounds the tail's count.** -/
theorem count_le_of_budget_tail {adversary : Adversary} {q : Nat}
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hresult : result ∈ support (tail adversary walk)) : result.1.2 ≤ q := by
  have houtcome : result.1 ∈ support ((fun pair => pair.1.2) <$> warmedRun adversary) := by
    rw [support_map]
    exact ⟨_, mem_support_warmedRun hwalk hresult, rfl⟩
  rw [Averaging.support_eq_of_evalDist_eq (evalDist_outcome adversary), support_map] at houtcome
  obtain ⟨inner, hinner, houter⟩ := houtcome
  rw [← houter]
  exact WholeGameStructural.count_le_of_budget hbudget hinner

/-- The walk's cache carries canonical entries and nothing else. -/
theorem walk_cache_canonical
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) (input : Bytes) (hinput : walk.2 input ≠ none) :
    ∃ parent : StructuralNode,
      input = canonicalInput walk.1.1.2.2 walk.1.2 parent := by
  obtain ⟨outputs, -, hcache⟩ := mem_support_graphWalk hwalk
  rw [hcache] at hinput
  exact Programming.cacheFrom_empty_canonical _ _ outputs _ input hinput

/-- **The structural term, at this run's honest key.** -/
theorem prob_deviatingCollision_tail_le (adversary : Adversary) (q : Nat)
    (hbudget : HasTotalBudget adversary q)
    {walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec}
    (hwalk : walk ∈ support graphWalk) :
    Pr[fun result : (Outcome × Nat) × QueryCache HashSpec =>
        StructuralTerm.DeviatingCollision walk.1.1.2.2 walk.1.2 result |
      tail adversary walk] ≤ q / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  rw [tail]
  refine le_trans (probEvent_mono ?_)
    (StructuralTerm.prob_deviatingCollision_le
      (countAllHashes (afterSeeds adversary walk.1.1)) walk.1.1.2.2 walk.1.2 q walk.2
      (walk_cache_canonical hwalk))
  intro result hresult hcollision
  have hres : result ∈ support (tail adversary walk) := by rw [tail]; exact hresult
  refine ⟨hcollision, ?_⟩
  exact GrowthBudget.GrowthAtMost.mono
    (GrowthBudget.growth_le_count (afterSeeds adversary walk.1.1) walk.2 result hresult)
    (count_le_of_budget_tail hbudget hwalk hres)

end SlhDsaSecurity.WarmedCharges
