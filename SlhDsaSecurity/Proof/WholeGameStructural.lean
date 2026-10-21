import SlhDsaSecurity.Proof.StructuralTerm
import SlhDsaSecurity.Proof.GrowthBudget
import SlhDsaSecurity.Proof.CombinedCharge

/-!
# The structural term for the whole game

Under the all-queries-counted accounting the structural charge applies to the entire
experiment at once, with no side conditions on the honest phase. Three facts combine:

* the game starts from the empty cache, which is vacuously a cache of honest canonical
  queries, so `StructuralTerm.prob_deviatingCollision_le` applies with no hypothesis;
* `GrowthBudget.growth_le_count` bounds the cache growth of any supported run by that
  run's own total hash count;
* `Security.HasTotalBudget` bounds that count by `q` with probability one.

The result, `prob_deviatingCollision_whole_game_le`, is the structural term: in the whole
game, the probability that any deviating structural collision occurs — the shape of every
witness `Extraction.*` yields from an accepted forgery — is at most `q / 2 ^ 128`.

This is where charging the honest work pays off. Key generation and signing are now
charged, so their cache growth is covered by the same budget and needs no separate
treatment; under verifier-counted accounting the honest phase had to be analysed apart and
its canonical queries identified one by one.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.WholeGameStructural

open Security CanonicalGraph

/-- The instrumented run, before the count is projected away. -/
noncomputable def instrumentedRun (adversary : Adversary) :
    ProbComp ((Outcome × Nat) × QueryCache HashSpec) :=
  (simulateQ KeygenUniform.rom (countAllHashes (experiment adversary))).run ∅

theorem mem_support_runAll_of_mem_support {adversary : Adversary}
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hmem : result ∈ support (instrumentedRun adversary)) :
    result.1 ∈ support (runAll adversary) := by
  unfold runAll XmssSecurity.RandomOracleModel.run
  rw [StateT.run'_eq, support_map]
  exact ⟨result, hmem, rfl⟩

/-- The budget bounds the total hash count on every supported run. -/
theorem count_le_of_budget {adversary : Adversary} {q : Nat}
    (hbudget : HasTotalBudget adversary q)
    {result : (Outcome × Nat) × QueryCache HashSpec}
    (hmem : result ∈ support (instrumentedRun adversary)) : result.1.2 ≤ q :=
  ((probEvent_eq_one_iff.mp hbudget).2 result.1
    (mem_support_runAll_of_mem_support hmem)).2

/-- **The structural term for the whole game.** With every hash call charged, the
probability that the game produces any deviating structural collision is at most
`q / 2 ^ 128`. -/
theorem prob_deviatingCollision_whole_game_le (adversary : Adversary) (q : Nat)
    (publicSeed : Digest) (cells : Cells) (hbudget : HasTotalBudget adversary q) :
    Pr[fun result : (Outcome × Nat) × QueryCache HashSpec =>
        StructuralTerm.DeviatingCollision publicSeed cells result |
      instrumentedRun adversary] ≤ q / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_trans (probEvent_mono ?_)
    (StructuralTerm.prob_deviatingCollision_le (countAllHashes (experiment adversary))
      publicSeed cells q ∅ (by intro input hinput; exact absurd (by simp) hinput))
  intro result hmem hcollision
  refine ⟨hcollision, ?_⟩
  exact GrowthBudget.GrowthAtMost.mono
    (GrowthBudget.growth_le_count (experiment adversary) ∅ result hmem)
    (count_le_of_budget hbudget hmem)

/-! ## The answer side of the budget, for the whole game

The structural term above charges one of the two answer-side avenues. The other is FORS
coverage, and `CombinedCharge` charges them together — as one predicate, so their rate is the
maximum `2 ^ -128` rather than the sum, which is what keeps the answer side inside half the
target.

`prob_combinedBad_whole_game_le` is that charge at the whole game, discharging the growth
budget from `HasTotalBudget` exactly as the structural term does. It is the `hanswer`
obligation of `MainTheorem.totalSecurityBits_of_halves`, for the cells and disclosures that
the experiment's key generation and signing produce. -/

/-- **The answer side for the whole game.** -/
theorem prob_combinedBad_whole_game_le (adversary : Adversary) (q : Nat)
    (publicSeed : Digest) (pk : PublicKey) (cells : Cells)
    (revealed : ForsCoverage.Disclosures) (loads : ForsCoverage.Instance → Nat)
    (hload : ∀ index tree, (revealed index tree).card ≤ loads index)
    (hmoment : ∑ index, loads index ^ 14 ≤ 2 ^ 102)
    (hseparated : ∀ input, CombinedCharge.IsMessageInput pk input →
      CanonicalTarget.canonicalTarget publicSeed cells input = none)
    (hbudget : HasTotalBudget adversary q) :
    Pr[fun result : (Outcome × Nat) × QueryCache HashSpec =>
        GrowthCharge.Bad (CombinedCharge.CombinedBad publicSeed pk cells revealed) result |
      instrumentedRun adversary] ≤ q / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  refine le_trans (probEvent_mono ?_)
    (CombinedCharge.prob_combinedBad_within_le (countAllHashes (experiment adversary))
      publicSeed pk cells revealed loads hload hmoment hseparated q ∅
      (by intro input output hentry; exact absurd hentry (by simp)))
  intro result hmem hbad
  exact ⟨hbad, GrowthBudget.GrowthAtMost.mono
    (GrowthBudget.growth_le_count (experiment adversary) ∅ result hmem)
    (count_le_of_budget hbudget hmem)⟩

end SlhDsaSecurity.WholeGameStructural
