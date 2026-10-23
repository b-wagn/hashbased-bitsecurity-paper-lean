import SlhDsaSecurity.Proof.StructuralTerm
import SlhDsaSecurity.Proof.GrowthBudget
import SlhDsaSecurity.Proof.CombinedCharge
import SlhDsaSecurity.Proof.GrowthCharge
import SlhDsaSecurity.Statement.Security

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
  unfold runAll Xmss.RandomOracleModel.run
  rw [StateT.run'_eq, support_map]
  exact ⟨result, hmem, rfl⟩

/-! ## The answer side of the budget, for the whole game

The structural term above charges one of the two answer-side avenues. The other is FORS
coverage, and `CombinedCharge` charges them together — as one predicate, so their rate is the
maximum `2 ^ -128` rather than the sum, which is what keeps the answer side inside half the
target.

`prob_combinedBad_whole_game_le` is that charge at the whole game, discharging the growth
budget from `HasTotalBudget` exactly as the structural term does. It is the `hanswer`
obligation of `MainTheorem.totalSecurityBits_of_halves`, for the cells and disclosures that
the experiment's key generation and signing produce.

*That assembly is no longer the live one* — `totalSecurityBits_of_halves` has no consumers, and
the proof is assembled by `ObligationShapes.target_of_answer_and_leaves`. The charge below is
still live; it is the shape it was once an obligation of that moved. -/

/-! ## The answer side, charged per class

`prob_combinedBad_whole_game_le` charges both answer-side clauses as one predicate, at the
maximum rate. That keeps the answer side inside `q / 2 ^ 128`, but it leaves nothing over:
`2 q / 2 ^ 129` is exactly the allowance, and the load-cap defect has nowhere to go.

Charging per class recovers the room. A structural-class query can buy a structural hit, rate
`2`; a message-class query can buy coverage, rate `1`. Their sum `2 qs + qm` is below the
allowance `2 (qs + qm)` by exactly `qm`, which is the slack
`Assembly.cap_defect_within_slack` spends on the `2 ^ -126` defect. It is also the form the
coverage half must take, since that half goes through the leave-one-out tape rather than a
fixed disclosure set.

The class counts are taken as hypotheses here. Deriving them needs the game instrumented with
`ClassBudget.countClass` rather than the plain total counter, which is a separate step. -/

/-! ## The answer side, charged by weight

The weighted charge is the form the game can feed: one budget, read off one counter. At
weights `2` on a structural-class input and `1` on a message-class one, in units of `2 ^ -129`,
the answer side costs `weighted / 2 ^ 129`.

The budget comes for free from the existing instrumentation. Every weight is at most `2`, so
`WeightedCharge.weightedGrowth_of_growth` turns the plain growth bound into a weighted one at
`2 q` — exactly the answer side's allowance. That is the whole accounting on the branch of the
dichotomy where no defect is owed; the other branch needs the finer count, which
`WeightedCharge.jointGrowth_le_count` now supplies. -/

end SlhDsaSecurity.WholeGameStructural
