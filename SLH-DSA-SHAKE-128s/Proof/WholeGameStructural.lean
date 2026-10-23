import «SLH-DSA-SHAKE-128s».Proof.StructuralTerm
import «SLH-DSA-SHAKE-128s».Proof.GrowthBudget
import «SLH-DSA-SHAKE-128s».Proof.CombinedCharge
import «SLH-DSA-SHAKE-128s».Proof.GrowthCharge
import «SLH-DSA-SHAKE-128s».Statement.Security

/-!
# The whole game, instrumented

`instrumentedRun` runs the experiment under the all-queries counter `countAllHashes`, keeping the
cache and the count of every hash call, so a statement about the whole game's work reads off this
one run. `mem_support_runAll_of_mem_support` ties its support back to `runAll`.
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

end SlhDsaSecurity.WholeGameStructural
