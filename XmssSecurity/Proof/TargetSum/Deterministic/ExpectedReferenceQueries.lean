import XmssSecurity.Proof.TargetSum.Deterministic.SelectedCostState
import XmssSecurity.Proof.TargetSum.Direct.SeedGuessingExpected

/-! Selected hash-query counts pass through the memoized table-to-reference game hop.
The seed loss can consequently be measured in the same reference game as the other losses. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Seeded

attribute [local irreducible] gameAfterSecrets

theorem evalDist_referenceOutputs_withState {State : Type}
    (hash : QueryImpl HashSpec (StateT State ProbComp)) (adversary : Adversary) (state : State) :
    𝒟[do
      let parameterOutput ← ($ᵗ HashOutput : ProbComp HashOutput)
      let outputs ← ($ᵗ ChainOutputs)
      (simulateQ (worldHandler hash) (gameAfterSecrets adversary (truncateHash parameterOutput)
        (outputSecrets outputs))).run state] =
      𝒟[(simulateQ (worldHandler hash) (gameCore Concrete.scheme adversary)).run state] := by
  rw [gameCore_independent_eq, worldHandler_sampling_bind]
  trans 𝒟[do
    let parameter ← Concrete.samplePublicParameter
    let outputs ← ($ᵗ ChainOutputs)
    (simulateQ (worldHandler hash) (gameAfterSecrets adversary parameter (outputSecrets outputs))).run state]
  · exact evalDist_parameter_continuation fun parameter => do
      let outputs ← ($ᵗ ChainOutputs)
      (simulateQ (worldHandler hash) (gameAfterSecrets adversary parameter (outputSecrets outputs))).run state
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  rw [worldHandler_sampling_bind]
  exact evalDist_secrets_continuation fun secret =>
    (simulateQ (worldHandler hash) (gameAfterSecrets adversary parameter secret)).run state

theorem evalDist_independentTableRun_memo {State : Type}
    (hash : QueryImpl HashSpec (StateT State ProbComp)) (adversary : Adversary) (state : State) :
    𝒟[do
      let material ← drawSigningMaterial
      (simulateQ (worldHandler hash) (tableGameAfterSecrets (memoAdversary adversary)
        (truncateHash material.1) (outputSecrets material.2.1) material.2.2)).run state] =
      𝒟[(simulateQ (worldHandler hash) (gameCore Concrete.scheme (memoAdversary adversary))).run state] := by
  rw [← evalDist_referenceOutputs_withState hash]
  unfold drawSigningMaterial
  simp only [bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameterOutput
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro outputs
  exact evalDist_tableGameAfterSecrets_memo hash adversary (truncateHash parameterOutput) (outputSecrets outputs) state

theorem expectedTableSeedQueries_memo_eq_reference (adversary : Adversary) :
    expectedTableSeedQueries (memoAdversary adversary) =
      expectedSimulatedQueryCount romImpl (hashBad MaySeedHit)
        (gameCore Concrete.scheme (memoAdversary adversary)) ∅ := by
  unfold expectedTableSeedQueries
  simp_rw [expectedQueries_eq_selectedCostWorld]
  rw [← tsum_probOutput_bind_mul]
  apply tsum_congr
  intro result
  rw [probOutput_congr rfl (evalDist_independentTableRun_memo (selectedCostHash MaySeedHit) adversary (∅, 0))]

theorem forgeAdvantage_seeded_le_memo (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤ forgeAdvantage scheme (memoAdversary adversary) := by
  unfold forgeAdvantage
  rw [probOutput_congr rfl (evalDist_gameCore_deterministic_programmed adversary),
    probOutput_congr rfl (evalDist_gameCore_deterministic_programmed (memoAdversary adversary))]
  unfold programmedDeterministicGame
  apply probOutput_bind_mono
  intro seed _
  apply probOutput_bind_mono
  intro parameterOutput _
  apply probOutput_bind_mono
  intro outputs _
  apply probOutput_bind_mono
  intro randomizers _
  exact prob_tableGameAfterSecrets_le_memo adversary (truncateHash parameterOutput) (outputSecrets outputs)
    randomizers (signingDerivationCache seed parameterOutput outputs randomizers)

theorem forgeAdvantage_deterministic_le_reference_expectedReferenceSeed (adversary : Adversary) :
    forgeAdvantage scheme adversary ≤ forgeAdvantage Concrete.scheme (memoAdversary adversary) +
      expectedSimulatedQueryCount romImpl (hashBad MaySeedHit)
        (gameCore Concrete.scheme (memoAdversary adversary)) ∅ / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  calc
    _ ≤ forgeAdvantage scheme (memoAdversary adversary) := forgeAdvantage_seeded_le_memo adversary
    _ ≤ Pr[= true | independentTableGame (memoAdversary adversary)] +
        expectedTableSeedQueries (memoAdversary adversary) / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
      forgeAdvantage_deterministic_le_table_expectedSeed (memoAdversary adversary)
    _ = _ := by
      rw [expectedTableSeedQueries_memo_eq_reference,
        probOutput_congr rfl (evalDist_independentTableGame_memo adversary)]
      rfl

/-- info: 'XmssSecurity.TargetSum.Seeded.forgeAdvantage_deterministic_le_reference_expectedReferenceSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forgeAdvantage_deterministic_le_reference_expectedReferenceSeed

end XmssSecurity.TargetSum.Seeded
