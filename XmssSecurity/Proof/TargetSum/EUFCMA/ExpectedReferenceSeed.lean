import XmssSecurity.Proof.TargetSum.EUFCMA.ExpectedSeedHop
import XmssSecurity.Proof.TargetSum.Deterministic.SelectedCostState
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Carry the standard seed-domain loss into the reference execution with the
same selected-query counter used for the other query classes. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA.Seeded
open XmssSecurity.EUFCMA

open XmssSecurity.Generic.Seeded XmssSecurity.TargetSum.Seeded

attribute [local irreducible] gameAfterSecrets

theorem evalDist_referenceOutputs_withState {State : Type}
    (hash : QueryImpl HashSpec (StateT State ProbComp)) (adversary : Adversary) (state : State) :
    𝒟[do
      let parameterOutput ← ($ᵗ HashOutput : ProbComp HashOutput)
      let outputs ← ($ᵗ Seeded.ChainOutputs)
      (simulateQ (Seeded.worldHandler hash) (gameAfterSecrets adversary (Generic.truncateHash parameterOutput)
        (Seeded.outputSecrets outputs))).run state] =
      𝒟[(simulateQ (Seeded.worldHandler hash) (gameCore Concrete.scheme adversary)).run state] := by
  rw [gameCore_independent_eq, Seeded.worldHandler_sampling_bind]
  trans 𝒟[do
    let parameter ← Concrete.samplePublicParameter
    let outputs ← ($ᵗ Seeded.ChainOutputs)
    (simulateQ (Seeded.worldHandler hash) (gameAfterSecrets adversary parameter (Seeded.outputSecrets outputs))).run state]
  · exact Seeded.evalDist_parameter_continuation fun parameter => do
      let outputs ← ($ᵗ Seeded.ChainOutputs)
      (simulateQ (Seeded.worldHandler hash) (gameAfterSecrets adversary parameter (Seeded.outputSecrets outputs))).run state
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  rw [Seeded.worldHandler_sampling_bind]
  exact Seeded.evalDist_secrets_continuation fun secret =>
    (simulateQ (Seeded.worldHandler hash) (gameAfterSecrets adversary parameter secret)).run state

theorem evalDist_independentTableRun_memo {State : Type}
    (hash : QueryImpl HashSpec (StateT State ProbComp)) (adversary : Adversary) (state : State) :
    𝒟[do
      let material ← Seeded.drawSigningMaterial
      (simulateQ (Seeded.worldHandler hash) (tableGameAfterSecrets (Seeded.memoAdversary adversary)
        (Generic.truncateHash material.1) (Seeded.outputSecrets material.2.1) material.2.2)).run state] =
      𝒟[(simulateQ (Seeded.worldHandler hash) (gameCore Concrete.scheme (Seeded.memoAdversary adversary))).run state] := by
  rw [← evalDist_referenceOutputs_withState hash]
  unfold Seeded.drawSigningMaterial
  simp only [bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameterOutput
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro outputs
  exact evalDist_tableGameAfterSecrets_memo hash adversary (Generic.truncateHash parameterOutput) (Seeded.outputSecrets outputs) state

theorem expectedTableSeedQueries_memo_eq_reference (adversary : Adversary) :
    expectedTableSeedQueries (Seeded.memoAdversary adversary) =
      expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit)
        (gameCore Concrete.scheme (Seeded.memoAdversary adversary)) ∅ := by
  unfold expectedTableSeedQueries
  simp_rw [expectedQueries_eq_selectedCostWorld]
  rw [← tsum_probOutput_bind_mul]
  apply tsum_congr
  intro result
  rw [probOutput_congr rfl (evalDist_independentTableRun_memo (selectedCostHash MaySeedHit) adversary (∅, 0))]

theorem forgeAdvantage_seeded_le_memo (adversary : Adversary) :
    forgeAdvantage Seeded.scheme adversary ≤ forgeAdvantage Seeded.scheme (Seeded.memoAdversary adversary) := by
  unfold forgeAdvantage
  rw [probOutput_congr rfl (evalDist_gameCore_deterministic_programmed adversary),
    probOutput_congr rfl (evalDist_gameCore_deterministic_programmed (Seeded.memoAdversary adversary))]
  unfold programmedDeterministicGame
  apply probOutput_bind_mono
  intro seed _
  apply probOutput_bind_mono
  intro parameterOutput _
  apply probOutput_bind_mono
  intro outputs _
  apply probOutput_bind_mono
  intro randomizers _
  exact prob_tableGameAfterSecrets_le_memo adversary (Generic.truncateHash parameterOutput) (Seeded.outputSecrets outputs)
    randomizers (Seeded.signingDerivationCache seed parameterOutput outputs randomizers)

theorem forgeAdvantage_deterministic_le_reference_expectedReferenceSeed (adversary : Adversary) :
    forgeAdvantage Seeded.scheme adversary ≤ forgeAdvantage Concrete.scheme (Seeded.memoAdversary adversary) +
      expectedSimulatedQueryCount romImpl (Seeded.hashBad MaySeedHit)
        (gameCore Concrete.scheme (Seeded.memoAdversary adversary)) ∅ / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  calc
    _ ≤ forgeAdvantage Seeded.scheme (Seeded.memoAdversary adversary) := forgeAdvantage_seeded_le_memo adversary
    _ ≤ Pr[= true | independentTableGame (Seeded.memoAdversary adversary)] +
        expectedTableSeedQueries (Seeded.memoAdversary adversary) / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
      forgeAdvantage_deterministic_le_table_expectedSeed (Seeded.memoAdversary adversary)
    _ = _ := by
      rw [expectedTableSeedQueries_memo_eq_reference,
        probOutput_congr rfl (evalDist_independentTableGame_memo adversary)]
      rfl

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Seeded.forgeAdvantage_deterministic_le_reference_expectedReferenceSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forgeAdvantage_deterministic_le_reference_expectedReferenceSeed

end XmssSecurity.TargetSum.EUFCMA.Seeded
