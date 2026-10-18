import XmssSecurity.Proof.TargetSum.EUFCMA.ExpectedSeedHop
import XmssSecurity.Proof.TargetSum.Deterministic.SelectedCostState
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Carry the standard seed-domain loss into the reference execution with the
same selected-query counter used for the other query classes. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA.Seeded
open XmssSecurity.EUFCMA

open XmssSecurity.Generic.Seeded XmssSecurity.TargetSum.Seeded

attribute [local irreducible] gameAfterSecrets

theorem evalDist_referenceOutputs_withState {State : Type}
    (hash : QueryImpl HashSpec (StateT State ProbComp)) (adversary : Generic.Adversary) (state : State) :
    𝒟[do
      let parameterOutput ← ($ᵗ HashOutput : ProbComp HashOutput)
      let outputs ← ($ᵗ Generic.Seeded.ChainOutputs)
      (simulateQ (Generic.Seeded.worldHandler hash) (gameAfterSecrets adversary (Generic.truncateHash parameterOutput)
        (Generic.Seeded.outputSecrets outputs))).run state] =
      𝒟[(simulateQ (Generic.Seeded.worldHandler hash) (gameCore Generic.Concrete.scheme adversary)).run state] := by
  rw [gameCore_independent_eq, Generic.Seeded.worldHandler_sampling_bind]
  trans 𝒟[do
    let parameter ← Generic.Concrete.samplePublicParameter
    let outputs ← ($ᵗ Generic.Seeded.ChainOutputs)
    (simulateQ (Generic.Seeded.worldHandler hash) (gameAfterSecrets adversary parameter (Generic.Seeded.outputSecrets outputs))).run state]
  · exact Generic.Seeded.evalDist_parameter_continuation fun parameter => do
      let outputs ← ($ᵗ Generic.Seeded.ChainOutputs)
      (simulateQ (Generic.Seeded.worldHandler hash) (gameAfterSecrets adversary parameter (Generic.Seeded.outputSecrets outputs))).run state
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  rw [Generic.Seeded.worldHandler_sampling_bind]
  exact Generic.Seeded.evalDist_secrets_continuation fun secret =>
    (simulateQ (Generic.Seeded.worldHandler hash) (gameAfterSecrets adversary parameter secret)).run state

theorem evalDist_independentTableRun_memo {State : Type}
    (hash : QueryImpl HashSpec (StateT State ProbComp)) (adversary : Generic.Adversary) (state : State) :
    𝒟[do
      let material ← Generic.Seeded.drawSigningMaterial
      (simulateQ (Generic.Seeded.worldHandler hash) (tableGameAfterSecrets (Generic.Seeded.memoAdversary adversary)
        (Generic.truncateHash material.1) (Generic.Seeded.outputSecrets material.2.1) material.2.2)).run state] =
      𝒟[(simulateQ (Generic.Seeded.worldHandler hash) (gameCore Generic.Concrete.scheme (Generic.Seeded.memoAdversary adversary))).run state] := by
  rw [← evalDist_referenceOutputs_withState hash]
  unfold Generic.Seeded.drawSigningMaterial
  simp only [bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameterOutput
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro outputs
  exact evalDist_tableGameAfterSecrets_memo hash adversary (Generic.truncateHash parameterOutput) (Generic.Seeded.outputSecrets outputs) state

theorem expectedTableSeedQueries_memo_eq_reference (adversary : Generic.Adversary) :
    expectedTableSeedQueries (Generic.Seeded.memoAdversary adversary) =
      expectedSimulatedQueryCount Generic.romImpl (Generic.Seeded.hashBad Generic.MaySeedHit)
        (gameCore Generic.Concrete.scheme (Generic.Seeded.memoAdversary adversary)) ∅ := by
  unfold expectedTableSeedQueries
  simp_rw [expectedQueries_eq_selectedCostWorld]
  rw [← tsum_probOutput_bind_mul]
  apply tsum_congr
  intro result
  rw [probOutput_congr rfl (evalDist_independentTableRun_memo (selectedCostHash Generic.MaySeedHit) adversary (∅, 0))]

theorem forgeAdvantage_seeded_le_memo (adversary : Generic.Adversary) :
    forgeAdvantage Generic.Seeded.scheme adversary ≤ forgeAdvantage Generic.Seeded.scheme (Generic.Seeded.memoAdversary adversary) := by
  unfold forgeAdvantage
  rw [probOutput_congr rfl (evalDist_gameCore_deterministic_programmed adversary),
    probOutput_congr rfl (evalDist_gameCore_deterministic_programmed (Generic.Seeded.memoAdversary adversary))]
  unfold programmedDeterministicGame
  apply probOutput_bind_mono
  intro seed _
  apply probOutput_bind_mono
  intro parameterOutput _
  apply probOutput_bind_mono
  intro outputs _
  apply probOutput_bind_mono
  intro randomizers _
  exact prob_tableGameAfterSecrets_le_memo adversary (Generic.truncateHash parameterOutput) (Generic.Seeded.outputSecrets outputs)
    randomizers (Generic.Seeded.signingDerivationCache seed parameterOutput outputs randomizers)

theorem forgeAdvantage_deterministic_le_reference_expectedReferenceSeed (adversary : Generic.Adversary) :
    forgeAdvantage Generic.Seeded.scheme adversary ≤ forgeAdvantage Generic.Concrete.scheme (Generic.Seeded.memoAdversary adversary) +
      expectedSimulatedQueryCount Generic.romImpl (Generic.Seeded.hashBad Generic.MaySeedHit)
        (gameCore Generic.Concrete.scheme (Generic.Seeded.memoAdversary adversary)) ∅ / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  calc
    _ ≤ forgeAdvantage Generic.Seeded.scheme (Generic.Seeded.memoAdversary adversary) := forgeAdvantage_seeded_le_memo adversary
    _ ≤ Pr[= true | independentTableGame (Generic.Seeded.memoAdversary adversary)] +
        expectedTableSeedQueries (Generic.Seeded.memoAdversary adversary) / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
      forgeAdvantage_deterministic_le_table_expectedSeed (Generic.Seeded.memoAdversary adversary)
    _ = _ := by
      rw [expectedTableSeedQueries_memo_eq_reference,
        probOutput_congr rfl (evalDist_independentTableGame_memo adversary)]
      rfl

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Seeded.forgeAdvantage_deterministic_le_reference_expectedReferenceSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forgeAdvantage_deterministic_le_reference_expectedReferenceSeed

end XmssSecurity.TargetSum.EUFCMA.Seeded
