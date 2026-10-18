import XmssSecurity.Proof.Generic.Deterministic.TableToReference
import XmssSecurity.Proof.Generic.Seeded.HashTrace

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Generic.Seeded

variable [Code]

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

attribute [local irreducible] gameAfterSecrets

theorem evalDist_parameter_continuation {α : Type} (next : PublicParameter → ProbComp α) :
    𝒟[do let output ← ($ᵗ Digest : ProbComp Digest); next (output)] =
      𝒟[do let parameter ← Concrete.samplePublicParameter; next parameter] := by
  rw [evalDist_bind, evalDist_bind, evalDist_samplePublicParameter]

theorem evalDist_secrets_continuation {α : Type} (next : ChainSecrets → ProbComp α) :
    𝒟[do let outputs ← ($ᵗ ChainSecrets); next (outputs)] =
      𝒟[do let secret ← Concrete.sampleSecret; next secret] := by
  conv_rhs => rw [evalDist_bind, evalDist_sampleSecret, ← evalDist_bind]

theorem evalDist_referenceOutputs (adversary : Adversary) :
    𝒟[do
      let parameterOutput ← ($ᵗ Digest : ProbComp Digest)
      let outputs ← ($ᵗ ChainSecrets)
      (simulateQ romImpl (gameAfterSecrets adversary (parameterOutput)
        (outputs))).run' ∅] =
      𝒟[(simulateQ romImpl (gameCore Concrete.scheme adversary)).run' ∅] := by
  rw [gameCore_independent_eq, run'_lift_sample_bind]
  trans 𝒟[do
    let parameter ← Concrete.samplePublicParameter
    let outputs ← ($ᵗ ChainSecrets)
    (simulateQ romImpl (gameAfterSecrets adversary parameter (outputs))).run' ∅]
  · exact evalDist_parameter_continuation fun parameter => do
      let outputs ← ($ᵗ ChainSecrets)
      (simulateQ romImpl (gameAfterSecrets adversary parameter (outputs))).run' ∅
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  rw [run'_lift_sample_bind]
  exact evalDist_secrets_continuation fun secret =>
    (simulateQ romImpl (gameAfterSecrets adversary parameter secret)).run' ∅

theorem worldHandler_randomOracle : worldHandler randomOracle = romImpl := rfl

theorem evalDist_independentTableGame_memo (adversary : Adversary) :
    𝒟[independentTableGame (memoAdversary adversary)] =
      𝒟[(simulateQ romImpl (gameCore Concrete.scheme (memoAdversary adversary))).run' ∅] := by
  rw [← evalDist_referenceOutputs]
  unfold independentTableGame drawSigningMaterial
  simp only [bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameterOutput
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro outputs
  have h := evalDist_tableGameAfterSecrets_memo randomOracle adversary (parameterOutput) (outputs) ∅
  rw [worldHandler_randomOracle] at h
  have heq := congrArg (fun distribution => Prod.fst <$> distribution) h
  simpa only [StateT.run'_eq, evalDist_map, evalDist_bind, map_bind] using heq

end XmssSecurity.Generic.Seeded
