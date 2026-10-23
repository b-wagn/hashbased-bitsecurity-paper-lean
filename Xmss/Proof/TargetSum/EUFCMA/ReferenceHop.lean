import Xmss.Proof.TargetSum.EUFCMA.Memoization
import Xmss.Proof.TargetSum.EUFCMA.DirectBridge
import Xmss.Proof.Generic.Deterministic.ReferenceDistribution
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability
/-! The full standard-forgery hop from the seeded scheme to the existing randomized
reference execution, with at most D / 2^256 loss for D direct hash queries. -/

open OracleComp OracleSpec ENNReal

open Xmss.Generic

namespace Xmss.TargetSum.EUFCMA.Seeded
open Xmss.EUFCMA

open Xmss.Generic.Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {State : Type}

attribute [local irreducible] Seeded.tableSign

noncomputable def gameAfterSecrets (adversary : Adversary) (parameter : PublicParameter)
    (secret : Seeded.ChainSecrets) : OracleComp OracleWorld Bool := do
  let result ← liftM
    (Generic.Merkle.treeNode parameter secret treeHeight Generic.Merkle.rootNode : OracleComp HashSpec Digest).withQueryLog
  let sk := Generic.Keygen.precomputedSecretKey parameter secret (Generic.hashCacheOfLog result.2)
  EUFCMA.gameRest precomputedScheme adversary ⟨result.1, parameter⟩ sk

theorem gameCore_independent_eq (adversary : Adversary) :
    EUFCMA.gameCore precomputedScheme adversary = (do
      let parameter ← liftM Keygen.samplePublicParameter
      let secret ← liftM Keygen.sampleSecret
      gameAfterSecrets adversary parameter secret) := by
  simp only [EUFCMA.gameCore, precomputedScheme, Keygen.precomputedKeygen, gameAfterSecrets,
    EUFCMA.gameRest, bind_assoc, pure_bind]

theorem runWorldSigning_sourceGame (secretKey : Generic.SecretKey)
    (publicKey : PublicKey) (adversary : Adversary) :
    Seeded.runWorldSigning (fun (request : SignRequest) => Signing.precomputedCappedSign secretKey request.epoch request.message) (sourceGame publicKey adversary) =
      EUFCMA.gameRest precomputedScheme adversary publicKey secretKey := by
  unfold sourceGame
  rw [Seeded.runWorldSigning, simulateQ_bind]
  change (Seeded.runWorldSigning (fun (request : SignRequest) => Signing.precomputedCappedSign secretKey request.epoch request.message) (DeterministicSigning.withRequestLog (adversary.main publicKey)) >>=
    fun result => Seeded.runWorldSigning (fun (request : SignRequest) => Signing.precomputedCappedSign secretKey request.epoch request.message) (DeterministicSigning.baseLift (finishGame publicKey result))) = _
  rw [Seeded.runWorldSigning_withRequestLog]
  have hlift (result) : Seeded.runWorldSigning (fun (request : SignRequest) => Signing.precomputedCappedSign secretKey request.epoch request.message) (DeterministicSigning.baseLift (finishGame publicKey result)) =
      finishGame publicKey result := by
    rw [Seeded.runWorldSigning, DeterministicSigning.simulateQ_baseLift, simulateQ_ofLift_eq_self]
  simp_rw [hlift]
  unfold Seeded.loggedRun EUFCMA.gameRest finishGame transcriptWin
  rfl

theorem evalDist_tableGameAfterSecrets_memo (hash : QueryImpl HashSpec (StateT State ProbComp))
    (adversary : Adversary) (parameter : PublicParameter) (outputs : Seeded.ChainSecrets) (state : State) :
    𝒟[do
      let randomizers ← Seeded.sampleRandomizerOutputs
      (simulateQ (Seeded.worldHandler hash) (tableGameAfterSecrets (Seeded.memoAdversary adversary) parameter outputs randomizers)).run state] =
      𝒟[(simulateQ (Seeded.worldHandler hash) (gameAfterSecrets (Seeded.memoAdversary adversary)
        parameter outputs)).run state] := by
  unfold tableGameAfterSecrets gameAfterSecrets
  simp only [simulateQ_bind, StateT.run_bind]
  rw [evalDist_bind_bind_swap]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro result
  have hleft (randomizers) := runSigning_sourceGame randomizers (Generic.Keygen.precomputedSecretKey parameter outputs (Generic.hashCacheOfLog result.1.2))
    ⟨result.1.1, parameter⟩ (Seeded.memoAdversary adversary)
  simp_rw [← hleft]
  rw [← runWorldSigning_sourceGame, Seeded.simulateQ_runWorldSigning]
  exact Seeded.evalDist_tableRequests hash (Generic.Keygen.precomputedSecretKey parameter outputs (Generic.hashCacheOfLog result.1.2))
    (sourceGame ⟨result.1.1, parameter⟩ (Seeded.memoAdversary adversary))
    (freshRequests_sourceGame_memo _ _) result.2

theorem evalDist_referenceOutputs (adversary : Adversary) :
    𝒟[do
      let parameterOutput ← ($ᵗ Digest : ProbComp Digest)
      let outputs ← ($ᵗ Seeded.ChainSecrets)
      (simulateQ romImpl (gameAfterSecrets adversary (parameterOutput)
        (outputs))).run' ∅] =
      𝒟[(simulateQ romImpl (EUFCMA.gameCore precomputedScheme adversary)).run' ∅] := by
  rw [gameCore_independent_eq, Seeded.run'_lift_sample_bind]
  trans 𝒟[do
    let parameter ← Keygen.samplePublicParameter
    let outputs ← ($ᵗ Seeded.ChainSecrets)
    (simulateQ romImpl (gameAfterSecrets adversary parameter (outputs))).run' ∅]
  · exact Seeded.evalDist_parameter_continuation fun parameter => do
      let outputs ← ($ᵗ Seeded.ChainSecrets)
      (simulateQ romImpl (gameAfterSecrets adversary parameter (outputs))).run' ∅
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  rw [Seeded.run'_lift_sample_bind]
  exact Seeded.evalDist_secrets_continuation fun secret =>
    (simulateQ romImpl (gameAfterSecrets adversary parameter secret)).run' ∅

theorem evalDist_independentTableGame_memo (adversary : Adversary) :
    𝒟[independentTableGame (Seeded.memoAdversary adversary)] =
      𝒟[(simulateQ romImpl (EUFCMA.gameCore precomputedScheme (Seeded.memoAdversary adversary))).run' ∅] := by
  rw [← evalDist_referenceOutputs]
  unfold independentTableGame Seeded.drawSigningMaterial
  simp only [bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameterOutput
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro outputs
  have h := evalDist_tableGameAfterSecrets_memo randomOracle adversary (parameterOutput) (outputs) ∅
  rw [Seeded.worldHandler_randomOracle] at h
  have heq := congrArg (fun distribution => Prod.fst <$> distribution) h
  simpa only [StateT.run'_eq, evalDist_map, evalDist_bind, map_bind] using heq

theorem forgeAdvantage_deterministic_le_reference_direct (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    EUFCMA.forgeAdvantage Seeded.scheme adversary ≤
      EUFCMA.forgeAdvantage precomputedScheme (Seeded.memoAdversary adversary) +
        D / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  have hmemo := prob_independentTableGame_le_memo adversary
  rw [probOutput_congr rfl (evalDist_independentTableGame_memo adversary)] at hmemo
  exact (forgeAdvantage_deterministic_le_table_direct adversary D hD).trans (add_le_add hmemo le_rfl)

/-- info: 'Xmss.TargetSum.EUFCMA.Seeded.forgeAdvantage_deterministic_le_reference_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forgeAdvantage_deterministic_le_reference_direct

end Xmss.TargetSum.EUFCMA.Seeded

namespace Xmss.TargetSum.EUFCMA
open Xmss.EUFCMA

/-- A reference bound including the seed-guessing loss closes the direct statement. -/
theorem direct_security_of_reference_bound (bits : ℕ)
    (h : ∀ (adversary : Adversary) (D : ℕ), 1 ≤ D →
      Direct.IsDirectQueryBound adversary D →
      forgeAdvantage precomputedScheme adversary + D / ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤
        D / ((2 ^ bits : ℕ) : ℝ≥0∞)) :
    (notion Unforgeability.CountingMode.direct).HasClassicalSecurityBits Generic.xmss bits := by
  apply direct_security_of_isDirectQueryBound
  intro adversary D hD hbound
  exact (Seeded.forgeAdvantage_deterministic_le_reference_direct adversary D hbound).trans
    (h (Seeded.memoAdversary adversary) D hD
      (Seeded.memoAdversary_isDirectQueryBound adversary D hbound))

/-- info: 'Xmss.TargetSum.EUFCMA.direct_security_of_reference_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms direct_security_of_reference_bound

end Xmss.TargetSum.EUFCMA
