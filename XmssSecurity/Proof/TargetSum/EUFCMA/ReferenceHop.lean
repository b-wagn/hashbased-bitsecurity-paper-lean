import XmssSecurity.Proof.TargetSum.EUFCMA.Memoization
import XmssSecurity.Proof.TargetSum.EUFCMA.DirectBridge
import XmssSecurity.Proof.Generic.Deterministic.ReferenceDistribution
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! The full standard-forgery hop from the seeded scheme to the existing randomized
reference execution, with at most D / 2^256 loss for D direct hash queries. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.EUFCMA.Seeded
open XmssSecurity.EUFCMA

open XmssSecurity.Generic.Seeded Generic.DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {State : Type}

attribute [local irreducible] Generic.Seeded.tableSign

noncomputable def gameAfterSecrets (adversary : Generic.Adversary) (parameter : PublicParameter)
    (secret : Generic.Seeded.ChainSecrets) : OracleComp OracleWorld Bool := do
  let result ← liftM
    (Generic.Concrete.treeNode parameter secret treeHeight Generic.Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog
  let sk := Generic.Concrete.precomputedSecretKey parameter secret (Generic.hashCacheOfLog result.2)
  EUFCMA.gameRest Generic.Concrete.scheme adversary ⟨result.1, parameter⟩ sk

theorem gameCore_independent_eq (adversary : Generic.Adversary) :
    EUFCMA.gameCore Generic.Concrete.scheme adversary = (do
      let parameter ← liftM Generic.Concrete.samplePublicParameter
      let secret ← liftM Generic.Concrete.sampleSecret
      gameAfterSecrets adversary parameter secret) := by
  simp only [EUFCMA.gameCore, Generic.Concrete.scheme, Generic.Concrete.precomputedKeygen, gameAfterSecrets,
    EUFCMA.gameRest, bind_assoc, pure_bind]

theorem runWorldSigning_sourceGame (secretKey : Generic.SecretKey)
    (publicKey : PublicKey) (adversary : Generic.Adversary) :
    Generic.Seeded.runWorldSigning (fun (request : Generic.SignRequest) => Generic.Concrete.precomputedCappedSign secretKey request.epoch request.message) (sourceGame publicKey adversary) =
      EUFCMA.gameRest Generic.Concrete.scheme adversary publicKey secretKey := by
  unfold sourceGame
  rw [Generic.Seeded.runWorldSigning, simulateQ_bind]
  change (Generic.Seeded.runWorldSigning (fun (request : Generic.SignRequest) => Generic.Concrete.precomputedCappedSign secretKey request.epoch request.message) (Generic.DeterministicSigning.withRequestLog (adversary.main publicKey)) >>=
    fun result => Generic.Seeded.runWorldSigning (fun (request : Generic.SignRequest) => Generic.Concrete.precomputedCappedSign secretKey request.epoch request.message) (Generic.DeterministicSigning.baseLift (finishGame publicKey result))) = _
  rw [Generic.Seeded.runWorldSigning_withRequestLog]
  have hlift (result) : Generic.Seeded.runWorldSigning (fun (request : Generic.SignRequest) => Generic.Concrete.precomputedCappedSign secretKey request.epoch request.message) (Generic.DeterministicSigning.baseLift (finishGame publicKey result)) =
      finishGame publicKey result := by
    rw [Generic.Seeded.runWorldSigning, Generic.DeterministicSigning.simulateQ_baseLift, simulateQ_ofLift_eq_self]
  simp_rw [hlift]
  unfold Generic.Seeded.loggedRun EUFCMA.gameRest finishGame transcriptWin
  rfl

theorem evalDist_tableGameAfterSecrets_memo (hash : QueryImpl HashSpec (StateT State ProbComp))
    (adversary : Generic.Adversary) (parameter : PublicParameter) (outputs : Generic.Seeded.ChainSecrets) (state : State) :
    𝒟[do
      let randomizers ← Generic.Seeded.sampleRandomizerOutputs
      (simulateQ (Generic.Seeded.worldHandler hash) (tableGameAfterSecrets (Generic.Seeded.memoAdversary adversary) parameter outputs randomizers)).run state] =
      𝒟[(simulateQ (Generic.Seeded.worldHandler hash) (gameAfterSecrets (Generic.Seeded.memoAdversary adversary)
        parameter outputs)).run state] := by
  unfold tableGameAfterSecrets gameAfterSecrets
  simp only [simulateQ_bind, StateT.run_bind]
  rw [evalDist_bind_bind_swap]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro result
  have hleft (randomizers) := runSigning_sourceGame randomizers (Generic.Concrete.precomputedSecretKey parameter outputs (Generic.hashCacheOfLog result.1.2))
    ⟨result.1.1, parameter⟩ (Generic.Seeded.memoAdversary adversary)
  simp_rw [← hleft]
  rw [← runWorldSigning_sourceGame, Generic.Seeded.simulateQ_runWorldSigning]
  exact Generic.Seeded.evalDist_tableRequests hash (Generic.Concrete.precomputedSecretKey parameter outputs (Generic.hashCacheOfLog result.1.2))
    (sourceGame ⟨result.1.1, parameter⟩ (Generic.Seeded.memoAdversary adversary))
    (freshRequests_sourceGame_memo _ _) result.2

theorem evalDist_referenceOutputs (adversary : Generic.Adversary) :
    𝒟[do
      let parameterOutput ← ($ᵗ HashOutput : ProbComp HashOutput)
      let outputs ← ($ᵗ Generic.Seeded.ChainOutputs)
      (simulateQ Generic.romImpl (gameAfterSecrets adversary (Generic.truncateHash parameterOutput)
        (Generic.Seeded.outputSecrets outputs))).run' ∅] =
      𝒟[(simulateQ Generic.romImpl (EUFCMA.gameCore Generic.Concrete.scheme adversary)).run' ∅] := by
  rw [gameCore_independent_eq, Generic.Seeded.run'_lift_sample_bind]
  trans 𝒟[do
    let parameter ← Generic.Concrete.samplePublicParameter
    let outputs ← ($ᵗ Generic.Seeded.ChainOutputs)
    (simulateQ Generic.romImpl (gameAfterSecrets adversary parameter (Generic.Seeded.outputSecrets outputs))).run' ∅]
  · exact Generic.Seeded.evalDist_parameter_continuation fun parameter => do
      let outputs ← ($ᵗ Generic.Seeded.ChainOutputs)
      (simulateQ Generic.romImpl (gameAfterSecrets adversary parameter (Generic.Seeded.outputSecrets outputs))).run' ∅
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  rw [Generic.Seeded.run'_lift_sample_bind]
  exact Generic.Seeded.evalDist_secrets_continuation fun secret =>
    (simulateQ Generic.romImpl (gameAfterSecrets adversary parameter secret)).run' ∅

theorem evalDist_independentTableGame_memo (adversary : Generic.Adversary) :
    𝒟[independentTableGame (Generic.Seeded.memoAdversary adversary)] =
      𝒟[(simulateQ Generic.romImpl (EUFCMA.gameCore Generic.Concrete.scheme (Generic.Seeded.memoAdversary adversary))).run' ∅] := by
  rw [← evalDist_referenceOutputs]
  unfold independentTableGame Generic.Seeded.drawSigningMaterial
  simp only [bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameterOutput
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro outputs
  have h := evalDist_tableGameAfterSecrets_memo randomOracle adversary (Generic.truncateHash parameterOutput) (Generic.Seeded.outputSecrets outputs) ∅
  rw [Generic.Seeded.worldHandler_randomOracle] at h
  have heq := congrArg (fun distribution => Prod.fst <$> distribution) h
  simpa only [StateT.run'_eq, evalDist_map, evalDist_bind, map_bind] using heq

theorem forgeAdvantage_deterministic_le_reference_direct (adversary : Generic.Adversary) (D : ℕ)
    (hD : Generic.Direct.IsDirectQueryBound adversary D) :
    EUFCMA.forgeAdvantage Generic.Seeded.scheme adversary ≤
      EUFCMA.forgeAdvantage Generic.Concrete.scheme (Generic.Seeded.memoAdversary adversary) +
        D / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  have hmemo := prob_independentTableGame_le_memo adversary
  rw [probOutput_congr rfl (evalDist_independentTableGame_memo adversary)] at hmemo
  exact (forgeAdvantage_deterministic_le_table_direct adversary D hD).trans (add_le_add hmemo le_rfl)

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Seeded.forgeAdvantage_deterministic_le_reference_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forgeAdvantage_deterministic_le_reference_direct

end XmssSecurity.TargetSum.EUFCMA.Seeded

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

/-- A reference bound including the seed-guessing loss closes the direct statement. -/
theorem direct_security_of_reference_bound (bits : ℕ)
    (h : ∀ (adversary : Generic.Adversary) (D : ℕ), 1 ≤ D →
      Generic.Direct.IsDirectQueryBound adversary D →
      forgeAdvantage Generic.Concrete.scheme adversary + D / ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤
        D / ((2 ^ bits : ℕ) : ℝ≥0∞)) :
    (notion SUFCMA.CountingMode.direct).HasClassicalSecurityBits Generic.xmss bits := by
  apply direct_security_of_isDirectQueryBound
  intro adversary D hD hbound
  exact (Seeded.forgeAdvantage_deterministic_le_reference_direct adversary D hbound).trans
    (h (Generic.Seeded.memoAdversary adversary) D hD
      (Generic.Seeded.memoAdversary_isDirectQueryBound adversary D hbound))

/-- info: 'XmssSecurity.TargetSum.EUFCMA.direct_security_of_reference_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms direct_security_of_reference_bound

end XmssSecurity.TargetSum.EUFCMA
