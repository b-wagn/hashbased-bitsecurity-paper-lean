import XmssSecurity.Proof.EUFCMA.Memoization
import XmssSecurity.Proof.EUFCMA.DirectBridge
import XmssSecurity.Proof.Deterministic.ReferenceDistribution

/-! The full standard-forgery hop from the seeded scheme to the existing randomized
reference execution, with at most D / 2^256 loss for D direct hash queries. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.EUFCMA.Seeded

open XmssSecurity.Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {State : Type}

attribute [local irreducible] tableSign

noncomputable def gameAfterSecrets (adversary : Adversary) (parameter : PublicParameter)
    (secret : ChainSecrets) : OracleComp OracleWorld Bool := do
  let result ← liftM
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog
  let sk := Concrete.precomputedSecretKey parameter secret (hashCacheOfLog result.2)
  EUFCMA.gameRest Concrete.scheme adversary ⟨result.1, parameter⟩ sk

theorem gameCore_independent_eq (adversary : Adversary) :
    EUFCMA.gameCore Concrete.scheme adversary = (do
      let parameter ← liftM Concrete.samplePublicParameter
      let secret ← liftM Concrete.sampleSecret
      gameAfterSecrets adversary parameter secret) := by
  simp only [EUFCMA.gameCore, Concrete.scheme, Concrete.precomputedKeygen, gameAfterSecrets,
    EUFCMA.gameRest, bind_assoc, pure_bind]

theorem runWorldSigning_sourceGame (secretKey : XmssSecurity.SecretKey)
    (publicKey : PublicKey) (adversary : Adversary) :
    runWorldSigning (fun (request : SignRequest) => Concrete.precomputedCappedSign secretKey request.epoch request.message) (sourceGame publicKey adversary) =
      EUFCMA.gameRest Concrete.scheme adversary publicKey secretKey := by
  unfold sourceGame
  rw [runWorldSigning, simulateQ_bind]
  change (runWorldSigning (fun (request : SignRequest) => Concrete.precomputedCappedSign secretKey request.epoch request.message) (withRequestLog (adversary.main publicKey)) >>=
    fun result => runWorldSigning (fun (request : SignRequest) => Concrete.precomputedCappedSign secretKey request.epoch request.message) (baseLift (finishGame publicKey result))) = _
  rw [runWorldSigning_withRequestLog]
  have hlift (result) : runWorldSigning (fun (request : SignRequest) => Concrete.precomputedCappedSign secretKey request.epoch request.message) (baseLift (finishGame publicKey result)) =
      finishGame publicKey result := by
    rw [runWorldSigning, simulateQ_baseLift, simulateQ_ofLift_eq_self]
  simp_rw [hlift]
  unfold loggedRun EUFCMA.gameRest finishGame transcriptWin
  rfl

theorem evalDist_tableGameAfterSecrets_memo (hash : QueryImpl HashSpec (StateT State ProbComp))
    (adversary : Adversary) (parameter : PublicParameter) (outputs : ChainSecrets) (state : State) :
    𝒟[do
      let randomizers ← sampleRandomizerOutputs
      (simulateQ (worldHandler hash) (tableGameAfterSecrets (memoAdversary adversary) parameter outputs randomizers)).run state] =
      𝒟[(simulateQ (worldHandler hash) (gameAfterSecrets (memoAdversary adversary)
        parameter outputs)).run state] := by
  unfold tableGameAfterSecrets gameAfterSecrets
  simp only [simulateQ_bind, StateT.run_bind]
  rw [evalDist_bind_bind_swap]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro result
  have hleft (randomizers) := runSigning_sourceGame randomizers (Concrete.precomputedSecretKey parameter outputs (hashCacheOfLog result.1.2))
    ⟨result.1.1, parameter⟩ (memoAdversary adversary)
  simp_rw [← hleft]
  rw [← runWorldSigning_sourceGame, simulateQ_runWorldSigning]
  exact evalDist_tableRequests hash (Concrete.precomputedSecretKey parameter outputs (hashCacheOfLog result.1.2))
    (sourceGame ⟨result.1.1, parameter⟩ (memoAdversary adversary))
    (freshRequests_sourceGame_memo _ _) result.2

theorem evalDist_referenceOutputs (adversary : Adversary) :
    𝒟[do
      let parameterOutput ← ($ᵗ HashOutput : ProbComp HashOutput)
      let outputs ← ($ᵗ ChainOutputs)
      (simulateQ romImpl (gameAfterSecrets adversary (truncateHash parameterOutput)
        (outputSecrets outputs))).run' ∅] =
      𝒟[(simulateQ romImpl (EUFCMA.gameCore Concrete.scheme adversary)).run' ∅] := by
  rw [gameCore_independent_eq, run'_lift_sample_bind]
  trans 𝒟[do
    let parameter ← Concrete.samplePublicParameter
    let outputs ← ($ᵗ ChainOutputs)
    (simulateQ romImpl (gameAfterSecrets adversary parameter (outputSecrets outputs))).run' ∅]
  · exact evalDist_parameter_continuation fun parameter => do
      let outputs ← ($ᵗ ChainOutputs)
      (simulateQ romImpl (gameAfterSecrets adversary parameter (outputSecrets outputs))).run' ∅
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameter
  rw [run'_lift_sample_bind]
  exact evalDist_secrets_continuation fun secret =>
    (simulateQ romImpl (gameAfterSecrets adversary parameter secret)).run' ∅

theorem evalDist_independentTableGame_memo (adversary : Adversary) :
    𝒟[independentTableGame (memoAdversary adversary)] =
      𝒟[(simulateQ romImpl (EUFCMA.gameCore Concrete.scheme (memoAdversary adversary))).run' ∅] := by
  rw [← evalDist_referenceOutputs]
  unfold independentTableGame drawSigningMaterial
  simp only [bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameterOutput
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro outputs
  have h := evalDist_tableGameAfterSecrets_memo randomOracle adversary (truncateHash parameterOutput) (outputSecrets outputs) ∅
  rw [worldHandler_randomOracle] at h
  have heq := congrArg (fun distribution => Prod.fst <$> distribution) h
  simpa only [StateT.run'_eq, evalDist_map, evalDist_bind, map_bind] using heq

theorem forgeAdvantage_deterministic_le_reference_direct (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    EUFCMA.forgeAdvantage scheme adversary ≤
      EUFCMA.forgeAdvantage Concrete.scheme (memoAdversary adversary) +
        D / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  have hmemo := prob_independentTableGame_le_memo adversary
  rw [probOutput_congr rfl (evalDist_independentTableGame_memo adversary)] at hmemo
  exact (forgeAdvantage_deterministic_le_table_direct adversary D hD).trans (add_le_add hmemo le_rfl)

/-- info: 'XmssSecurity.EUFCMA.Seeded.forgeAdvantage_deterministic_le_reference_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forgeAdvantage_deterministic_le_reference_direct

end XmssSecurity.EUFCMA.Seeded

namespace XmssSecurity.EUFCMA

/-- A reference bound including the seed-guessing loss closes the direct statement. -/
theorem direct_security_of_reference_bound (bits : ℕ)
    (h : ∀ (adversary : XmssSecurity.Adversary) (D : ℕ), 1 ≤ D →
      Direct.IsDirectQueryBound adversary D →
      forgeAdvantage Concrete.scheme adversary + D / ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤
        D / ((2 ^ bits : ℕ) : ℝ≥0∞)) :
    (notion SUFCMA.CountingMode.direct).HasClassicalSecurityBits xmss bits := by
  apply direct_security_of_isDirectQueryBound
  intro adversary D hD hbound
  exact (Seeded.forgeAdvantage_deterministic_le_reference_direct adversary D hbound).trans
    (h (XmssSecurity.Seeded.memoAdversary adversary) D hD
      (XmssSecurity.Seeded.memoAdversary_isDirectQueryBound adversary D hbound))

/-- info: 'XmssSecurity.EUFCMA.direct_security_of_reference_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms direct_security_of_reference_bound

end XmssSecurity.EUFCMA
