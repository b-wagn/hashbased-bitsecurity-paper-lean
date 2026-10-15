import XmssSecurity.Proof.EUFCMA.Execution
import XmssSecurity.Proof.Direct.SeedGuessing

/-! Preserve standard freshness while replacing seeded derivations by independent
randomizer tables. Only direct seed-domain queries contribute the guessing loss. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.EUFCMA.Seeded

open XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable def deterministicGameAfterSecrets (adversary : Adversary) (seed : MasterSeed)
    (parameter : PublicParameter) (secret : ChainSecrets) : OracleComp OracleWorld Bool := do
  let result ← liftM
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog
  let sk := Concrete.precomputedSecretKey parameter secret (hashCacheOfLog result.2)
  EUFCMA.gameRest scheme adversary ⟨result.1, parameter⟩ ⟨seed, sk⟩

noncomputable def tableGameAfterSecrets (adversary : Adversary) (parameter : PublicParameter)
    (secret : ChainSecrets) (randomizers : RandomizerOutputs) : OracleComp OracleWorld Bool := do
  let result ← liftM
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog
  let sk := Concrete.precomputedSecretKey parameter secret (hashCacheOfLog result.2)
  EUFCMA.gameRest (tableScheme randomizers) adversary ⟨result.1, parameter⟩ sk

theorem gameCore_deterministic_eq (adversary : Adversary) :
    EUFCMA.gameCore scheme adversary = (do
      let seed ← liftM sampleMasterSeed
      let (parameter, secret) ← liftM (deriveParametersAndSecrets seed)
      deterministicGameAfterSecrets adversary seed parameter secret) := by
  simp only [EUFCMA.gameCore, scheme, keygen, keygenFromSeed, deterministicGameAfterSecrets, EUFCMA.gameRest,
    deriveParametersAndSecrets, deriveChainSecrets, liftM_bind, liftM_pure, bind_assoc, pure_bind]

theorem erases_deterministicGameRest (known : QueryCache HashSpec) (seed : MasterSeed)
    (pk : PublicKey) (sk : XmssSecurity.SecretKey) (randomizers : RandomizerOutputs)
    (hrandomizers : ∀ position, known (randomizerInputs sk.parameter seed position) = some (randomizers position))
    (adversary : Adversary) :
    Erases (worldKnown known)
      (EUFCMA.gameRest scheme adversary pk ⟨seed, sk⟩)
      (EUFCMA.gameRest (tableScheme randomizers) adversary pk sk) := by
  unfold EUFCMA.gameRest
  apply Erases.bind _ _ _ (fun _ => Erases.refl (worldKnown known) _)
  apply Erases.simulateQ_writer
  intro input
  cases input with
  | inl input =>
      simp only [QueryImpl.add_apply_inl]
      exact .refl _ _
  | inr request =>
      simp only [QueryImpl.add_apply_inr, signingOracle, QueryImpl.run_withLogging_apply, bind_pure_comp]
      exact (erases_sign known seed sk randomizers
        hrandomizers request.epoch request.message).lift_hash.map _

theorem erases_deterministicGameAfterSecrets (known : QueryCache HashSpec) (seed : MasterSeed)
    (parameter : PublicParameter) (secret : ChainSecrets) (randomizers : RandomizerOutputs)
    (hrandomizers : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (adversary : Adversary) :
    Erases (worldKnown known) (deterministicGameAfterSecrets adversary seed parameter secret)
      (tableGameAfterSecrets adversary parameter secret randomizers) := by
  unfold deterministicGameAfterSecrets tableGameAfterSecrets
  apply (Erases.refl (worldKnown known) _).bind
  intro result
  exact erases_deterministicGameRest known seed ⟨result.1, parameter⟩
    (Concrete.precomputedSecretKey parameter secret (hashCacheOfLog result.2)) randomizers hrandomizers adversary

attribute [local irreducible] deterministicGameAfterSecrets tableGameAfterSecrets signingDerivationCache

theorem evalDist_deterministicGameAfterSecrets_prepared (adversary : Adversary) (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : ChainOutputs) :
    𝒟[(simulateQ romImpl (deterministicGameAfterSecrets adversary seed (truncateHash parameterOutput)
        (outputSecrets outputs))).run' (derivationCache seed parameterOutput outputs)] =
      𝒟[do
        let randomizers ← sampleRandomizerOutputs
        (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash parameterOutput)
            (outputSecrets outputs) randomizers)).run'
          (signingDerivationCache seed parameterOutput outputs randomizers)] := by
  rw [evalDist_presample_computation _
    (liftM (prepareRandomizers (truncateHash parameterOutput) seed) : OracleComp OracleWorld RandomizerOutputs)]
  rw [show simulateQ romImpl (liftM (prepareRandomizers (truncateHash parameterOutput) seed) : OracleComp OracleWorld RandomizerOutputs) =
      simulateQ randomOracle (prepareRandomizers (truncateHash parameterOutput) seed)
      from QueryImpl.simulateQ_add_liftM_right _ _ _,
    evalDist_bind, evalDist_prepareRandomizers, ← evalDist_bind, bind_map_left]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro randomizers
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  exact congrArg _ ((erases_deterministicGameAfterSecrets _ seed _ _ randomizers
    (signingDerivationCache_randomizer seed parameterOutput outputs randomizers) adversary).evalDist_run _ le_rfl)

noncomputable def programmedDeterministicGame (adversary : Adversary) : ProbComp Bool := do
  let seed ← sampleMasterSeed
  let parameterOutput ← $ᵗ HashOutput
  let outputs ← $ᵗ ChainOutputs
  let randomizers ← sampleRandomizerOutputs
  (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash parameterOutput)
      (outputSecrets outputs) randomizers)).run'
    (signingDerivationCache seed parameterOutput outputs randomizers)

theorem evalDist_gameCore_deterministic_programmed (adversary : Adversary) :
    𝒟[(simulateQ romImpl (EUFCMA.gameCore scheme adversary)).run' ∅] =
      𝒟[programmedDeterministicGame adversary] := by
  rw [gameCore_deterministic_eq, run'_lift_sample_bind]
  unfold programmedDeterministicGame
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro seed
  rw [run'_lift_hash_bind, evalDist_bind, evalDist_deriveParametersAndSecrets, ← evalDist_bind]
  simp only [bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameterOutput
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro outputs
  exact evalDist_deterministicGameAfterSecrets_prepared adversary seed parameterOutput outputs

noncomputable def independentTableGame (adversary : Adversary) : ProbComp Bool := do
  let material ← drawSigningMaterial
  (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1) (outputSecrets material.2.1) material.2.2)).run' ∅

theorem evalDist_programmedDeterministicGame_seed_last (adversary : Adversary) :
    𝒟[programmedDeterministicGame adversary] = 𝒟[do
      let material ← drawSigningMaterial
      let seed ← sampleMasterSeed
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1) (outputSecrets material.2.1) material.2.2)).run'
        (signingDerivationCache seed material.1 material.2.1 material.2.2)] := by
  have heq : programmedDeterministicGame adversary = (do
      let seed ← sampleMasterSeed
      let material ← drawSigningMaterial
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1) (outputSecrets material.2.1) material.2.2)).run'
        (signingDerivationCache seed material.1 material.2.1 material.2.2)) := by
    simp only [programmedDeterministicGame, drawSigningMaterial, bind_assoc, pure_bind]
  rw [heq, evalDist_bind_bind_swap]

theorem tableGameRest_bound (randomizers : RandomizerOutputs) (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (pk : PublicKey) (sk : XmssSecurity.SecretKey) :
    (EUFCMA.gameRest (tableScheme randomizers) adversary pk sk).IsQueryBoundP (hashBad MaySeedHit) D := by
  unfold EUFCMA.gameRest
  rw [← Nat.add_zero D]
  refine OracleComp.isQueryBoundP_bind
    (isQueryBoundP_simulateQ_writer_run _ Direct.IsDirectHashQuery _
      (tableGameImpl_step randomizers sk) _ D (hD pk)) ?_
  rintro ⟨forgery, log⟩ _
  rw [← Nat.add_zero 0]
  refine OracleComp.isQueryBoundP_bind
    (liftM_hash_noSeed _ (Concrete.verify_noSeed _ _ _ _)) ?_
  intro verified _
  simp

theorem tableGameAfterSecrets_bound (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (parameter : PublicParameter)
    (secret : ChainSecrets) (randomizers : RandomizerOutputs) :
    (tableGameAfterSecrets adversary parameter secret randomizers).IsQueryBoundP
      (hashBad MaySeedHit) D := by
  unfold tableGameAfterSecrets
  rw [← Nat.zero_add D]
  refine OracleComp.isQueryBoundP_bind (liftM_hash_noSeed _ ?_)
    (fun result _ => tableGameRest_bound randomizers adversary D hD _ _)
  rw [withQueryLog, OracleComp.isQueryBoundP_iff_of_map_eq (QueryImpl.fst_map_run_withLogging _ _),
    simulateQ_ofLift_eq_self]
  exact Concrete.treeNode_noSeed _ _ _ _

theorem forgeAdvantage_deterministic_le_table_direct (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    EUFCMA.forgeAdvantage scheme adversary ≤ Pr[= true | independentTableGame adversary] +
      D / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  unfold EUFCMA.forgeAdvantage independentTableGame
  simp only [probOutput_def, evalDist_gameCore_deterministic_programmed,
    evalDist_programmedDeterministicGame_seed_last]
  change Pr[= true | drawSigningMaterial >>= fun material => sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1)
        (outputSecrets material.2.1) material.2.2)).run'
        (signingDerivationCache seed material.1 material.2.1 material.2.2)] ≤
    Pr[= true | drawSigningMaterial >>= fun material =>
      (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash material.1)
        (outputSecrets material.2.1) material.2.2)).run' ∅] + _
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply probEvent_bind_congr_le_add
  intro material _
  exact probEvent_random_cache_change_derivationHit_le _
    (fun seed => signingDerivationCache seed material.1 material.2.1 material.2.2) ∅
    (fun seed => signingDerivationCache_agreeOutside_derivationHit seed _ _ _) D
    (tableGameAfterSecrets_bound adversary D hD _ _ _) (fun value => value = true)

/-- info: 'XmssSecurity.EUFCMA.Seeded.forgeAdvantage_deterministic_le_table_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forgeAdvantage_deterministic_le_table_direct

end XmssSecurity.EUFCMA.Seeded
