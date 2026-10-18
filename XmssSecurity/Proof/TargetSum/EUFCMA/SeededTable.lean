import XmssSecurity.Proof.TargetSum.EUFCMA.Execution
import XmssSecurity.Proof.Generic.Direct.SeedGuessing
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Preserve standard freshness while replacing seeded derivations by independent
randomizer tables. Only direct seed-domain queries contribute the guessing loss. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.EUFCMA.Seeded
open XmssSecurity.EUFCMA

open XmssSecurity.Generic.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable def deterministicGameAfterSecrets (adversary : Generic.Adversary) (seed : MasterSeed)
    (parameter : PublicParameter) (secret : Generic.Seeded.ChainSecrets) : OracleComp OracleWorld Bool := do
  let result ← liftM
    (Generic.Concrete.treeNode parameter secret treeHeight Generic.Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog
  let sk := Generic.Concrete.precomputedSecretKey parameter secret (Generic.hashCacheOfLog result.2)
  EUFCMA.gameRest Generic.Seeded.scheme adversary ⟨result.1, parameter⟩ ⟨seed, sk⟩

noncomputable def tableGameAfterSecrets (adversary : Generic.Adversary) (parameter : PublicParameter)
    (secret : Generic.Seeded.ChainSecrets) (randomizers : Generic.Seeded.RandomizerOutputs) : OracleComp OracleWorld Bool := do
  let result ← liftM
    (Generic.Concrete.treeNode parameter secret treeHeight Generic.Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog
  let sk := Generic.Concrete.precomputedSecretKey parameter secret (Generic.hashCacheOfLog result.2)
  EUFCMA.gameRest (Generic.Seeded.tableScheme randomizers) adversary ⟨result.1, parameter⟩ sk

theorem gameCore_deterministic_eq (adversary : Generic.Adversary) :
    EUFCMA.gameCore Generic.Seeded.scheme adversary = (do
      let seed ← liftM Generic.sampleMasterSeed
      let (parameter, secret) ← liftM (Generic.Seeded.deriveParametersAndSecrets seed)
      deterministicGameAfterSecrets adversary seed parameter secret) := by
  simp only [EUFCMA.gameCore, Generic.Seeded.scheme, Generic.Seeded.keygen, Generic.Seeded.keygenFromSeed, deterministicGameAfterSecrets, EUFCMA.gameRest,
    Generic.Seeded.deriveParametersAndSecrets, Generic.Seeded.deriveChainSecrets, liftM_bind, liftM_pure, bind_assoc, pure_bind]

theorem erases_deterministicGameRest (known : QueryCache HashSpec) (seed : MasterSeed)
    (pk : PublicKey) (sk : Generic.SecretKey) (randomizers : Generic.Seeded.RandomizerOutputs)
    (hrandomizers : ∀ position, known (Generic.Seeded.randomizerInputs sk.parameter seed position) = some (randomizers position))
    (adversary : Generic.Adversary) :
    Generic.Seeded.Erases (Generic.Seeded.worldKnown known)
      (EUFCMA.gameRest Generic.Seeded.scheme adversary pk ⟨seed, sk⟩)
      (EUFCMA.gameRest (Generic.Seeded.tableScheme randomizers) adversary pk sk) := by
  unfold EUFCMA.gameRest
  apply Generic.Seeded.Erases.bind _ _ _ (fun _ => Generic.Seeded.Erases.refl (Generic.Seeded.worldKnown known) _)
  apply Generic.Seeded.Erases.simulateQ_writer
  intro input
  cases input with
  | inl input =>
      simp only [QueryImpl.add_apply_inl]
      exact .refl _ _
  | inr request =>
      simp only [QueryImpl.add_apply_inr, Generic.signingOracle, QueryImpl.run_withLogging_apply, bind_pure_comp]
      exact (Generic.Seeded.erases_sign known seed sk randomizers
        hrandomizers request.epoch request.message).lift_hash.map _

theorem erases_deterministicGameAfterSecrets (known : QueryCache HashSpec) (seed : MasterSeed)
    (parameter : PublicParameter) (secret : Generic.Seeded.ChainSecrets) (randomizers : Generic.Seeded.RandomizerOutputs)
    (hrandomizers : ∀ position, known (Generic.Seeded.randomizerInputs parameter seed position) = some (randomizers position))
    (adversary : Generic.Adversary) :
    Generic.Seeded.Erases (Generic.Seeded.worldKnown known) (deterministicGameAfterSecrets adversary seed parameter secret)
      (tableGameAfterSecrets adversary parameter secret randomizers) := by
  unfold deterministicGameAfterSecrets tableGameAfterSecrets
  apply (Generic.Seeded.Erases.refl (Generic.Seeded.worldKnown known) _).bind
  intro result
  exact erases_deterministicGameRest known seed ⟨result.1, parameter⟩
    (Generic.Concrete.precomputedSecretKey parameter secret (Generic.hashCacheOfLog result.2)) randomizers hrandomizers adversary

attribute [local irreducible] deterministicGameAfterSecrets tableGameAfterSecrets Generic.Seeded.signingDerivationCache

theorem evalDist_deterministicGameAfterSecrets_prepared (adversary : Generic.Adversary) (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : Generic.Seeded.ChainOutputs) :
    𝒟[(simulateQ Generic.romImpl (deterministicGameAfterSecrets adversary seed (Generic.truncateHash parameterOutput)
        (Generic.Seeded.outputSecrets outputs))).run' (Generic.Seeded.derivationCache seed parameterOutput outputs)] =
      𝒟[do
        let randomizers ← Generic.Seeded.sampleRandomizerOutputs
        (simulateQ Generic.romImpl (tableGameAfterSecrets adversary (Generic.truncateHash parameterOutput)
            (Generic.Seeded.outputSecrets outputs) randomizers)).run'
          (Generic.Seeded.signingDerivationCache seed parameterOutput outputs randomizers)] := by
  rw [Generic.Seeded.evalDist_presample_computation _
    (liftM (Generic.Seeded.prepareRandomizers (Generic.truncateHash parameterOutput) seed) : OracleComp OracleWorld Generic.Seeded.RandomizerOutputs)]
  rw [show simulateQ Generic.romImpl (liftM (Generic.Seeded.prepareRandomizers (Generic.truncateHash parameterOutput) seed) : OracleComp OracleWorld Generic.Seeded.RandomizerOutputs) =
      simulateQ randomOracle (Generic.Seeded.prepareRandomizers (Generic.truncateHash parameterOutput) seed)
      from QueryImpl.simulateQ_add_liftM_right _ _ _,
    evalDist_bind, Generic.Seeded.evalDist_prepareRandomizers, ← evalDist_bind, bind_map_left]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro randomizers
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  exact congrArg _ ((erases_deterministicGameAfterSecrets _ seed _ _ randomizers
    (Generic.Seeded.signingDerivationCache_randomizer seed parameterOutput outputs randomizers) adversary).evalDist_run _ le_rfl)

noncomputable def programmedDeterministicGame (adversary : Generic.Adversary) : ProbComp Bool := do
  let seed ← Generic.sampleMasterSeed
  let parameterOutput ← $ᵗ HashOutput
  let outputs ← $ᵗ Generic.Seeded.ChainOutputs
  let randomizers ← Generic.Seeded.sampleRandomizerOutputs
  (simulateQ Generic.romImpl (tableGameAfterSecrets adversary (Generic.truncateHash parameterOutput)
      (Generic.Seeded.outputSecrets outputs) randomizers)).run'
    (Generic.Seeded.signingDerivationCache seed parameterOutput outputs randomizers)

theorem evalDist_gameCore_deterministic_programmed (adversary : Generic.Adversary) :
    𝒟[(simulateQ Generic.romImpl (EUFCMA.gameCore Generic.Seeded.scheme adversary)).run' ∅] =
      𝒟[programmedDeterministicGame adversary] := by
  rw [gameCore_deterministic_eq, Generic.Seeded.run'_lift_sample_bind]
  unfold programmedDeterministicGame
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro seed
  rw [Generic.Seeded.run'_lift_hash_bind, evalDist_bind, Generic.Seeded.evalDist_deriveParametersAndSecrets, ← evalDist_bind]
  simp only [bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameterOutput
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro outputs
  exact evalDist_deterministicGameAfterSecrets_prepared adversary seed parameterOutput outputs

noncomputable def independentTableGame (adversary : Generic.Adversary) : ProbComp Bool := do
  let material ← Generic.Seeded.drawSigningMaterial
  (simulateQ Generic.romImpl (tableGameAfterSecrets adversary (Generic.truncateHash material.1) (Generic.Seeded.outputSecrets material.2.1) material.2.2)).run' ∅

theorem evalDist_programmedDeterministicGame_seed_last (adversary : Generic.Adversary) :
    𝒟[programmedDeterministicGame adversary] = 𝒟[do
      let material ← Generic.Seeded.drawSigningMaterial
      let seed ← Generic.sampleMasterSeed
      (simulateQ Generic.romImpl (tableGameAfterSecrets adversary (Generic.truncateHash material.1) (Generic.Seeded.outputSecrets material.2.1) material.2.2)).run'
        (Generic.Seeded.signingDerivationCache seed material.1 material.2.1 material.2.2)] := by
  have heq : programmedDeterministicGame adversary = (do
      let seed ← Generic.sampleMasterSeed
      let material ← Generic.Seeded.drawSigningMaterial
      (simulateQ Generic.romImpl (tableGameAfterSecrets adversary (Generic.truncateHash material.1) (Generic.Seeded.outputSecrets material.2.1) material.2.2)).run'
        (Generic.Seeded.signingDerivationCache seed material.1 material.2.1 material.2.2)) := by
    simp only [programmedDeterministicGame, Generic.Seeded.drawSigningMaterial, bind_assoc, pure_bind]
  rw [heq, evalDist_bind_bind_swap]

theorem tableGameRest_bound (randomizers : Generic.Seeded.RandomizerOutputs) (adversary : Generic.Adversary) (D : ℕ)
    (hD : Generic.Direct.IsDirectQueryBound adversary D) (pk : PublicKey) (sk : Generic.SecretKey) :
    (EUFCMA.gameRest (Generic.Seeded.tableScheme randomizers) adversary pk sk).IsQueryBoundP (Generic.Seeded.hashBad Generic.MaySeedHit) D := by
  unfold EUFCMA.gameRest
  rw [← Nat.add_zero D]
  refine OracleComp.isQueryBoundP_bind
    (Generic.Seeded.isQueryBoundP_simulateQ_writer_run _ Generic.Direct.IsDirectHashQuery _
      (Generic.Seeded.tableGameImpl_step randomizers sk) _ D (hD pk)) ?_
  rintro ⟨forgery, log⟩ _
  rw [← Nat.add_zero 0]
  refine OracleComp.isQueryBoundP_bind
    (Generic.Seeded.liftM_hash_noSeed _ (Generic.Concrete.verify_noSeed _ _ _ _)) ?_
  intro verified _
  simp

theorem tableGameAfterSecrets_bound (adversary : Generic.Adversary) (D : ℕ)
    (hD : Generic.Direct.IsDirectQueryBound adversary D) (parameter : PublicParameter)
    (secret : Generic.Seeded.ChainSecrets) (randomizers : Generic.Seeded.RandomizerOutputs) :
    (tableGameAfterSecrets adversary parameter secret randomizers).IsQueryBoundP
      (Generic.Seeded.hashBad Generic.MaySeedHit) D := by
  unfold tableGameAfterSecrets
  rw [← Nat.zero_add D]
  refine OracleComp.isQueryBoundP_bind (Generic.Seeded.liftM_hash_noSeed _ ?_)
    (fun result _ => tableGameRest_bound randomizers adversary D hD _ _)
  rw [withQueryLog, OracleComp.isQueryBoundP_iff_of_map_eq (QueryImpl.fst_map_run_withLogging _ _),
    simulateQ_ofLift_eq_self]
  exact Generic.Concrete.treeNode_noSeed _ _ _ _

theorem forgeAdvantage_deterministic_le_table_direct (adversary : Generic.Adversary) (D : ℕ)
    (hD : Generic.Direct.IsDirectQueryBound adversary D) :
    EUFCMA.forgeAdvantage Generic.Seeded.scheme adversary ≤ Pr[= true | independentTableGame adversary] +
      D / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  unfold EUFCMA.forgeAdvantage independentTableGame
  simp only [probOutput_def, evalDist_gameCore_deterministic_programmed,
    evalDist_programmedDeterministicGame_seed_last]
  change Pr[= true | Generic.Seeded.drawSigningMaterial >>= fun material => Generic.sampleMasterSeed >>= fun seed =>
      (simulateQ Generic.romImpl (tableGameAfterSecrets adversary (Generic.truncateHash material.1)
        (Generic.Seeded.outputSecrets material.2.1) material.2.2)).run'
        (Generic.Seeded.signingDerivationCache seed material.1 material.2.1 material.2.2)] ≤
    Pr[= true | Generic.Seeded.drawSigningMaterial >>= fun material =>
      (simulateQ Generic.romImpl (tableGameAfterSecrets adversary (Generic.truncateHash material.1)
        (Generic.Seeded.outputSecrets material.2.1) material.2.2)).run' ∅] + _
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply probEvent_bind_congr_le_add
  intro material _
  exact Generic.Seeded.probEvent_random_cache_change_derivationHit_le _
    (fun seed => Generic.Seeded.signingDerivationCache seed material.1 material.2.1 material.2.2) ∅
    (fun seed => Generic.Seeded.signingDerivationCache_agreeOutside_derivationHit seed _ _ _) D
    (tableGameAfterSecrets_bound adversary D hD _ _ _) (fun value => value = true)

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Seeded.forgeAdvantage_deterministic_le_table_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forgeAdvantage_deterministic_le_table_direct

end XmssSecurity.TargetSum.EUFCMA.Seeded
