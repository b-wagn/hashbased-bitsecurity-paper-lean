import XmssSecurity.Proof.TargetSum.Deterministic.SignerBudgetTransfer
import XmssSecurity.Proof.TargetSum.Seeded.UnqueriedCacheTransfer
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Realize each independent tree-generation outcome under a supported cache that fixes
the seed derivations and all signing randomizers. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Seeded

open Generic.DeterministicSigning

attribute [local irreducible] Generic.sampleMasterSeed Generic.Seeded.derivationCache Generic.Seeded.signingDerivationCache
  Generic.Seeded.prepareRandomizers Generic.Seeded.sampleRandomizerOutputs Generic.Seeded.deriveParametersAndSecrets

theorem deriveParametersAndSecrets_support (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : Generic.Seeded.ChainOutputs) :
    ((Generic.truncateHash parameterOutput, Generic.Seeded.outputSecrets outputs), Generic.Seeded.derivationCache seed parameterOutput outputs)
      ∈ support ((simulateQ randomOracle (Generic.Seeded.deriveParametersAndSecrets seed)).run ∅) := by
  rw [mem_support_iff_of_evalDist_eq (Generic.Seeded.evalDist_deriveParametersAndSecrets seed),
    mem_support_bind_iff]
  refine ⟨parameterOutput, mem_support_uniformSample HashOutput, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨outputs, ?_, by simp⟩
  rw [mem_support_iff, probOutput_uniformSample]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

theorem prepareRandomizers_support (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : Generic.Seeded.ChainOutputs) (randomizers : Generic.Seeded.RandomizerOutputs) :
    (randomizers, Generic.Seeded.signingDerivationCache seed parameterOutput outputs randomizers) ∈
      support ((simulateQ randomOracle (Generic.Seeded.prepareRandomizers (Generic.truncateHash parameterOutput) seed)).run
        (Generic.Seeded.derivationCache seed parameterOutput outputs)) := by
  rw [mem_support_iff_of_evalDist_eq (Generic.Seeded.evalDist_prepareRandomizers seed parameterOutput outputs),
    support_map]
  refine ⟨randomizers, ?_, rfl⟩
  rw [mem_support_iff]
  unfold Generic.Seeded.sampleRandomizerOutputs
  rw [probOutput_uniformSample]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

noncomputable def prepareSigningMaterial (seed : MasterSeed) : OracleComp HashSpec Generic.Seeded.RandomizerOutputs := do
  let (parameter, _) ← Generic.Seeded.deriveParametersAndSecrets seed
  Generic.Seeded.prepareRandomizers parameter seed

theorem prepareSigningMaterial_support (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : Generic.Seeded.ChainOutputs) (randomizers : Generic.Seeded.RandomizerOutputs) :
    (randomizers, Generic.Seeded.signingDerivationCache seed parameterOutput outputs randomizers) ∈
      support ((simulateQ randomOracle (prepareSigningMaterial seed)).run ∅) := by
  rw [prepareSigningMaterial, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨((Generic.truncateHash parameterOutput, Generic.Seeded.outputSecrets outputs),
      Generic.Seeded.derivationCache seed parameterOutput outputs),
    deriveParametersAndSecrets_support seed parameterOutput outputs,
    prepareRandomizers_support seed parameterOutput outputs randomizers⟩

theorem run_deriveParametersAndSecrets_prepared (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : Generic.Seeded.ChainOutputs) (randomizers : Generic.Seeded.RandomizerOutputs) :
    (simulateQ randomOracle (Generic.Seeded.deriveParametersAndSecrets seed)).run
      (Generic.Seeded.signingDerivationCache seed parameterOutput outputs randomizers) =
        pure ((Generic.truncateHash parameterOutput, Generic.Seeded.outputSecrets outputs),
          Generic.Seeded.signingDerivationCache seed parameterOutput outputs randomizers) := by
  exact ((Generic.DeterministicSigning.resolves_of_run (Generic.Seeded.deriveParametersAndSecrets seed) ∅ _
    (deriveParametersAndSecrets_support seed parameterOutput outputs)).mono
      (Generic.DeterministicSigning.cache_le_of_run (Generic.Seeded.prepareRandomizers (Generic.truncateHash parameterOutput) seed) _ _
        (prepareRandomizers_support seed parameterOutput outputs randomizers))).run_eq_pure

theorem keygenFromSeed_eq_derive_then_tree (seed : MasterSeed) :
    Generic.Seeded.keygenFromSeed seed = (do
      let (parameter, secret) ← Generic.Seeded.deriveParametersAndSecrets seed
      let result ← (Generic.Concrete.treeNode parameter secret treeHeight Generic.Concrete.rootNode :
        OracleComp HashSpec Digest).withQueryLog
      pure (⟨result.1, parameter⟩,
        ⟨seed, Generic.Concrete.precomputedSecretKey parameter secret (Generic.hashCacheOfLog result.2)⟩)) := by
  simp only [Generic.Seeded.keygenFromSeed, Generic.Seeded.deriveParametersAndSecrets, Generic.Seeded.deriveChainSecrets, bind_assoc, pure_bind]

theorem run_keygenFromSeed_prepared (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : Generic.Seeded.ChainOutputs) (randomizers : Generic.Seeded.RandomizerOutputs) :
    (simulateQ randomOracle (Generic.Seeded.keygenFromSeed seed)).run
      (Generic.Seeded.signingDerivationCache seed parameterOutput outputs randomizers) =
      (fun result =>
        ((⟨result.1.1, Generic.truncateHash parameterOutput⟩,
          ⟨seed, Generic.Concrete.precomputedSecretKey (Generic.truncateHash parameterOutput)
            (Generic.Seeded.outputSecrets outputs) (Generic.hashCacheOfLog result.1.2)⟩), result.2)) <$>
        (simulateQ randomOracle
          (Generic.Concrete.treeNode (Generic.truncateHash parameterOutput) (Generic.Seeded.outputSecrets outputs)
            treeHeight Generic.Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog).run
          (Generic.Seeded.signingDerivationCache seed parameterOutput outputs randomizers) := by
  rw [keygenFromSeed_eq_derive_then_tree, simulateQ_bind, StateT.run_bind,
    run_deriveParametersAndSecrets_prepared, pure_bind]
  simp only [bind_pure_comp, simulateQ_map, StateT.run_map]

theorem xmss_keygen_prepared_support (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : Generic.Seeded.ChainOutputs) (randomizers : Generic.Seeded.RandomizerOutputs)
    (tree : (Digest × QueryLog HashSpec) × QueryCache HashSpec)
    (htree : tree ∈ support ((simulateQ randomOracle
      (Generic.Concrete.treeNode (Generic.truncateHash parameterOutput) (Generic.Seeded.outputSecrets outputs)
        treeHeight Generic.Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog).run
          (Generic.Seeded.signingDerivationCache seed parameterOutput outputs randomizers))) :
    ((⟨tree.1.1, Generic.truncateHash parameterOutput⟩,
      ⟨seed, Generic.Concrete.precomputedSecretKey (Generic.truncateHash parameterOutput)
        (Generic.Seeded.outputSecrets outputs) (Generic.hashCacheOfLog tree.1.2)⟩), tree.2) ∈
      support ((simulateQ Generic.romImpl Generic.xmss.keygen).run
        (Generic.Seeded.signingDerivationCache seed parameterOutput outputs randomizers)) := by
  change _ ∈ support ((simulateQ Generic.romImpl (do
    let candidate ← liftM Generic.sampleMasterSeed
    liftM (Generic.Seeded.keygenFromSeed candidate) : OracleComp OracleWorld _)).run _)
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  refine ⟨(seed, Generic.Seeded.signingDerivationCache seed parameterOutput outputs randomizers), ?_, ?_⟩
  · rw [Generic.romImpl, QueryImpl.simulateQ_add_liftM_left, unifFwdImpl.simulateQ_run, support_map]
    refine ⟨seed, ?_, rfl⟩
    rw [mem_support_iff]
    unfold Generic.sampleMasterSeed
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  · rw [Generic.romImpl, QueryImpl.simulateQ_add_liftM_right, run_keygenFromSeed_prepared, support_map]
    exact ⟨tree, htree, rfl⟩

theorem exists_prepared_tree_of_independent (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : Generic.Seeded.ChainOutputs) (randomizers : Generic.Seeded.RandomizerOutputs)
    (tree : (Digest × QueryLog HashSpec) × QueryCache HashSpec)
    (htree : tree ∈ support ((simulateQ randomOracle
      (Generic.Concrete.treeNode (Generic.truncateHash parameterOutput) (Generic.Seeded.outputSecrets outputs)
        treeHeight Generic.Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog).run ∅)) :
    ∃ cache,
      (tree.1, cache) ∈ support ((simulateQ randomOracle
        (Generic.Concrete.treeNode (Generic.truncateHash parameterOutput) (Generic.Seeded.outputSecrets outputs)
          treeHeight Generic.Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog).run
            (Generic.Seeded.signingDerivationCache seed parameterOutput outputs randomizers)) ∧
      Generic.Seeded.AgreeOutside (fun input => Generic.SeedHit input seed) cache tree.2 ∧
      (∀ position, cache (Generic.Seeded.randomizerInputs (Generic.truncateHash parameterOutput) seed position) =
        some (randomizers position)) := by
  classical
  have hqueries :
      (Generic.Concrete.treeNode (Generic.truncateHash parameterOutput) (Generic.Seeded.outputSecrets outputs)
        treeHeight Generic.Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog.IsQueryBoundP
          (Generic.Seeded.DerivationHit seed) 0 := by
    rw [withQueryLog,
      OracleComp.isQueryBoundP_iff_of_map_eq (QueryImpl.fst_map_run_withLogging _ _),
      simulateQ_ofLift_eq_self]
    exact (Generic.Concrete.treeNode_noSeed _ _ _ _).of_imp (fun _ h => h.2)
  obtain ⟨cache, hcache, hagree⟩ := support_transfer_of_no_protected_queries
    (Generic.Seeded.DerivationHit seed) _ hqueries _ ∅
    (Generic.Seeded.signingDerivationCache_agreeOutside_derivationHit seed parameterOutput outputs randomizers)
    tree htree
  refine ⟨cache, hcache, ?_, ?_⟩
  · intro input hinput
    exact hagree input (fun h => hinput h.1)
  · intro position
    exact (Generic.DeterministicSigning.cache_le_of_run _ _ _ hcache)
      (Generic.Seeded.signingDerivationCache_randomizer seed parameterOutput outputs randomizers position)

/-- info: 'XmssSecurity.TargetSum.Seeded.exists_prepared_tree_of_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_prepared_tree_of_independent

/-- info: 'XmssSecurity.TargetSum.Seeded.xmss_keygen_prepared_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_keygen_prepared_support

end XmssSecurity.TargetSum.Seeded
