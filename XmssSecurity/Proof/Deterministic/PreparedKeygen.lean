import XmssSecurity.Proof.Deterministic.SignerBudgetTransfer
import XmssSecurity.Proof.Seeded.UnqueriedCacheTransfer

/-! Realize each independent tree-generation outcome under a supported cache that fixes
the seed derivations and all signing randomizers. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Seeded

open DeterministicSigning

attribute [local irreducible] sampleMasterSeed derivationCache signingDerivationCache
  prepareRandomizers sampleRandomizerOutputs deriveParametersAndSecrets

theorem deriveParametersAndSecrets_support (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : ChainOutputs) :
    ((truncateHash parameterOutput, outputSecrets outputs), derivationCache seed parameterOutput outputs)
      ∈ support ((simulateQ randomOracle (deriveParametersAndSecrets seed)).run ∅) := by
  rw [mem_support_iff_of_evalDist_eq (evalDist_deriveParametersAndSecrets seed),
    mem_support_bind_iff]
  refine ⟨parameterOutput, mem_support_uniformSample HashOutput, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨outputs, ?_, by simp⟩
  rw [mem_support_iff, probOutput_uniformSample]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

theorem prepareRandomizers_support (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : ChainOutputs) (randomizers : RandomizerOutputs) :
    (randomizers, signingDerivationCache seed parameterOutput outputs randomizers) ∈
      support ((simulateQ randomOracle (prepareRandomizers (truncateHash parameterOutput) seed)).run
        (derivationCache seed parameterOutput outputs)) := by
  rw [mem_support_iff_of_evalDist_eq (evalDist_prepareRandomizers seed parameterOutput outputs),
    support_map]
  refine ⟨randomizers, ?_, rfl⟩
  rw [mem_support_iff]
  unfold sampleRandomizerOutputs
  rw [probOutput_uniformSample]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

noncomputable def prepareSigningMaterial (seed : MasterSeed) : OracleComp HashSpec RandomizerOutputs := do
  let (parameter, _) ← deriveParametersAndSecrets seed
  prepareRandomizers parameter seed

theorem prepareSigningMaterial_support (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : ChainOutputs) (randomizers : RandomizerOutputs) :
    (randomizers, signingDerivationCache seed parameterOutput outputs randomizers) ∈
      support ((simulateQ randomOracle (prepareSigningMaterial seed)).run ∅) := by
  rw [prepareSigningMaterial, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨((truncateHash parameterOutput, outputSecrets outputs),
      derivationCache seed parameterOutput outputs),
    deriveParametersAndSecrets_support seed parameterOutput outputs,
    prepareRandomizers_support seed parameterOutput outputs randomizers⟩

theorem run_deriveParametersAndSecrets_prepared (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : ChainOutputs) (randomizers : RandomizerOutputs) :
    (simulateQ randomOracle (deriveParametersAndSecrets seed)).run
      (signingDerivationCache seed parameterOutput outputs randomizers) =
        pure ((truncateHash parameterOutput, outputSecrets outputs),
          signingDerivationCache seed parameterOutput outputs randomizers) := by
  exact ((resolves_of_run (deriveParametersAndSecrets seed) ∅ _
    (deriveParametersAndSecrets_support seed parameterOutput outputs)).mono
      (cache_le_of_run (prepareRandomizers (truncateHash parameterOutput) seed) _ _
        (prepareRandomizers_support seed parameterOutput outputs randomizers))).run_eq_pure

theorem keygenFromSeed_eq_derive_then_tree (seed : MasterSeed) :
    keygenFromSeed seed = (do
      let (parameter, secret) ← deriveParametersAndSecrets seed
      let result ← (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest).withQueryLog
      pure (⟨result.1, parameter⟩,
        ⟨seed, Concrete.precomputedSecretKey parameter secret (hashCacheOfLog result.2)⟩)) := by
  simp only [keygenFromSeed, deriveParametersAndSecrets, deriveChainSecrets, bind_assoc, pure_bind]

theorem run_keygenFromSeed_prepared (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : ChainOutputs) (randomizers : RandomizerOutputs) :
    (simulateQ randomOracle (keygenFromSeed seed)).run
      (signingDerivationCache seed parameterOutput outputs randomizers) =
      (fun result =>
        ((⟨result.1.1, truncateHash parameterOutput⟩,
          ⟨seed, Concrete.precomputedSecretKey (truncateHash parameterOutput)
            (outputSecrets outputs) (hashCacheOfLog result.1.2)⟩), result.2)) <$>
        (simulateQ randomOracle
          (Concrete.treeNode (truncateHash parameterOutput) (outputSecrets outputs)
            treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog).run
          (signingDerivationCache seed parameterOutput outputs randomizers) := by
  rw [keygenFromSeed_eq_derive_then_tree, simulateQ_bind, StateT.run_bind,
    run_deriveParametersAndSecrets_prepared, pure_bind]
  simp only [bind_pure_comp, simulateQ_map, StateT.run_map]

theorem xmss_keygen_prepared_support (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : ChainOutputs) (randomizers : RandomizerOutputs)
    (tree : (Digest × QueryLog HashSpec) × QueryCache HashSpec)
    (htree : tree ∈ support ((simulateQ randomOracle
      (Concrete.treeNode (truncateHash parameterOutput) (outputSecrets outputs)
        treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog).run
          (signingDerivationCache seed parameterOutput outputs randomizers))) :
    ((⟨tree.1.1, truncateHash parameterOutput⟩,
      ⟨seed, Concrete.precomputedSecretKey (truncateHash parameterOutput)
        (outputSecrets outputs) (hashCacheOfLog tree.1.2)⟩), tree.2) ∈
      support ((simulateQ romImpl xmss.keygen).run
        (signingDerivationCache seed parameterOutput outputs randomizers)) := by
  change _ ∈ support ((simulateQ romImpl (do
    let candidate ← liftM sampleMasterSeed
    liftM (keygenFromSeed candidate) : OracleComp OracleWorld _)).run _)
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  refine ⟨(seed, signingDerivationCache seed parameterOutput outputs randomizers), ?_, ?_⟩
  · rw [romImpl, QueryImpl.simulateQ_add_liftM_left, unifFwdImpl.simulateQ_run, support_map]
    refine ⟨seed, ?_, rfl⟩
    rw [mem_support_iff]
    unfold sampleMasterSeed
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  · rw [romImpl, QueryImpl.simulateQ_add_liftM_right, run_keygenFromSeed_prepared, support_map]
    exact ⟨tree, htree, rfl⟩

theorem exists_prepared_tree_of_independent (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : ChainOutputs) (randomizers : RandomizerOutputs)
    (tree : (Digest × QueryLog HashSpec) × QueryCache HashSpec)
    (htree : tree ∈ support ((simulateQ randomOracle
      (Concrete.treeNode (truncateHash parameterOutput) (outputSecrets outputs)
        treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog).run ∅)) :
    ∃ cache,
      (tree.1, cache) ∈ support ((simulateQ randomOracle
        (Concrete.treeNode (truncateHash parameterOutput) (outputSecrets outputs)
          treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog).run
            (signingDerivationCache seed parameterOutput outputs randomizers)) ∧
      AgreeOutside (fun input => SeedHit input seed) cache tree.2 ∧
      (∀ position, cache (randomizerInputs (truncateHash parameterOutput) seed position) =
        some (randomizers position)) := by
  classical
  have hqueries :
      (Concrete.treeNode (truncateHash parameterOutput) (outputSecrets outputs)
        treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog.IsQueryBoundP
          (DerivationHit seed) 0 := by
    rw [withQueryLog,
      OracleComp.isQueryBoundP_iff_of_map_eq (QueryImpl.fst_map_run_withLogging _ _),
      simulateQ_ofLift_eq_self]
    exact (Concrete.treeNode_noSeed _ _ _ _).of_imp (fun _ h => h.2)
  obtain ⟨cache, hcache, hagree⟩ := support_transfer_of_no_protected_queries
    (DerivationHit seed) _ hqueries _ ∅
    (signingDerivationCache_agreeOutside_derivationHit seed parameterOutput outputs randomizers)
    tree htree
  refine ⟨cache, hcache, ?_, ?_⟩
  · intro input hinput
    exact hagree input (fun h => hinput h.1)
  · intro position
    exact (cache_le_of_run _ _ _ hcache)
      (signingDerivationCache_randomizer seed parameterOutput outputs randomizers position)

/-- info: 'XmssSecurity.Seeded.exists_prepared_tree_of_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_prepared_tree_of_independent

/-- info: 'XmssSecurity.Seeded.xmss_keygen_prepared_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_keygen_prepared_support

end XmssSecurity.Seeded
