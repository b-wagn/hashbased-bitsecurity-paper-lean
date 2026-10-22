import Xmss.Proof.TargetSum.Deterministic.SignerBudgetTransfer
import Xmss.Proof.TargetSum.Seeded.UnqueriedCacheTransfer
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Realize each independent tree-generation outcome under a supported cache that fixes
the seed derivations and all signing randomizers. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Seeded

open DeterministicSigning

attribute [local irreducible] Generic.sampleMasterSeed Seeded.derivationCache Seeded.signingDerivationCache
  Seeded.prepareRandomizers Seeded.sampleRandomizerOutputs Seeded.deriveParametersAndSecrets

theorem deriveParametersAndSecrets_support (seed : MasterSeed)
    (parameterOutput : Digest) (outputs : Seeded.ChainSecrets) :
    ((parameterOutput, outputs), Seeded.derivationCache seed parameterOutput outputs)
      ∈ support ((simulateQ randomOracle (Seeded.deriveParametersAndSecrets seed)).run ∅) := by
  rw [mem_support_iff_of_evalDist_eq (Seeded.evalDist_deriveParametersAndSecrets seed),
    mem_support_bind_iff]
  refine ⟨parameterOutput, mem_support_uniformSample Digest, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨outputs, ?_, by simp⟩
  rw [mem_support_iff, probOutput_uniformSample]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

theorem prepareRandomizers_support (seed : MasterSeed)
    (parameterOutput : Digest) (outputs : Seeded.ChainSecrets) (randomizers : Seeded.RandomizerOutputs) :
    (randomizers, Seeded.signingDerivationCache seed parameterOutput outputs randomizers) ∈
      support ((simulateQ randomOracle (Seeded.prepareRandomizers (parameterOutput) seed)).run
        (Seeded.derivationCache seed parameterOutput outputs)) := by
  rw [mem_support_iff_of_evalDist_eq (Seeded.evalDist_prepareRandomizers seed parameterOutput outputs),
    support_map]
  refine ⟨randomizers, ?_, rfl⟩
  rw [mem_support_iff]
  unfold Seeded.sampleRandomizerOutputs
  rw [probOutput_uniformSample]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

noncomputable def prepareSigningMaterial (seed : MasterSeed) : OracleComp HashSpec Seeded.RandomizerOutputs := do
  let (parameter, _) ← Seeded.deriveParametersAndSecrets seed
  Seeded.prepareRandomizers parameter seed

theorem prepareSigningMaterial_support (seed : MasterSeed)
    (parameterOutput : Digest) (outputs : Seeded.ChainSecrets) (randomizers : Seeded.RandomizerOutputs) :
    (randomizers, Seeded.signingDerivationCache seed parameterOutput outputs randomizers) ∈
      support ((simulateQ randomOracle (prepareSigningMaterial seed)).run ∅) := by
  rw [prepareSigningMaterial, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  exact ⟨((parameterOutput, outputs),
      Seeded.derivationCache seed parameterOutput outputs),
    deriveParametersAndSecrets_support seed parameterOutput outputs,
    prepareRandomizers_support seed parameterOutput outputs randomizers⟩

theorem run_deriveParametersAndSecrets_prepared (seed : MasterSeed)
    (parameterOutput : Digest) (outputs : Seeded.ChainSecrets) (randomizers : Seeded.RandomizerOutputs) :
    (simulateQ randomOracle (Seeded.deriveParametersAndSecrets seed)).run
      (Seeded.signingDerivationCache seed parameterOutput outputs randomizers) =
        pure ((parameterOutput, outputs),
          Seeded.signingDerivationCache seed parameterOutput outputs randomizers) := by
  exact ((DeterministicSigning.resolves_of_run (Seeded.deriveParametersAndSecrets seed) ∅ _
    (deriveParametersAndSecrets_support seed parameterOutput outputs)).mono
      (DeterministicSigning.cache_le_of_run (Seeded.prepareRandomizers (parameterOutput) seed) _ _
        (prepareRandomizers_support seed parameterOutput outputs randomizers))).run_eq_pure

theorem keygenFromSeed_eq_derive_then_tree (seed : MasterSeed) :
    Generic.Seeded.keygenFromSeed seed = (do
      let (parameter, secret) ← Seeded.deriveParametersAndSecrets seed
      let result ← (Generic.Merkle.treeNode parameter secret treeHeight Generic.Merkle.rootNode :
        OracleComp HashSpec Digest).withQueryLog
      pure (⟨result.1, parameter⟩,
        ⟨seed, Generic.Keygen.precomputedSecretKey parameter secret (Generic.hashCacheOfLog result.2)⟩)) := by
  simp only [Generic.Seeded.keygenFromSeed, Seeded.deriveParametersAndSecrets, Seeded.deriveChainSecrets, bind_assoc, pure_bind]

theorem run_keygenFromSeed_prepared (seed : MasterSeed)
    (parameterOutput : Digest) (outputs : Seeded.ChainSecrets) (randomizers : Seeded.RandomizerOutputs) :
    (simulateQ randomOracle (Generic.Seeded.keygenFromSeed seed)).run
      (Seeded.signingDerivationCache seed parameterOutput outputs randomizers) =
      (fun result =>
        ((⟨result.1.1, parameterOutput⟩,
          ⟨seed, Generic.Keygen.precomputedSecretKey (parameterOutput)
            (outputs) (Generic.hashCacheOfLog result.1.2)⟩), result.2)) <$>
        (simulateQ randomOracle
          (Generic.Merkle.treeNode (parameterOutput) (outputs)
            treeHeight Generic.Merkle.rootNode : OracleComp HashSpec Digest).withQueryLog).run
          (Seeded.signingDerivationCache seed parameterOutput outputs randomizers) := by
  rw [keygenFromSeed_eq_derive_then_tree, simulateQ_bind, StateT.run_bind,
    run_deriveParametersAndSecrets_prepared, pure_bind]
  simp only [bind_pure_comp, simulateQ_map, StateT.run_map]

theorem xmss_keygen_prepared_support (seed : MasterSeed)
    (parameterOutput : Digest) (outputs : Seeded.ChainSecrets) (randomizers : Seeded.RandomizerOutputs)
    (tree : (Digest × QueryLog HashSpec) × QueryCache HashSpec)
    (htree : tree ∈ support ((simulateQ randomOracle
      (Generic.Merkle.treeNode (parameterOutput) (outputs)
        treeHeight Generic.Merkle.rootNode : OracleComp HashSpec Digest).withQueryLog).run
          (Seeded.signingDerivationCache seed parameterOutput outputs randomizers))) :
    ((⟨tree.1.1, parameterOutput⟩,
      ⟨seed, Generic.Keygen.precomputedSecretKey (parameterOutput)
        (outputs) (Generic.hashCacheOfLog tree.1.2)⟩), tree.2) ∈
      support ((simulateQ romImpl Generic.xmss.keygen).run
        (Seeded.signingDerivationCache seed parameterOutput outputs randomizers)) := by
  change _ ∈ support ((simulateQ romImpl (do
    let candidate ← liftM Generic.sampleMasterSeed
    liftM (Generic.Seeded.keygenFromSeed candidate) : OracleComp OracleWorld _)).run _)
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
  refine ⟨(seed, Seeded.signingDerivationCache seed parameterOutput outputs randomizers), ?_, ?_⟩
  · rw [romImpl, QueryImpl.simulateQ_add_liftM_left, unifFwdImpl.simulateQ_run, support_map]
    refine ⟨seed, ?_, rfl⟩
    rw [mem_support_iff]
    unfold Generic.sampleMasterSeed
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  · rw [romImpl, QueryImpl.simulateQ_add_liftM_right, run_keygenFromSeed_prepared, support_map]
    exact ⟨tree, htree, rfl⟩

theorem exists_prepared_tree_of_independent (seed : MasterSeed)
    (parameterOutput : Digest) (outputs : Seeded.ChainSecrets) (randomizers : Seeded.RandomizerOutputs)
    (tree : (Digest × QueryLog HashSpec) × QueryCache HashSpec)
    (htree : tree ∈ support ((simulateQ randomOracle
      (Generic.Merkle.treeNode (parameterOutput) (outputs)
        treeHeight Generic.Merkle.rootNode : OracleComp HashSpec Digest).withQueryLog).run ∅)) :
    ∃ cache,
      (tree.1, cache) ∈ support ((simulateQ randomOracle
        (Generic.Merkle.treeNode (parameterOutput) (outputs)
          treeHeight Generic.Merkle.rootNode : OracleComp HashSpec Digest).withQueryLog).run
            (Seeded.signingDerivationCache seed parameterOutput outputs randomizers)) ∧
      Seeded.AgreeOutside (fun input => SeedHit input seed) cache tree.2 ∧
      (∀ position, cache (Seeded.randomizerInputs (parameterOutput) seed position) =
        some (randomizers position)) := by
  classical
  have hqueries :
      (Generic.Merkle.treeNode (parameterOutput) (outputs)
        treeHeight Generic.Merkle.rootNode : OracleComp HashSpec Digest).withQueryLog.IsQueryBoundP
          (Seeded.DerivationHit seed) 0 := by
    rw [withQueryLog,
      OracleComp.isQueryBoundP_iff_of_map_eq (QueryImpl.fst_map_run_withLogging _ _),
      simulateQ_ofLift_eq_self]
    exact (Merkle.treeNode_noSeed _ _ _ _).of_imp (fun _ h => h.2)
  obtain ⟨cache, hcache, hagree⟩ := support_transfer_of_no_protected_queries
    (Seeded.DerivationHit seed) _ hqueries _ ∅
    (Seeded.signingDerivationCache_agreeOutside_derivationHit seed parameterOutput outputs randomizers)
    tree htree
  refine ⟨cache, hcache, ?_, ?_⟩
  · intro input hinput
    exact hagree input (fun h => hinput h.1)
  · intro position
    exact (DeterministicSigning.cache_le_of_run _ _ _ hcache)
      (Seeded.signingDerivationCache_randomizer seed parameterOutput outputs randomizers position)

/-- info: 'Xmss.TargetSum.Seeded.exists_prepared_tree_of_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_prepared_tree_of_independent

/-- info: 'Xmss.TargetSum.Seeded.xmss_keygen_prepared_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_keygen_prepared_support

end Xmss.TargetSum.Seeded
