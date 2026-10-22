import Xmss.Proof.TargetSum.Modes.SignerPrepared
import Xmss.Proof.TargetSum.Deterministic.PreparedKeygen
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Transfer the statement's signer-counted budget to the independent reference phase,
charging each direct hash once and each reference signing attempt twice. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Modes
open Xmss.Modes

open Seeded DeterministicSigning

attribute [local irreducible] Generic.sampleMasterSeed Seeded.signingDerivationCache prepareSigningMaterial

theorem signer_tablePhaseCostBound_after_independent_tree
    (adversary : AdversaryBridge.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q)
    (parameterOutput : Digest) (outputs : Seeded.ChainSecrets) (randomizers : Seeded.RandomizerOutputs)
    (tree : (Digest × QueryLog HashSpec) × QueryCache HashSpec)
    (htree : tree ∈ support ((simulateQ randomOracle
      (Generic.Merkle.treeNode (parameterOutput) (outputs)
        treeHeight Generic.Merkle.rootNode : OracleComp HashSpec Digest).withQueryLog).run ∅)) :
    TablePhaseCostBound randomizers
      (Generic.Keygen.precomputedSecretKey (parameterOutput) (outputs)
        (Generic.hashCacheOfLog tree.1.2))
      (DeterministicSigning.withRequestLog (adversary.main ⟨tree.1.1, parameterOutput⟩)) tree.2 q := by
  classical
  let caches : MasterSeed → QueryCache HashSpec := fun seed =>
    Classical.choose (exists_prepared_tree_of_independent seed parameterOutput outputs randomizers
      tree htree)
  have hcaches (seed : MasterSeed) := Classical.choose_spec
    (exists_prepared_tree_of_independent seed parameterOutput outputs randomizers tree htree)
  apply tablePhaseCostBound_of_seed_caches randomizers _ _ q [] caches tree.2
    (by simpa using hsmall)
  · intro seed _
    exact (hcaches seed).2.1
  · intro seed _
    have hprepared : (randomizers, Seeded.signingDerivationCache seed parameterOutput outputs randomizers) ∈
        support ((simulateQ romImpl
          (liftM (prepareSigningMaterial seed) : OracleComp OracleWorld Seeded.RandomizerOutputs)).run ∅) := by
      rw [romImpl, QueryImpl.simulateQ_add_liftM_right]
      exact prepareSigningMaterial_support seed parameterOutput outputs randomizers
    have hkey := xmss_keygen_prepared_support seed parameterOutput outputs randomizers
      (tree.1, caches seed) (hcaches seed).1
    have hphase := signer_adversaryPhase_hashQueryBound_after_initial_preparation
      adversary q hbound (liftM (prepareSigningMaterial seed))
      (randomizers, Seeded.signingDerivationCache seed parameterOutput outputs randomizers) hprepared
      _ _ _ hkey
    rw [signer_phase_eq_runSigning] at hphase
    exact fun result hresult => tablePhaseCost_le_of_hashQueryBound seed
      (Generic.Keygen.precomputedSecretKey (parameterOutput) (outputs)
        (Generic.hashCacheOfLog tree.1.2)) randomizers
      (DeterministicSigning.withRequestLog (adversary.main ⟨tree.1.1, parameterOutput⟩))
      (caches seed) (hcaches seed).2.2 q hphase result hresult

theorem signer_referencePhaseCost_le_after_independent_tree
    (adversary : AdversaryBridge.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q)
    (parameterOutput : Digest) (outputs : Seeded.ChainSecrets)
    (tree : (Digest × QueryLog HashSpec) × QueryCache HashSpec)
    (htree : tree ∈ support ((simulateQ randomOracle
      (Generic.Merkle.treeNode (parameterOutput) (outputs)
        treeHeight Generic.Merkle.rootNode : OracleComp HashSpec Digest).withQueryLog).run ∅))
    (result : (Forgery × QueryLog SigningSpec) × Seeded.CostState)
    (hresult : result ∈ support ((simulateQ
      (referencePhaseCostImpl (Generic.Keygen.precomputedSecretKey (parameterOutput)
        (outputs) (Generic.hashCacheOfLog tree.1.2)))
      (DeterministicSigning.withRequestLog (DeterministicSigning.memoize
        (adversary.main ⟨tree.1.1, parameterOutput⟩) ∅))).run (tree.2, 0))) :
    result.2.2 ≤ q := by
  apply referencePhaseCost_logged_memo_le_of_table _ _ tree.2 q _ result hresult
  intro randomizers
  exact signer_tablePhaseCostBound_after_independent_tree adversary q hsmall hbound
    parameterOutput outputs randomizers tree htree

theorem signer_referencePhaseCost_le_after_tree
    (adversary : AdversaryBridge.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q)
    (parameter : PublicParameter) (secret : Seeded.ChainSecrets)
    (tree : (Digest × QueryLog HashSpec) × QueryCache HashSpec)
    (htree : tree ∈ support ((simulateQ randomOracle
      (Generic.Merkle.treeNode parameter secret treeHeight Generic.Merkle.rootNode :
        OracleComp HashSpec Digest).withQueryLog).run ∅))
    (result : (Forgery × QueryLog SigningSpec) × Seeded.CostState)
    (hresult : result ∈ support ((simulateQ
      (referencePhaseCostImpl (Generic.Keygen.precomputedSecretKey parameter secret
        (Generic.hashCacheOfLog tree.1.2)))
      (DeterministicSigning.withRequestLog (DeterministicSigning.memoize (adversary.main ⟨tree.1.1, parameter⟩) ∅))).run (tree.2, 0))) :
    result.2.2 ≤ q := by
  refine signer_referencePhaseCost_le_after_independent_tree adversary q hsmall hbound
    parameter secret tree htree result hresult

/-- The statement's budget bounds every supported reference adversary phase after ordinary
independent key generation. No programmed-cache or randomizer premise remains. -/
theorem signer_referencePhaseCost_le_after_keygen
    (adversary : AdversaryBridge.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q)
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅))
    (result : (Forgery × QueryLog SigningSpec) × Seeded.CostState)
    (hresult : result ∈ support ((simulateQ (referencePhaseCostImpl keyResult.1.2)
      (DeterministicSigning.withRequestLog (DeterministicSigning.memoize (adversary.main keyResult.1.1) ∅))).run (keyResult.2, 0))) :
    result.2.2 ≤ q := by
  change keyResult ∈ support ((simulateQ romImpl Keygen.precomputedKeygen).run ∅) at hkey
  unfold Keygen.precomputedKeygen at hkey
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hkey
  obtain ⟨⟨parameter, parameterCache⟩, hparameter, hrest⟩ := hkey
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨secret, secretCache⟩, hsecret, hrest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨treeResult, rootCache⟩, htree, hout⟩ := hrest
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hout
  subst keyResult
  have hparameterCache : parameterCache = ∅ := xmssRom_lift_probComp_cache_eq Keygen.samplePublicParameter ∅
    (parameter, parameterCache) hparameter
  have hsecretCache : secretCache = ∅ :=
    (xmssRom_lift_probComp_cache_eq Keygen.sampleSecret parameterCache
      (secret, secretCache) hsecret).trans hparameterCache
  dsimp only at htree
  rw [hsecretCache, romImpl, QueryImpl.simulateQ_add_liftM_right] at htree
  exact signer_referencePhaseCost_le_after_tree adversary q hsmall hbound parameter secret
    (treeResult, rootCache) htree result hresult

/-- info: 'Xmss.TargetSum.Modes.signer_referencePhaseCost_le_after_independent_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_referencePhaseCost_le_after_independent_tree

/-- info: 'Xmss.TargetSum.Modes.signer_referencePhaseCost_le_after_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_referencePhaseCost_le_after_keygen

end Xmss.TargetSum.Modes
