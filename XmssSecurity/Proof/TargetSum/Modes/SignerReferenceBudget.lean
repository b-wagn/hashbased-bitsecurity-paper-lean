import XmssSecurity.Proof.TargetSum.Modes.SignerPrepared
import XmssSecurity.Proof.TargetSum.Deterministic.PreparedKeygen
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Transfer the statement's signer-counted budget to the independent reference phase,
charging each direct hash once and each reference signing attempt twice. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Modes
open XmssSecurity.Modes

open Seeded Generic.DeterministicSigning

attribute [local irreducible] Generic.sampleMasterSeed Generic.Seeded.signingDerivationCache prepareSigningMaterial

theorem signer_tablePhaseCostBound_after_independent_tree
    (adversary : Generic.Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q)
    (parameterOutput : HashOutput) (outputs : Generic.Seeded.ChainOutputs) (randomizers : Generic.Seeded.RandomizerOutputs)
    (tree : (Digest × QueryLog HashSpec) × QueryCache HashSpec)
    (htree : tree ∈ support ((simulateQ randomOracle
      (Generic.Concrete.treeNode (Generic.truncateHash parameterOutput) (Generic.Seeded.outputSecrets outputs)
        treeHeight Generic.Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog).run ∅)) :
    TablePhaseCostBound randomizers
      (Generic.Concrete.precomputedSecretKey (Generic.truncateHash parameterOutput) (Generic.Seeded.outputSecrets outputs)
        (Generic.hashCacheOfLog tree.1.2))
      (Generic.DeterministicSigning.withRequestLog (adversary.main ⟨tree.1.1, Generic.truncateHash parameterOutput⟩)) tree.2 q := by
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
    have hprepared : (randomizers, Generic.Seeded.signingDerivationCache seed parameterOutput outputs randomizers) ∈
        support ((simulateQ Generic.romImpl
          (liftM (prepareSigningMaterial seed) : OracleComp OracleWorld Generic.Seeded.RandomizerOutputs)).run ∅) := by
      rw [Generic.romImpl, QueryImpl.simulateQ_add_liftM_right]
      exact prepareSigningMaterial_support seed parameterOutput outputs randomizers
    have hkey := xmss_keygen_prepared_support seed parameterOutput outputs randomizers
      (tree.1, caches seed) (hcaches seed).1
    have hphase := signer_adversaryPhase_hashQueryBound_after_initial_preparation
      adversary q hbound (liftM (prepareSigningMaterial seed))
      (randomizers, Generic.Seeded.signingDerivationCache seed parameterOutput outputs randomizers) hprepared
      _ _ _ hkey
    rw [signer_phase_eq_runSigning] at hphase
    exact fun result hresult => tablePhaseCost_le_of_hashQueryBound seed
      (Generic.Concrete.precomputedSecretKey (Generic.truncateHash parameterOutput) (Generic.Seeded.outputSecrets outputs)
        (Generic.hashCacheOfLog tree.1.2)) randomizers
      (Generic.DeterministicSigning.withRequestLog (adversary.main ⟨tree.1.1, Generic.truncateHash parameterOutput⟩))
      (caches seed) (hcaches seed).2.2 q hphase result hresult

theorem signer_referencePhaseCost_le_after_independent_tree
    (adversary : Generic.Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q)
    (parameterOutput : HashOutput) (outputs : Generic.Seeded.ChainOutputs)
    (tree : (Digest × QueryLog HashSpec) × QueryCache HashSpec)
    (htree : tree ∈ support ((simulateQ randomOracle
      (Generic.Concrete.treeNode (Generic.truncateHash parameterOutput) (Generic.Seeded.outputSecrets outputs)
        treeHeight Generic.Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog).run ∅))
    (result : (Generic.Forgery × QueryLog Generic.SigningSpec) × Generic.Seeded.CostState)
    (hresult : result ∈ support ((simulateQ
      (referencePhaseCostImpl (Generic.Concrete.precomputedSecretKey (Generic.truncateHash parameterOutput)
        (Generic.Seeded.outputSecrets outputs) (Generic.hashCacheOfLog tree.1.2)))
      (Generic.DeterministicSigning.withRequestLog (Generic.DeterministicSigning.memoize
        (adversary.main ⟨tree.1.1, Generic.truncateHash parameterOutput⟩) ∅))).run (tree.2, 0))) :
    result.2.2 ≤ q := by
  apply referencePhaseCost_logged_memo_le_of_table _ _ tree.2 q _ result hresult
  intro randomizers
  exact signer_tablePhaseCostBound_after_independent_tree adversary q hsmall hbound
    parameterOutput outputs randomizers tree htree

theorem signer_referencePhaseCost_le_after_tree
    (adversary : Generic.Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q)
    (parameter : PublicParameter) (secret : Generic.Seeded.ChainSecrets)
    (tree : (Digest × QueryLog HashSpec) × QueryCache HashSpec)
    (htree : tree ∈ support ((simulateQ randomOracle
      (Generic.Concrete.treeNode parameter secret treeHeight Generic.Concrete.rootNode :
        OracleComp HashSpec Digest).withQueryLog).run ∅))
    (result : (Generic.Forgery × QueryLog Generic.SigningSpec) × Generic.Seeded.CostState)
    (hresult : result ∈ support ((simulateQ
      (referencePhaseCostImpl (Generic.Concrete.precomputedSecretKey parameter secret
        (Generic.hashCacheOfLog tree.1.2)))
      (Generic.DeterministicSigning.withRequestLog (Generic.DeterministicSigning.memoize (adversary.main ⟨tree.1.1, parameter⟩) ∅))).run (tree.2, 0))) :
    result.2.2 ≤ q := by
  refine signer_referencePhaseCost_le_after_independent_tree adversary q hsmall hbound
    (Generic.Rom.hashOutputEquivDigestPair.symm (0, parameter))
    (Generic.Seeded.chainOutputHalves.symm ((fun _ _ => 0), secret)) tree ?_ result ?_
  · simpa only [Generic.Seeded.truncate_from_halves, Generic.Seeded.outputSecrets_from_halves] using htree
  · simpa only [Generic.Seeded.truncate_from_halves, Generic.Seeded.outputSecrets_from_halves] using hresult

/-- The statement's budget bounds every supported reference adversary phase after ordinary
independent key generation. No programmed-cache or randomizer premise remains. -/
theorem signer_referencePhaseCost_le_after_keygen
    (adversary : Generic.Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q)
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅))
    (result : (Generic.Forgery × QueryLog Generic.SigningSpec) × Generic.Seeded.CostState)
    (hresult : result ∈ support ((simulateQ (referencePhaseCostImpl keyResult.1.2)
      (Generic.DeterministicSigning.withRequestLog (Generic.DeterministicSigning.memoize (adversary.main keyResult.1.1) ∅))).run (keyResult.2, 0))) :
    result.2.2 ≤ q := by
  change keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.precomputedKeygen).run ∅) at hkey
  unfold Generic.Concrete.precomputedKeygen at hkey
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hkey
  obtain ⟨⟨parameter, parameterCache⟩, hparameter, hrest⟩ := hkey
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨secret, secretCache⟩, hsecret, hrest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨treeResult, rootCache⟩, htree, hout⟩ := hrest
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hout
  subst keyResult
  have hparameterCache : parameterCache = ∅ := Generic.xmssRom_lift_probComp_cache_eq Generic.Concrete.samplePublicParameter ∅
    (parameter, parameterCache) hparameter
  have hsecretCache : secretCache = ∅ :=
    (Generic.xmssRom_lift_probComp_cache_eq Generic.Concrete.sampleSecret parameterCache
      (secret, secretCache) hsecret).trans hparameterCache
  dsimp only at htree
  rw [hsecretCache, Generic.romImpl, QueryImpl.simulateQ_add_liftM_right] at htree
  exact signer_referencePhaseCost_le_after_tree adversary q hsmall hbound parameter secret
    (treeResult, rootCache) htree result hresult

/-- info: 'XmssSecurity.TargetSum.Modes.signer_referencePhaseCost_le_after_independent_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_referencePhaseCost_le_after_independent_tree

/-- info: 'XmssSecurity.TargetSum.Modes.signer_referencePhaseCost_le_after_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_referencePhaseCost_le_after_keygen

end XmssSecurity.TargetSum.Modes
