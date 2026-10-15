import XmssSecurity.Proof.Modes.SignerPrepared
import XmssSecurity.Proof.Deterministic.PreparedKeygen

/-! Transfer the statement's signer-counted budget to the independent reference phase,
charging each direct hash once and each reference signing attempt twice. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Modes

open Seeded DeterministicSigning

attribute [local irreducible] sampleMasterSeed signingDerivationCache prepareSigningMaterial

theorem signer_tablePhaseCostBound_after_independent_tree
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (parameterOutput : HashOutput) (outputs : ChainOutputs) (randomizers : RandomizerOutputs)
    (tree : (Digest × QueryLog HashSpec) × QueryCache HashSpec)
    (htree : tree ∈ support ((simulateQ randomOracle
      (Concrete.treeNode (truncateHash parameterOutput) (outputSecrets outputs)
        treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog).run ∅)) :
    TablePhaseCostBound randomizers
      (Concrete.precomputedSecretKey (truncateHash parameterOutput) (outputSecrets outputs)
        (hashCacheOfLog tree.1.2))
      (withRequestLog (adversary.main ⟨tree.1.1, truncateHash parameterOutput⟩)) tree.2 q := by
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
    have hprepared : (randomizers, signingDerivationCache seed parameterOutput outputs randomizers) ∈
        support ((simulateQ romImpl
          (liftM (prepareSigningMaterial seed) : OracleComp OracleWorld RandomizerOutputs)).run ∅) := by
      rw [romImpl, QueryImpl.simulateQ_add_liftM_right]
      exact prepareSigningMaterial_support seed parameterOutput outputs randomizers
    have hkey := xmss_keygen_prepared_support seed parameterOutput outputs randomizers
      (tree.1, caches seed) (hcaches seed).1
    have hphase := signer_adversaryPhase_hashQueryBound_after_initial_preparation
      adversary q hbound (liftM (prepareSigningMaterial seed))
      (randomizers, signingDerivationCache seed parameterOutput outputs randomizers) hprepared
      _ _ _ hkey
    rw [signer_phase_eq_runSigning] at hphase
    exact fun result hresult => tablePhaseCost_le_of_hashQueryBound seed
      (Concrete.precomputedSecretKey (truncateHash parameterOutput) (outputSecrets outputs)
        (hashCacheOfLog tree.1.2)) randomizers
      (withRequestLog (adversary.main ⟨tree.1.1, truncateHash parameterOutput⟩))
      (caches seed) (hcaches seed).2.2 q hphase result hresult

theorem signer_referencePhaseCost_le_after_independent_tree
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (parameterOutput : HashOutput) (outputs : ChainOutputs)
    (tree : (Digest × QueryLog HashSpec) × QueryCache HashSpec)
    (htree : tree ∈ support ((simulateQ randomOracle
      (Concrete.treeNode (truncateHash parameterOutput) (outputSecrets outputs)
        treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog).run ∅))
    (result : (Forgery × QueryLog SigningSpec) × CostState)
    (hresult : result ∈ support ((simulateQ
      (referencePhaseCostImpl (Concrete.precomputedSecretKey (truncateHash parameterOutput)
        (outputSecrets outputs) (hashCacheOfLog tree.1.2)))
      (withRequestLog (memoize
        (adversary.main ⟨tree.1.1, truncateHash parameterOutput⟩) ∅))).run (tree.2, 0))) :
    result.2.2 ≤ q := by
  apply referencePhaseCost_logged_memo_le_of_table _ _ tree.2 q _ result hresult
  intro randomizers
  exact signer_tablePhaseCostBound_after_independent_tree adversary q hsmall hbound
    parameterOutput outputs randomizers tree htree

theorem signer_referencePhaseCost_le_after_tree
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (parameter : PublicParameter) (secret : ChainSecrets)
    (tree : (Digest × QueryLog HashSpec) × QueryCache HashSpec)
    (htree : tree ∈ support ((simulateQ randomOracle
      (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
        OracleComp HashSpec Digest).withQueryLog).run ∅))
    (result : (Forgery × QueryLog SigningSpec) × CostState)
    (hresult : result ∈ support ((simulateQ
      (referencePhaseCostImpl (Concrete.precomputedSecretKey parameter secret
        (hashCacheOfLog tree.1.2)))
      (withRequestLog (memoize (adversary.main ⟨tree.1.1, parameter⟩) ∅))).run (tree.2, 0))) :
    result.2.2 ≤ q := by
  refine signer_referencePhaseCost_le_after_independent_tree adversary q hsmall hbound
    (Rom.hashOutputEquivDigestPair.symm (0, parameter))
    (chainOutputHalves.symm ((fun _ _ => 0), secret)) tree ?_ result ?_
  · simpa only [truncate_from_halves, outputSecrets_from_halves] using htree
  · simpa only [truncate_from_halves, outputSecrets_from_halves] using hresult

/-- The statement's budget bounds every supported reference adversary phase after ordinary
independent key generation. No programmed-cache or randomizer premise remains. -/
theorem signer_referencePhaseCost_le_after_keygen
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (keyResult : (PublicKey × XmssSecurity.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (result : (Forgery × QueryLog SigningSpec) × CostState)
    (hresult : result ∈ support ((simulateQ (referencePhaseCostImpl keyResult.1.2)
      (withRequestLog (memoize (adversary.main keyResult.1.1) ∅))).run (keyResult.2, 0))) :
    result.2.2 ≤ q := by
  change keyResult ∈ support ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) at hkey
  unfold Concrete.precomputedKeygen at hkey
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hkey
  obtain ⟨⟨parameter, parameterCache⟩, hparameter, hrest⟩ := hkey
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨secret, secretCache⟩, hsecret, hrest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨treeResult, rootCache⟩, htree, hout⟩ := hrest
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hout
  subst keyResult
  have hparameterCache : parameterCache = ∅ := xmssRom_lift_probComp_cache_eq Concrete.samplePublicParameter ∅
    (parameter, parameterCache) hparameter
  have hsecretCache : secretCache = ∅ :=
    (xmssRom_lift_probComp_cache_eq Concrete.sampleSecret parameterCache
      (secret, secretCache) hsecret).trans hparameterCache
  dsimp only at htree
  rw [hsecretCache, romImpl, QueryImpl.simulateQ_add_liftM_right] at htree
  exact signer_referencePhaseCost_le_after_tree adversary q hsmall hbound parameter secret
    (treeResult, rootCache) htree result hresult

theorem signer_expected_referencePhaseCost_le_after_keygen
    (adversary : Security.StatementAdversary) (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound xmss adversary q)
    (keyResult : (PublicKey × XmssSecurity.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    (∑' result, Pr[= result | (simulateQ (referencePhaseCostImpl keyResult.1.2)
      (withRequestLog (memoize (adversary.main keyResult.1.1) ∅))).run (keyResult.2, 0)] *
        (result.2.2 : ℝ≥0∞)) ≤ q := by
  let phase := (simulateQ (referencePhaseCostImpl keyResult.1.2)
    (withRequestLog (memoize (adversary.main keyResult.1.1) ∅))).run (keyResult.2, 0)
  calc
    _ ≤ ∑' result, Pr[= result | phase] * (q : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro result
      change Pr[= result | phase] * (result.2.2 : ℝ≥0∞) ≤ Pr[= result | phase] * (q : ℝ≥0∞)
      by_cases hzero : Pr[= result | phase] = 0
      · simp only [hzero, zero_mul, le_refl]
      · apply mul_le_mul' le_rfl
        exact_mod_cast signer_referencePhaseCost_le_after_keygen adversary q hsmall hbound
          keyResult hkey result (by rwa [mem_support_iff])
    _ = q := by
      rw [ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]

/-- info: 'XmssSecurity.Modes.signer_referencePhaseCost_le_after_independent_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_referencePhaseCost_le_after_independent_tree

/-- info: 'XmssSecurity.Modes.signer_referencePhaseCost_le_after_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_referencePhaseCost_le_after_keygen

/-- info: 'XmssSecurity.Modes.signer_expected_referencePhaseCost_le_after_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_expected_referencePhaseCost_le_after_keygen

end XmssSecurity.Modes
