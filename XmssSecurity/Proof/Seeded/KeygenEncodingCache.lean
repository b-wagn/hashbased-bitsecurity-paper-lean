import XmssSecurity.Proof.SignerSuccessBudget
import XmssSecurity.Proof.Seeded.KeygenExpansion

/-! Seed derivation and tree generation leave every encoding input fresh. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity

attribute [local irreducible] sampleMasterSeed

theorem Seeded.derivationCache_encodingInput_none (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : ChainOutputs) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (payload : Message × Randomness) :
    derivationCache seed parameterOutput outputs
      (Concrete.CacheView.encodingInput parameter leafIndex payload) = none := by
  unfold derivationCache
  rw [cacheRows_apply_of_not_mem]
  · apply QueryCache.cacheQuery_of_ne
    exact (keygenHashInput_ne_tweakableHashInput 0 parameter .parameter
      (.encoding leafIndex) seed _).symm
  · intro candidate chain heq
    exact keygenHashInput_ne_tweakableHashInput (truncateHash parameterOutput) parameter
      (.chain candidate chain) (.encoding leafIndex) seed _ heq.symm

theorem Seeded.keygenFromSeed_cache_none_encodingInput (seed : MasterSeed)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ randomOracle (keygenFromSeed seed)).run ∅))
    (leafIndex : LeafIndex) (payload : Message × Randomness) :
    keyResult.2 (Concrete.CacheView.encodingInput keyResult.1.2.precomputed.parameter
      leafIndex payload) = none := by
  unfold keygenFromSeed at hkey
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hkey
  obtain ⟨⟨parameter, parameterCache⟩, hparameter, hrest⟩ := hkey
  rw [run_deriveParameter, support_map] at hparameter
  obtain ⟨parameterOutput, _, hparameter⟩ := hparameter
  cases hparameter
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨secret, secretCache⟩, hsecret, hrest⟩ := hrest
  change (secret, secretCache) ∈ support ((simulateQ randomOracle
    (deriveChainSecrets (truncateHash parameterOutput) seed)).run
      (Seeded.parameterCache seed parameterOutput)) at hsecret
  rw [run_deriveChainSecrets, support_map] at hsecret
  obtain ⟨outputs, _, hsecret⟩ := hsecret
  cases hsecret
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨treeResult, rootCache⟩, htree, hout⟩ := hrest
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
  subst keyResult
  apply Concrete.CacheReplay.cache_none_of_zero_query_bound
    (Concrete.treeNode (truncateHash parameterOutput) (outputSecrets outputs)
      treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog
    (Concrete.CacheView.encodingInput (truncateHash parameterOutput) leafIndex payload)
    (derivationCache seed parameterOutput outputs) rootCache treeResult
  · rw [withQueryLog,
      OracleComp.isQueryBoundP_iff_of_map_eq (QueryImpl.fst_map_run_withLogging _ _),
      simulateQ_ofLift_eq_self]
    exact (Concrete.treeNode_queryBound_zero_encodingAddress (truncateHash parameterOutput)
      (outputSecrets outputs) leafIndex treeHeight Concrete.rootNode).of_imp (by
        intro input hinput
        subst input
        rw [Concrete.CacheView.encodingInput]
        exact (atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl)
  · exact derivationCache_encodingInput_none _ _ _ _ _ _
  · dsimp only at htree
    exact htree

theorem xmss_keygen_cache_none_encodingInput
    (keyResult : (PublicKey × Seeded.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl xmss.keygen).run ∅))
    (leafIndex : LeafIndex) (payload : Message × Randomness) :
    keyResult.2 (Concrete.CacheView.encodingInput keyResult.1.2.precomputed.parameter
      leafIndex payload) = none := by
  change keyResult ∈ support ((simulateQ romImpl (do
    let seed ← liftM sampleMasterSeed
    liftM (Seeded.keygenFromSeed seed) : OracleComp OracleWorld _)).run ∅) at hkey
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hkey
  obtain ⟨⟨seed, cache⟩, hseed, hkey⟩ := hkey
  have hcache : cache = ∅ := xmssRom_lift_probComp_cache_eq sampleMasterSeed ∅ (seed, cache) hseed
  subst cache
  rw [romImpl, QueryImpl.simulateQ_add_liftM_right] at hkey
  exact Seeded.keygenFromSeed_cache_none_encodingInput seed keyResult hkey leafIndex payload

theorem xmss_keygen_no_acceptedEncoding
    (keyResult : (PublicKey × Seeded.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl xmss.keygen).run ∅)) :
    ¬HasAcceptedEncoding keyResult.1.2.precomputed.parameter keyResult.2 :=
  not_hasAcceptedEncoding_of_no_encodingInputs _ _
    (xmss_keygen_cache_none_encodingInput keyResult hkey)

/-- The half-cost signing bound applies after every supported execution of the actual
seeded key generator, with no cache premise left to discharge. -/
theorem xmss_sign_afterKeygen_success_le_half_expectedHashQueries
    (keyResult : (PublicKey × Seeded.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl xmss.keygen).run ∅))
    (leafIndex : LeafIndex) (message : Message) :
    Pr[fun result : Option Signature × QueryCache HashSpec => result.1 ≠ none |
      (simulateQ romImpl (xmss.sign keyResult.1.2 leafIndex message)).run keyResult.2] ≤
      (Checksum.acceptanceProbability / 2) * expectedSimulatedQueryCount romImpl IsHashQuery
        (xmss.sign keyResult.1.2 leafIndex message) keyResult.2 :=
  xmss_sign_success_le_half_expectedHashQueries _ _ _ _ (xmss_keygen_no_acceptedEncoding keyResult hkey)

/-- info: 'XmssSecurity.xmss_keygen_no_acceptedEncoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_keygen_no_acceptedEncoding

/-- info: 'XmssSecurity.xmss_sign_afterKeygen_success_le_half_expectedHashQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms xmss_sign_afterKeygen_success_le_half_expectedHashQueries

end XmssSecurity
