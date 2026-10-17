import XmssSecurity.Proof.Checksum.Attack.MutationSigningCache
import XmssSecurity.Proof.Checksum.CappedChain.CausalSigningKeygenCoupling
import XmssSecurity.Proof.Checksum.Direct.DecidingSecondLane

/-! Removing the cached, unchanged chains from the concrete verification computation. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.Attack

open Concrete

theorem simulate_sequenceFin_single_uncached {α : Type} {n : ℕ}
    (computation : Fin n → OracleComp HashSpec α) (selected : Fin n) (values : Fin n → α)
    (baseCache cache : QueryCache HashSpec) (hle : baseCache ≤ cache)
    (hother : ∀ index, index ≠ selected → ∀ largerCache, baseCache ≤ largerCache →
      (simulateQ randomOracle (computation index)).run largerCache = pure (values index, largerCache)) :
    (simulateQ randomOracle (sequenceFin computation)).run cache =
      (fun result => (Function.update values selected result.1, result.2)) <$>
        (simulateQ randomOracle (computation selected)).run cache := by
  classical
  induction n generalizing cache with
  | zero => exact Fin.elim0 selected
  | succ n ih =>
      cases selected using Fin.cases with
      | zero =>
          rw [sequenceFin, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp]
          apply bind_congr_of_forall_mem_support
          rintro ⟨value, middleCache⟩ hmem
          have hmiddle : baseCache ≤ middleCache :=
            hle.trans (CacheReplay.randomOracle_cache_le _ cache (value, middleCache) hmem)
          rw [simulateQ_bind, StateT.run_bind,
            CappedChain.simulate_sequenceFin_run_eq_pure
              (fun index => computation index.succ) middleCache (fun index => values index.succ)
              (fun index => hother index.succ (Fin.succ_ne_zero _) middleCache hmiddle)]
          simp only [pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
          congr 1
          apply Prod.ext
          · funext index
            cases index using Fin.cases <;> simp
          · rfl
      | succ selected =>
          rw [sequenceFin, simulateQ_bind, StateT.run_bind,
            hother 0 (Fin.succ_ne_zero _).symm cache hle]
          simp only [pure_bind]
          rw [simulateQ_bind, StateT.run_bind,
            ih (fun index => computation index.succ) selected (fun index => values index.succ)
              cache hle (fun index hne largerCache hlarger =>
                hother index.succ (by simpa using hne) largerCache hlarger),
            bind_map_left, map_eq_bind_pure_comp]
          apply bind_congr
          rintro ⟨value, finalCache⟩
          simp only [simulateQ_pure, StateT.run_pure, Function.comp_apply]
          congr 1
          apply Prod.ext
          · funext index
            cases index using Fin.cases <;> simp [Function.update_apply, Ne.symm (Fin.succ_ne_zero selected)]
          · rfl

theorem hashPath_run_honest (inputs : ℕ → Digest → HashInput) (honest : ℕ → Digest)
    (start steps : ℕ) (cache : QueryCache HashSpec)
    (hhonest : ∀ i, start ≤ i → i < start + steps →
      ∃ output, cache (inputs i (honest i)) = some output ∧ truncateHash output = honest (i + 1)) :
    (simulateQ randomOracle (Rom.hashPath inputs start steps (honest start))).run cache =
      pure (honest (start + steps), cache) := by
  induction steps generalizing start with
  | zero => simp [Rom.hashPath]
  | succ steps ih =>
      obtain ⟨output, hcached, hnext⟩ := hhonest start le_rfl (by omega)
      rw [Rom.hashPath_run_succ, QueryImpl.withCaching_run_some _ hcached]
      simp only [pure_bind, hnext]
      rw [ih (start + 1) (fun i hi hiEnd => hhonest i (by omega) (by omega))]
      rw [show start + 1 + steps = start + (steps + 1) by omega]

theorem recoverHonestChain_run_pure
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (encoding : Encoding) (randomness : Randomness)
    (cache : QueryCache HashSpec) (hle : keyResult.2 ≤ cache) :
    (simulateQ randomOracle (recoverChain keyResult.1.2.parameter leafIndex chain (encoding chain)
      ((CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness encoding).chainValue chain) :
        OracleComp HashSpec Digest)).run cache =
      pure (CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
        keyResult.1.2.chainStart leafIndex chain, cache) := by
  have h := hashPath_run_honest
    (mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding randomness)
    (mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain (encoding chain))
    0 (mutationChainSteps (encoding chain)) cache (by
      intro i _ hi
      obtain ⟨output, hcached, hnext⟩ := mutationReplayInputs_honest keyResult hkey leafIndex chain
        encoding randomness i (by omega)
      exact ⟨output, hle hcached, hnext⟩)
  unfold mutationReplayInputs at h
  rw [mutationPath_chain _ _ _ _ _ _ _ le_rfl, Nat.zero_add,
    mutationHonestValue_start _ _ _ _ _ randomness, mutationHonestValue_endpoint] at h
  exact h

theorem recoverMutatedEndpoints_run
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (encoding : Encoding) (randomness : Randomness)
    (value : Digest) (cache : QueryCache HashSpec) (hle : keyResult.2 ≤ cache) :
    (simulateQ randomOracle (recoverEndpoints keyResult.1.2.parameter leafIndex encoding
      (CappedChain.replaceSignatureChainValue
        (CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness encoding)
        chain value) : OracleComp HashSpec (ChainIndex → Digest))).run cache =
      (fun result => (Function.update
        (CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart leafIndex) chain result.1, result.2)) <$>
        (simulateQ randomOracle
          (recoverChain keyResult.1.2.parameter leafIndex chain (encoding chain) value :
            OracleComp HashSpec Digest)).run cache := by
  unfold recoverEndpoints
  rw [simulate_sequenceFin_single_uncached _ chain
    (CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
      keyResult.1.2.chainStart leafIndex) keyResult.2 cache hle]
  · simp only [CappedChain.replaceSignatureChainValue_same]
  · intro other hother largerCache hlarger
    rw [CappedChain.replaceSignatureChainValue_other _ _ _ _ hother]
    exact recoverHonestChain_run_pure keyResult hkey leafIndex other encoding randomness
      largerCache hlarger

theorem encodingHash_run_cached (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (message : Message) (randomness : Randomness) (encoding : Encoding)
    (hdecode : CacheView.decodedEncoding cache parameter leafIndex (message, randomness) = some encoding) :
    (simulateQ randomOracle (encodingHash parameter leafIndex message randomness :
      OracleComp HashSpec Digest)).run cache =
      pure (CacheView.encodingHash cache parameter leafIndex (message, randomness), cache) := by
  obtain ⟨output, hcached⟩ := CacheView.encodingInput_cached_of_decode_some cache parameter
    leafIndex message randomness encoding hdecode
  unfold encodingHash tweakableHash oracleHash
  simp only [simulateQ_bind, HasQuery.instOfMonadLift_query, simulateQ_spec_query, StateT.run_bind]
  change (randomOracle (CacheView.encodingInput parameter leafIndex (message, randomness))).run cache >>= _ = _
  rw [QueryImpl.withCaching_run_some _ hcached]
  simp [CacheView.encodingHash, CacheView.digestAt, hcached]

theorem authenticationRoot_replaceSignatureChainValue (parameter : PublicParameter)
    (leafIndex : LeafIndex) (signature : Signature) (chain : ChainIndex) (value : Digest)
    (levels : ℕ) (leaf : Digest) :
    (authenticationRoot parameter leafIndex (CappedChain.replaceSignatureChainValue signature chain value)
      levels leaf : OracleComp HashSpec Digest) =
      authenticationRoot parameter leafIndex signature levels leaf := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      simp only [authenticationRoot, ih]
      rfl

theorem verifyMutatedSignature_run
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (message : Message)
    (encoding : Encoding) (randomness : Randomness) (value : Digest)
    (cache : QueryCache HashSpec) (hle : keyResult.2 ≤ cache)
    (hdecode : CacheView.decodedEncoding cache keyResult.1.2.parameter leafIndex (message, randomness) = some encoding) :
    (simulateQ randomOracle (verify keyResult.1.1 leafIndex message
      (CappedChain.replaceSignatureChainValue
        (CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness encoding)
        chain value) : OracleComp HashSpec Bool)).run cache =
      (fun result => (decide (result.1 = keyResult.1.1.root), result.2)) <$>
        (simulateQ randomOracle (mutationRoot keyResult.1.2.parameter leafIndex chain (encoding chain)
          (CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness encoding)
          (CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
            keyResult.1.2.chainStart leafIndex) value)).run cache := by
  have hparameter := Deciding.keygen_publicKey_parameter_eq keyResult hkey
  rw [verify_eq_decode, simulateQ_bind, StateT.run_bind]
  change (simulateQ randomOracle
      (encodingHash keyResult.1.1.parameter leafIndex message randomness : OracleComp HashSpec Digest)).run cache
    >>= _ = _
  rw [hparameter, encodingHash_run_cached _ _ _ _ _ _ hdecode]
  simp only [pure_bind, CacheView.decodeDigest_of_decodedEncoding hdecode]
  rw [simulateQ_bind, StateT.run_bind,
    recoverMutatedEndpoints_run keyResult hkey leafIndex chain encoding randomness value cache hle,
    bind_map_left]
  unfold mutationRoot
  rw [simulateQ_bind, StateT.run_bind, map_bind]
  apply bind_congr
  rintro ⟨endpoint, middleCache⟩
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind, map_bind]
  apply bind_congr
  rintro ⟨leaf, leafCache⟩
  simp only [verifyAfterLeaf, hparameter, authenticationRoot_replaceSignatureChainValue,
    bind_pure_comp, simulateQ_map, StateT.run_map]

noncomputable def randomMutationVerification (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) (chain : ChainIndex) (cache : QueryCache HashSpec) :
    ProbComp (Digest × (Bool × QueryCache HashSpec)) := do
  let value ← $ᵗ Digest
  let result ← (simulateQ randomOracle (verify publicKey leafIndex message
    (CappedChain.replaceSignatureChainValue signature chain value) : OracleComp HashSpec Bool)).run cache
  return (value, result)

theorem randomMutationVerification_run
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (message : Message)
    (encoding : Encoding) (randomness : Randomness)
    (cache : QueryCache HashSpec) (hle : keyResult.2 ≤ cache)
    (hdecode : CacheView.decodedEncoding cache keyResult.1.2.parameter leafIndex (message, randomness) = some encoding) :
    randomMutationVerification keyResult.1.1 leafIndex message
        (CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness encoding) chain cache =
      (fun result => (result.1, (decide (result.2.1 = keyResult.1.1.root), result.2.2))) <$>
        randomMutationRoot keyResult.1.2.parameter leafIndex chain (encoding chain)
          (CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness encoding)
          (CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
            keyResult.1.2.chainStart leafIndex) cache := by
  unfold randomMutationVerification randomMutationRoot
  rw [map_bind]
  apply bind_congr
  intro value
  rw [verifyMutatedSignature_run keyResult hkey leafIndex chain message encoding randomness value cache hle hdecode]
  simp only [bind_map_left, map_bind, map_pure]

theorem mutationVerification_probability_after_successful_signing
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) (signature : Signature) (finalCache : QueryCache HashSpec)
    (hsign : (some signature, finalCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2)) :
    ∃ encoding,
      CacheView.decodedEncoding finalCache keyResult.1.2.parameter
        request.epoch (request.message, signature.randomness) = some encoding ∧
      ∀ chain, Pr[fun outcome => outcome.1 ≠ signature.chainValue chain ∧ outcome.2.1 = true |
        randomMutationVerification keyResult.1.1 request.epoch request.message signature chain finalCache] =
        pathMutationProbability (40 - (encoding chain).val) := by
  obtain ⟨encoding, hdecode, hsignature, hroot⟩ := mutationRoot_probability_after_successful_signing
    keyResult hkey request signature finalCache hsign
  have hle := xmssRom_cache_le _ keyResult.2 (some signature, finalCache) hsign
  refine ⟨encoding, hdecode, ?_⟩
  intro chain
  have h := hroot chain
  rw [hsignature] at h ⊢
  rw [randomMutationVerification_run keyResult hkey request.epoch chain request.message encoding
    signature.randomness finalCache hle hdecode, probEvent_map]
  simpa only [Function.comp_def, decide_eq_true_eq] using h

/-- info: 'XmssSecurity.Checksum.Attack.verifyMutatedSignature_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verifyMutatedSignature_run

/-- info: 'XmssSecurity.Checksum.Attack.mutationVerification_probability_after_successful_signing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mutationVerification_probability_after_successful_signing

end XmssSecurity.Checksum.Attack
