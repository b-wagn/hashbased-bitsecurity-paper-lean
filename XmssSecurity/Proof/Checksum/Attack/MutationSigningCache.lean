import XmssSecurity.Proof.Checksum.Attack.MutationProbability

/-! Signing only adds encoding inputs, preserving the cache on the mutation path. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum

namespace Concrete

theorem precomputedSignBoundedAttempts_preserves_unqueriedInput
    (attempts : ℕ) (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (target : HashInput)
    (hother : ∀ randomness, CacheView.encodingInput secretKey.parameter leafIndex
      (message, randomness) ≠ target)
    (initialCache finalCache : QueryCache HashSpec) (result : Option Signature)
    (hmem : (result, finalCache) ∈ support ((simulateQ romImpl
      (precomputedSignBoundedAttempts attempts secretKey leafIndex message)).run initialCache)) :
    finalCache target = initialCache target := by
  induction attempts generalizing initialCache finalCache result with
  | zero =>
      simp only [precomputedSignBoundedAttempts, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact congrArg (fun cache : QueryCache HashSpec => cache target) hmem.2
  | succ attempts ih =>
      rw [precomputedSignBoundedAttempts_run_succ_eq, mem_support_bind_iff] at hmem
      obtain ⟨randomness, _, hrest⟩ := hmem
      rw [mem_support_bind_iff] at hrest
      obtain ⟨⟨attemptResult, attemptCache⟩, hattempt, hcontinue⟩ := hrest
      have heq : attemptCache target = initialCache target := by
        cases hcached : initialCache target with
        | none =>
            apply CacheReplay.cache_none_of_zero_query_bound
              (precomputedSignAttempt secretKey leafIndex message randomness :
                OracleComp HashSpec (Option Signature)) target initialCache attemptCache attemptResult
              ?_ hcached hattempt
            rw [precomputedSignAttempt]
            refine OracleComp.isQueryBoundP_bind (m := 0)
              (encodingHash_queryBound_zero_at_other_input _ _ _ _ target (hother randomness)) ?_
            intro digest _
            split <;> simp
        | some output =>
            exact CacheReplay.randomOracle_cache_le _ initialCache (attemptResult, attemptCache) hattempt hcached
      unfold precomputedSignBoundedAttemptsContinuation at hcontinue
      cases attemptResult with
      | none => exact (ih attemptCache finalCache result hcontinue).trans heq
      | some signature =>
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hcontinue
          exact (congrArg (fun cache : QueryCache HashSpec => cache target) hcontinue.2).trans heq

end Concrete

namespace Attack

open Concrete

theorem mutationPathInput_ne_encodingInput
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (digit : Digit) (signature : Signature) (endpoints : ChainIndex → Digest)
    (position : ℕ) (hposition : position < mutationChainSteps digit + 1 + treeHeight)
    (value : Digest) (signingLeaf : LeafIndex) (message : Message) (randomness : Randomness) :
    CacheView.encodingInput parameter signingLeaf (message, randomness) ≠
      mutationPathInput parameter leafIndex chain digit signature endpoints position value := by
  intro heq
  unfold mutationPathInput at heq
  split_ifs at heq
  all_goals try omega
  all_goals
    have hdomain := domain_eq_of_tweakableHashInput_eq parameter heq
    contradiction

theorem mutationReplayInputs_preserved_by_signing
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (leafIndex : LeafIndex)
    (chain : ChainIndex) (encoding : Encoding) (randomness : Randomness)
    (signingLeaf : LeafIndex) (message : Message) (result : Option Signature)
    (finalCache : QueryCache HashSpec)
    (hsign : (result, finalCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign secretKey signingLeaf message)).run cache))
    (position : ℕ) (hposition : position < mutationChainSteps (encoding chain) + 1 + treeHeight)
    (value : Digest) :
    finalCache (mutationReplayInputs cache secretKey leafIndex chain encoding randomness position value) =
      cache (mutationReplayInputs cache secretKey leafIndex chain encoding randomness position value) := by
  rw [precomputedCappedSign] at hsign
  exact precomputedSignBoundedAttempts_preserves_unqueriedInput signingAttemptLimit secretKey
    signingLeaf message _
    (fun signingRandomness => mutationPathInput_ne_encodingInput _ _ _ _ _ _ _ hposition value
      signingLeaf message signingRandomness) cache finalCache result hsign

theorem mutationReplayPath_probability_after_signing
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (encoding : Encoding) (randomness : Randomness)
    (signingLeaf : LeafIndex) (message : Message) (result : Option Signature)
    (finalCache : QueryCache HashSpec)
    (hsign : (result, finalCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign keyResult.1.2 signingLeaf message)).run keyResult.2)) :
    Pr[fun outcome => outcome.1 ≠
        (CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness encoding).chainValue chain ∧
        outcome.2.1 = keyResult.1.1.root |
      Rom.randomHashPath
        (mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding randomness)
        0 (40 - (encoding chain).val) finalCache] =
      pathMutationProbability (40 - (encoding chain).val) := by
  have hagree := mutationReplayInputs_preserved_by_signing keyResult.2 keyResult.1.2 leafIndex
    chain encoding randomness signingLeaf message result finalCache hsign
  have h := Rom.randomHashPath_distinct_hit_probability
    (mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding randomness)
    (mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain (encoding chain))
    0 (mutationChainSteps (encoding chain) + 1 + treeHeight) finalCache
    (by
      intro i _ hi j _ hj hne left right
      exact mutationPathInput_separate _ _ _ _ _ _ i j (by omega) (by omega) hne left right)
    (by
      intro i _ hi
      rw [hagree i (by omega)]
      exact mutationReplayInputs_honest keyResult hkey leafIndex chain encoding randomness i (by omega))
    (by
      intro i _ hi other hother
      rw [hagree i (by omega)]
      exact mutationReplayInputs_fresh keyResult hkey leafIndex chain encoding randomness i
        (by omega) other hother)
  simp only [Nat.zero_add] at h
  rw [mutationHonestValue_start _ _ _ _ _ randomness,
    mutationHonestValue_root keyResult hkey] at h
  simpa only [mutationPath_length, pathMutationProbability] using h

theorem signing_success_replay_at_keygen
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) (signature : Signature) (finalCache : QueryCache HashSpec)
    (hsign : (some signature, finalCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2)) :
    ∃ encoding,
      CacheView.decodedEncoding finalCache keyResult.1.2.parameter
        request.epoch (request.message, signature.randomness) = some encoding ∧
      signature = CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 request.epoch
        signature.randomness encoding := by
  have hle := xmssRom_cache_le _ keyResult.2 (some signature, finalCache) hsign
  have hconsistent := precomputedKeygen_support_consistent keyResult hkey
  obtain ⟨encoding, hdecode, hsignature⟩ := precomputedCappedSign_success_replay keyResult.1.2
    request keyResult.2 keyResult.2 finalCache finalCache signature hconsistent hle hsign le_rfl
  refine ⟨encoding, hdecode, hsignature.trans ?_⟩
  exact (hconsistent finalCache hle request.epoch signature.randomness encoding).symm.trans
    (hconsistent keyResult.2 le_rfl request.epoch signature.randomness encoding)

/-- Execute the concrete modified chain, leaf hash, and authentication path. -/
noncomputable def randomMutationRoot (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (signature : Signature)
    (endpoints : ChainIndex → Digest) (cache : QueryCache HashSpec) :
    ProbComp (Digest × (Digest × QueryCache HashSpec)) := do
  let value ← $ᵗ Digest
  let result ← (simulateQ randomOracle
    (mutationRoot parameter leafIndex chain digit signature endpoints value)).run cache
  return (value, result)

theorem randomMutationRoot_eq_randomHashPath (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (signature : Signature)
    (endpoints : ChainIndex → Digest) (cache : QueryCache HashSpec) :
    randomMutationRoot parameter leafIndex chain digit signature endpoints cache =
      Rom.randomHashPath (mutationPathInput parameter leafIndex chain digit signature endpoints)
        0 (40 - digit.val) cache := by
  unfold randomMutationRoot Rom.randomHashPath
  simp_rw [mutationRoot_eq_hashPath]

theorem mutationRoot_probability_after_successful_signing
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) (signature : Signature) (finalCache : QueryCache HashSpec)
    (hsign : (some signature, finalCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2)) :
    ∃ encoding,
      CacheView.decodedEncoding finalCache keyResult.1.2.parameter
        request.epoch (request.message, signature.randomness) = some encoding ∧
      signature = CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 request.epoch
        signature.randomness encoding ∧
      ∀ chain, Pr[fun outcome => outcome.1 ≠ signature.chainValue chain ∧
        outcome.2.1 = keyResult.1.1.root |
        randomMutationRoot keyResult.1.2.parameter request.epoch chain (encoding chain) signature
          (CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
            keyResult.1.2.chainStart request.epoch) finalCache] =
        pathMutationProbability (40 - (encoding chain).val) := by
  obtain ⟨encoding, hdecode, hsignature⟩ := signing_success_replay_at_keygen keyResult hkey
    request signature finalCache hsign
  refine ⟨encoding, hdecode, hsignature, ?_⟩
  intro chain
  have h := mutationReplayPath_probability_after_signing keyResult hkey request.epoch chain
    encoding signature.randomness request.epoch request.message (some signature) finalCache hsign
  rw [randomMutationRoot_eq_randomHashPath]
  change Pr[fun outcome => outcome.1 ≠ signature.chainValue chain ∧ outcome.2.1 = keyResult.1.1.root |
    Rom.randomHashPath (mutationPathInput keyResult.1.2.parameter request.epoch chain (encoding chain)
      signature (CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
        keyResult.1.2.chainStart request.epoch)) 0 (40 - (encoding chain).val) finalCache] = _
  conv_lhs => rw [hsignature]
  exact h

/-- info: 'XmssSecurity.Checksum.Attack.mutationReplayInputs_preserved_by_signing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mutationReplayInputs_preserved_by_signing

/-- info: 'XmssSecurity.Checksum.Attack.mutationReplayPath_probability_after_signing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mutationReplayPath_probability_after_signing

/-- info: 'XmssSecurity.Checksum.Attack.signing_success_replay_at_keygen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signing_success_replay_at_keygen

/-- info: 'XmssSecurity.Checksum.Attack.mutationRoot_probability_after_successful_signing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mutationRoot_probability_after_successful_signing

end Attack
end XmssSecurity.Checksum
