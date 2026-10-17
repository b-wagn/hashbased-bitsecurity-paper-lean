import XmssSecurity.Proof.Checksum.Attack.NeighborPreimageCache
import XmssSecurity.Proof.Checksum.Attack.MutationVerification

/-! A cached predecessor and one advanced chain value turn a neighboring encoding into
an accepted signature for the new message. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.Attack

open Concrete

theorem hashPath_run_after_first_cached (inputs : ℕ → Digest → HashInput) (honest : ℕ → Digest)
    (start steps : ℕ) (value : Digest) (cache : QueryCache HashSpec)
    (output : HashOutput) (hcached : cache (inputs start value) = some output)
    (htarget : truncateHash output = honest (start + 1))
    (hhonest : ∀ i, start + 1 ≤ i → i < start + 1 + steps →
      ∃ answer, cache (inputs i (honest i)) = some answer ∧ truncateHash answer = honest (i + 1)) :
    (simulateQ randomOracle (Rom.hashPath inputs start (steps + 1) value)).run cache =
      pure (honest (start + (steps + 1)), cache) := by
  rw [Rom.hashPath_run_succ, QueryImpl.withCaching_run_some _ hcached, pure_bind, htarget,
    hashPath_run_honest inputs honest (start + 1) steps cache hhonest]
  rw [show start + 1 + steps = start + (steps + 1) by omega]

theorem mutationRoot_run_after_cached_step
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (chain : ChainIndex) (encoding : Encoding) (randomness : Randomness)
    (cache : QueryCache HashSpec) (hle : keyResult.2 ≤ cache)
    (hstep : (encoding chain).val < chainLength - 1) (value : Digest) (output : HashOutput)
    (hcached : cache (CacheView.chainInput keyResult.1.2.parameter leafIndex chain
      ⟨(encoding chain).val, hstep⟩ value) = some output)
    (htarget : truncateHash output =
      Wots.walk (CacheView.chainStep keyResult.2 keyResult.1.2.parameter leafIndex chain)
        0 ((encoding chain).val + 1) (keyResult.1.2.chainStart leafIndex chain)) :
    (simulateQ randomOracle (mutationRoot keyResult.1.2.parameter leafIndex chain (encoding chain)
      (CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness encoding)
      (CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter keyResult.1.2.chainStart leafIndex)
      value)).run cache = pure (keyResult.1.1.root, cache) := by
  have hpositive : 0 < mutationChainSteps (encoding chain) := by
    unfold mutationChainSteps
    omega
  have hrun := hashPath_run_after_first_cached
    (mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding randomness)
    (mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain (encoding chain))
    0 (mutationChainSteps (encoding chain) + treeHeight) value cache output ?_ ?_ ?_
  · rw [mutationRoot_eq_hashPath, ← mutationPath_length]
    have hlength : mutationChainSteps (encoding chain) + treeHeight + 1 =
        mutationChainSteps (encoding chain) + 1 + treeHeight := by omega
    rw [Nat.zero_add, hlength, mutationHonestValue_root keyResult hkey] at hrun
    exact hrun
  · unfold mutationReplayInputs
    rw [mutationPathInput_chain _ _ _ _ _ _ _ hpositive]
    simpa only [Nat.add_zero] using hcached
  · rw [mutationHonestValue_chain _ _ _ _ _ _ (by omega)]
    exact htarget
  · intro i _ hi
    obtain ⟨answer, hanswer, hnext⟩ := mutationReplayInputs_honest keyResult hkey leafIndex chain
      encoding randomness i (by omega)
    exact ⟨answer, hle hanswer, hnext⟩

def transferredSignature (original : Signature) (randomness : Randomness)
    (encoding : Encoding) (transfer : DigitTransfer encoding) (preimage advanced : Digest) : Signature :=
  ⟨randomness, Function.update (Function.update original.chainValue transfer.1.1 preimage)
    transfer.2.1 advanced, original.authPath⟩

def successorStep (encoding : Encoding) (upper : IncreasingChain encoding) : ChainStep :=
  ⟨(encoding upper.1).val, by have h := upper.2; omega⟩

def advanceSignatureChain (parameter : PublicParameter) (leafIndex : LeafIndex)
    (original : Signature) (encoding : Encoding) (transfer : DigitTransfer encoding) :
    OracleComp HashSpec Digest :=
  chainHash parameter leafIndex transfer.2.1
    (successorStep encoding ⟨transfer.2.1, transfer.2.2.1⟩) (original.chainValue transfer.2.1)

theorem chainHash_run_cached (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (step : ChainStep) (value : Digest) (cache : QueryCache HashSpec)
    (output : HashOutput) (hcached : cache (CacheView.chainInput parameter leafIndex chain step value) = some output) :
    (simulateQ randomOracle (chainHash parameter leafIndex chain step value :
      OracleComp HashSpec Digest)).run cache = pure (truncateHash output, cache) := by
  change (fun result : HashOutput × QueryCache HashSpec => (truncateHash result.1, result.2)) <$>
    (randomOracle (CacheView.chainInput parameter leafIndex chain step value)).run cache = _
  rw [QueryImpl.withCaching_run_some _ hcached, map_pure]

theorem advanceSignatureChain_run
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (original : Signature) (encoding : Encoding)
    (hreplay : original = CacheReplay.signWithEncoding keyResult.2 keyResult.1.2
      leafIndex original.randomness encoding)
    (randomness : Randomness) (transfer : DigitTransfer encoding)
    (cache : QueryCache HashSpec) (hle : keyResult.2 ≤ cache) :
    (simulateQ randomOracle (advanceSignatureChain keyResult.1.2.parameter leafIndex original encoding transfer)).run cache =
      pure ((CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness
        (transferEncoding encoding transfer)).chainValue transfer.2.1, cache) := by
  obtain ⟨output, hcached⟩ := precomputedKeygen_cache_has_chainInput keyResult hkey leafIndex transfer.2.1
    (successorStep encoding ⟨transfer.2.1, transfer.2.2.1⟩)
  have hvalue : original.chainValue transfer.2.1 =
      Wots.walk (CacheView.chainStep keyResult.2 keyResult.1.2.parameter leafIndex transfer.2.1)
        0 (encoding transfer.2.1).val (keyResult.1.2.chainStart leafIndex transfer.2.1) := by
    rw [hreplay]
    rfl
  unfold advanceSignatureChain
  rw [chainHash_run_cached _ _ _ _ _ cache output (by rw [hvalue]; exact hle hcached)]
  have houtput : truncateHash output =
      (CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness
        (transferEncoding encoding transfer)).chainValue transfer.2.1 := by
    change truncateHash output = Wots.walk _ 0 (transferEncoding encoding transfer transfer.2.1).val _
    rw [transferEncoding_upper, Wots.walk, Nat.zero_add]
    unfold CacheView.chainStep
    have hposition : (encoding transfer.2.1).val < chainLength - 1 :=
      (successorStep encoding ⟨transfer.2.1, transfer.2.2.1⟩).isLt
    rw [dif_pos hposition]
    exact (CacheView.digestAt_eq_of_cache_eq_some hcached).symm
  rw [houtput]

theorem advanceSignatureChain_queryBound (parameter : PublicParameter) (leafIndex : LeafIndex)
    (original : Signature) (encoding : Encoding) (transfer : DigitTransfer encoding) :
    (advanceSignatureChain parameter leafIndex original encoding transfer).IsQueryBoundP (fun _ => True) 1 := by
  unfold advanceSignatureChain chainHash tweakableHash oracleHash
  simp

theorem transferredSignature_replay (keyCache : QueryCache HashSpec) (secretKey : SecretKey)
    (leafIndex : LeafIndex) (original : Signature) (encoding : Encoding)
    (hreplay : original = CacheReplay.signWithEncoding keyCache secretKey leafIndex original.randomness encoding)
    (randomness : Randomness) (transfer : DigitTransfer encoding) (preimage advanced : Digest)
    (hadvanced : advanced =
      (CacheReplay.signWithEncoding keyCache secretKey leafIndex randomness
        (transferEncoding encoding transfer)).chainValue transfer.2.1) :
    transferredSignature original randomness encoding transfer preimage advanced =
      CappedChain.replaceSignatureChainValue
        (CacheReplay.signWithEncoding keyCache secretKey leafIndex randomness
          (transferEncoding encoding transfer)) transfer.1.1 preimage := by
  rw [hreplay]
  unfold transferredSignature CappedChain.replaceSignatureChainValue CacheReplay.signWithEncoding
  congr 1
  funext chain
  by_cases hlower : chain = transfer.1.1
  · subst chain
    simp [Ne.symm transfer.2.2.2]
  · by_cases hupper : chain = transfer.2.1
    · subst chain
      simpa only [Function.update_self, Function.update_of_ne hlower, CacheReplay.signWithEncoding] using hadvanced
    · simp only [Function.update_of_ne hlower, Function.update_of_ne hupper,
        CacheReplay.signedChainValues, transferEncoding_other _ _ _ hlower hupper]

theorem verifyTransferredSignature_run
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (original : Signature) (encoding : Encoding)
    (hreplay : original = CacheReplay.signWithEncoding keyResult.2 keyResult.1.2
      leafIndex original.randomness encoding)
    (message : Message) (randomness : Randomness) (transfer : DigitTransfer encoding)
    (preimage advanced : Digest) (cache : QueryCache HashSpec) (hle : keyResult.2 ≤ cache)
    (hdecode : CacheView.decodedEncoding cache keyResult.1.2.parameter leafIndex (message, randomness) =
        some (transferEncoding encoding transfer))
    (hadvanced : advanced =
      (CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex randomness
        (transferEncoding encoding transfer)).chainValue transfer.2.1)
    (output : HashOutput)
    (hcached : cache (CacheView.chainInput keyResult.1.2.parameter leafIndex transfer.1.1
      (predecessorStep encoding transfer.1) preimage) = some output)
    (htarget : truncateHash output = original.chainValue transfer.1.1) :
    (simulateQ randomOracle (verify keyResult.1.1 leafIndex message
      (transferredSignature original randomness encoding transfer preimage advanced) :
        OracleComp HashSpec Bool)).run cache = pure (true, cache) := by
  rw [transferredSignature_replay _ _ _ _ _ hreplay _ _ _ _ hadvanced,
    verifyMutatedSignature_run keyResult hkey leafIndex transfer.1.1 message
      (transferEncoding encoding transfer) randomness preimage cache hle hdecode]
  have hstep : (transferEncoding encoding transfer transfer.1.1).val < chainLength - 1 := by
    rw [transferEncoding_lower]
    have hbound := (encoding transfer.1.1).isLt
    have hpositive := transfer.1.2
    omega
  rw [mutationRoot_run_after_cached_step keyResult hkey leafIndex transfer.1.1
    (transferEncoding encoding transfer) randomness cache hle hstep preimage output]
  · simp
  · have hposition : (⟨(transferEncoding encoding transfer transfer.1.1).val, hstep⟩ : ChainStep) =
        predecessorStep encoding transfer.1 := by
      apply Fin.ext
      exact transferEncoding_lower encoding transfer
    rw [hposition]
    exact hcached
  · rw [htarget, hreplay]
    change Wots.walk _ 0 (encoding transfer.1.1).val _ =
      Wots.walk _ 0 ((transferEncoding encoding transfer transfer.1.1).val + 1) _
    rw [transferEncoding_lower, Nat.sub_add_cancel (by have h := transfer.1.2; omega)]

/-- info: 'XmssSecurity.Checksum.Attack.verifyTransferredSignature_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms verifyTransferredSignature_run

end XmssSecurity.Checksum.Attack
