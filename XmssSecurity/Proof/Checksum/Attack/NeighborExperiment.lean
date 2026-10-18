import XmssSecurity.Proof.Checksum.Attack.NeighborVerification
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability
import XmssSecurity.Proof.Checksum.SigningSuccess

/-! Combining predecessor search with construction and verification of the neighboring signature. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.Attack

open Concrete

theorem encodingDecode_of_cache_le (initialCache finalCache : QueryCache HashSpec)
    (hle : initialCache ≤ finalCache) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (encoding : Encoding)
    (hdecode : Generic.Concrete.CacheView.decodedEncoding initialCache parameter leafIndex (message, randomness) = some encoding) :
    Generic.Concrete.CacheView.decodedEncoding finalCache parameter leafIndex (message, randomness) = some encoding := by
  obtain ⟨output, hcached⟩ := Generic.Concrete.CacheView.encodingInput_cached_of_decode_some initialCache
    parameter leafIndex message randomness encoding hdecode
  rw [← Generic.Concrete.CacheView.decodedEncoding_eq_of_input_eq (hcached.trans (hle hcached).symm)]
  exact hdecode

def checkNeighborPreimage (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message)
    (original : Generic.Signature) (encoding : Encoding) (randomness : Randomness)
    (transfer : DigitTransfer encoding) (block : PreimagePrefix) :
    Option (ℕ × HashOutput) → OracleComp HashSpec Bool
  | none => pure false
  | some (position, _) => do
      let advanced ← advanceSignatureChain publicKey.parameter leafIndex original encoding transfer
      Generic.Concrete.verify publicKey leafIndex message
        (transferredSignature original randomness encoding transfer (preimageCandidate block position) advanced)

theorem checkNeighborPreimage_run
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (original : Generic.Signature) (encoding : Encoding)
    (hreplay : original = Generic.Concrete.CacheReplay.signWithEncoding keyResult.2 keyResult.1.2
      leafIndex original.randomness encoding)
    (message : Message) (randomness : Randomness) (transfer : DigitTransfer encoding)
    (initialCache : QueryCache HashSpec) (hle : keyResult.2 ≤ initialCache)
    (hdecode : Generic.Concrete.CacheView.decodedEncoding initialCache keyResult.1.2.parameter leafIndex (message, randomness) =
        some (transferEncoding encoding transfer))
    (block : PreimagePrefix) (answer : Option (ℕ × HashOutput)) (finalCache : QueryCache HashSpec)
    (hsearch : (answer, finalCache) ∈ support ((simulateQ randomOracle
      (findDigestPreimage (Generic.Concrete.CacheView.chainInput keyResult.1.2.parameter leafIndex transfer.1.1
        (predecessorStep encoding transfer.1)) (original.chainValue transfer.1.1) block)).run initialCache)) :
    (simulateQ randomOracle (checkNeighborPreimage keyResult.1.1 leafIndex message original encoding
      randomness transfer block answer)).run finalCache = pure (decide (answer ≠ none), finalCache) := by
  cases answer with
  | none => simp [checkNeighborPreimage]
  | some answer =>
      rcases answer with ⟨position, output⟩
      obtain ⟨_, htarget, hcached⟩ := findDigestPreimage_success_cached _ _ _ _ _ _ _ hsearch
      have hcache := Generic.Concrete.CacheReplay.randomOracle_cache_le _ initialCache (some (position, output), finalCache) hsearch
      have hfinal := hle.trans hcache
      have hdecodeFinal := encodingDecode_of_cache_le initialCache finalCache hcache _ _ _ _ _ hdecode
      rw [checkNeighborPreimage, simulateQ_bind, StateT.run_bind]
      have hparameter := Generic.Deciding.keygen_publicKey_parameter_eq keyResult hkey
      rw [hparameter, advanceSignatureChain_run keyResult hkey leafIndex original encoding hreplay
        randomness transfer finalCache hfinal, pure_bind]
      rw [verifyTransferredSignature_run keyResult hkey leafIndex original encoding hreplay
        message randomness transfer (preimageCandidate block position) _ finalCache hfinal hdecodeFinal rfl
        output hcached htarget]
      rfl

theorem randomDigestPreimage_support (input : Digest → HashInput) (target : Digest)
    (cache : QueryCache HashSpec) (block : PreimagePrefix) (answer : Option (ℕ × HashOutput))
    (finalCache : QueryCache HashSpec)
    (hmem : (block, (answer, finalCache)) ∈ support (randomDigestPreimage input target cache)) :
    (answer, finalCache) ∈ support
      ((simulateQ randomOracle (findDigestPreimage input target block)).run cache) := by
  unfold randomDigestPreimage at hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨sampled, _, hrest⟩ := hmem
  simp only [bind_pure_comp, support_map, Set.mem_image] at hrest
  obtain ⟨result, hresult, heq⟩ := hrest
  cases heq
  exact hresult

noncomputable def predecessorVerificationExperiment (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (original : Generic.Signature) (encoding : Encoding) (randomness : Randomness)
    (transfer : DigitTransfer encoding) (cache : QueryCache HashSpec) : ProbComp Bool := do
  let result ← randomDigestPreimage (Generic.Concrete.CacheView.chainInput publicKey.parameter leafIndex transfer.1.1
    (predecessorStep encoding transfer.1)) (original.chainValue transfer.1.1) cache
  let verified ← (simulateQ randomOracle (checkNeighborPreimage publicKey leafIndex message original
    encoding randomness transfer result.1 result.2.1)).run result.2.2
  return verified.1

theorem predecessorVerificationExperiment_probability
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅))
    (leafIndex : LeafIndex) (original : Generic.Signature) (encoding : Encoding)
    (hreplay : original = Generic.Concrete.CacheReplay.signWithEncoding keyResult.2 keyResult.1.2
      leafIndex original.randomness encoding)
    (message : Message) (randomness : Randomness) (transfer : DigitTransfer encoding)
    (cache : QueryCache HashSpec) (hle : keyResult.2 ≤ cache)
    (hdecode : Generic.Concrete.CacheView.decodedEncoding cache keyResult.1.2.parameter leafIndex (message, randomness) =
        some (transferEncoding encoding transfer)) :
    Pr[= true | predecessorVerificationExperiment keyResult.1.1 leafIndex message original encoding
      randomness transfer cache] =
      Pr[fun result => result.2.1 ≠ none |
        randomDigestPreimage (Generic.Concrete.CacheView.chainInput keyResult.1.2.parameter leafIndex transfer.1.1
          (predecessorStep encoding transfer.1)) (original.chainValue transfer.1.1) cache] := by
  unfold predecessorVerificationExperiment
  rw [Generic.Deciding.keygen_publicKey_parameter_eq keyResult hkey, probOutput_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply tsum_congr
  rintro ⟨block, answer, finalCache⟩
  by_cases hmem : (block, (answer, finalCache)) ∈ support
      (randomDigestPreimage (Generic.Concrete.CacheView.chainInput keyResult.1.2.parameter leafIndex transfer.1.1
        (predecessorStep encoding transfer.1)) (original.chainValue transfer.1.1) cache)
  · rw [checkNeighborPreimage_run keyResult hkey leafIndex original encoding hreplay message randomness
      transfer cache hle hdecode block answer finalCache (randomDigestPreimage_support _ _ _ _ _ _ hmem)]
    cases answer <;> simp
  · rw [probOutput_eq_zero_of_not_mem_support hmem]
    simp

noncomputable def selectedNeighborTransfer (encoding : Encoding) (digest : Digest)
    (hmem : digest ∈ neighborDigests encoding) : DigitTransfer encoding :=
  Classical.choose (Finset.mem_image.mp hmem)

theorem selectedNeighborTransfer_decode (encoding : Encoding) (hvalid : Generic.Code.Valid encoding)
    (digest : Digest) (hmem : digest ∈ neighborDigests encoding) :
    Generic.Code.decodeDigest digest = some (transferEncoding encoding (selectedNeighborTransfer encoding digest hmem)) := by
  have hspec := Classical.choose_spec (Finset.mem_image.mp hmem)
  have heq := hspec.2
  change digestOfEncoding (transferEncoding encoding (selectedNeighborTransfer encoding digest hmem)) = digest at heq
  conv_lhs => rw [← heq]
  exact digestOfEncoding_decode _ (mem_neighborTransfers.mp hspec.1)

noncomputable def neighborVerificationContinuation (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (original : Generic.Signature) (encoding : Encoding)
    (answer : Option (ℕ × HashOutput)) (cache : QueryCache HashSpec) : ProbComp Bool := by
  classical
  exact match answer with
  | none => pure false
  | some (position, output) =>
      if hmem : Generic.truncateHash output ∈ neighborDigests encoding then
        predecessorVerificationExperiment publicKey leafIndex message original encoding
          (BitVec.ofNat randomnessBits position) (selectedNeighborTransfer encoding (Generic.truncateHash output) hmem) cache
      else pure false

theorem neighborVerificationContinuation_lower
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅))
    (request : Generic.SignRequest) (original : Generic.Signature) (signCache : QueryCache HashSpec)
    (hsign : (some original, signCache) ∈ support ((simulateQ Generic.romImpl
      (Generic.Concrete.precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2))
    (encoding : Encoding) (hvalid : Generic.Code.Valid encoding)
    (hreplay : original = Generic.Concrete.CacheReplay.signWithEncoding keyResult.2 keyResult.1.2
      request.epoch original.randomness encoding)
    (message : Message) (position : ℕ) (output : HashOutput) (searchCache : QueryCache HashSpec)
    (hsearch : (some (position, output), searchCache) ∈ support ((simulateQ randomOracle
      (findEncodingNeighbor keyResult.1.2.parameter request.epoch message encoding)).run signCache)) :
    2 / 5 ≤ Pr[= true | neighborVerificationContinuation keyResult.1.1 request.epoch message
      original encoding (some (position, output)) searchCache] := by
  classical
  obtain ⟨_, _, hneighbor, hcached⟩ := Generic.Attack.findHash_success_cached _ _ _ _ _ _ _ _ hsearch
  change Generic.truncateHash output ∈ neighborDigests encoding at hneighbor
  unfold neighborSearchInput at hcached
  simp only [neighborVerificationContinuation, dif_pos hneighbor]
  have hdecode : Generic.Concrete.CacheView.decodedEncoding searchCache keyResult.1.2.parameter
      request.epoch (message, BitVec.ofNat randomnessBits position) =
        some (transferEncoding encoding (selectedNeighborTransfer encoding (Generic.truncateHash output) hneighbor)) := by
    rw [Generic.Concrete.CacheView.decodedEncoding_eq_of_cache_eq_some hcached, Generic.Concrete.CacheView.encodingHash,
      Generic.Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached]
    exact selectedNeighborTransfer_decode encoding hvalid _ hneighbor
  have hsignLe := Generic.xmssRom_cache_le _ keyResult.2 (some original, signCache) hsign
  have hsearchLe := Generic.Concrete.CacheReplay.randomOracle_cache_le _ signCache (some (position, output), searchCache) hsearch
  rw [predecessorVerificationExperiment_probability keyResult hkey request.epoch original encoding
    hreplay message _ _ searchCache (hsignLe.trans hsearchLe) hdecode]
  exact randomDigestPreimage_success_after_neighborSearch keyResult hkey request original signCache hsign
    encoding hreplay message (some (position, output)) searchCache hsearch _

noncomputable def neighborVerificationExperiment (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (original : Generic.Signature) (encoding : Encoding) (cache : QueryCache HashSpec) : ProbComp Bool := do
  let result ← (simulateQ randomOracle (findEncodingNeighbor publicKey.parameter leafIndex message encoding)).run cache
  neighborVerificationContinuation publicKey leafIndex message original encoding result.1 result.2

theorem neighborVerificationExperiment_lower
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅))
    (request : Generic.SignRequest) (original : Generic.Signature) (signCache : QueryCache HashSpec)
    (hsign : (some original, signCache) ∈ support ((simulateQ Generic.romImpl
      (Generic.Concrete.precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2))
    (encoding : Encoding) (hvalid : Generic.Code.Valid encoding)
    (hreplay : original = Generic.Concrete.CacheReplay.signWithEncoding keyResult.2 keyResult.1.2
      request.epoch original.randomness encoding)
    (message : Message) (hne : message ≠ request.message) :
    (6 / 7 : ℝ≥0∞) * (2 / 5) ≤ Pr[= true | neighborVerificationExperiment keyResult.1.1 request.epoch message
      original encoding signCache] := by
  classical
  let search := (simulateQ randomOracle
    (findEncodingNeighbor keyResult.1.2.parameter request.epoch message encoding)).run signCache
  calc
    _ ≤ Pr[fun result => result.1 ≠ none | search] * (2 / 5) :=
      mul_le_mul_left (le_of_lt (findEncodingNeighbor_success_after_signing keyResult hkey request
        (some original) signCache hsign message hne encoding hvalid)) _
    _ ≤ _ := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      unfold neighborVerificationExperiment
      rw [Generic.Deciding.keygen_publicKey_parameter_eq keyResult hkey, probOutput_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      rintro ⟨answer, searchCache⟩
      by_cases hmem : (answer, searchCache) ∈ support search
      · cases answer with
        | none => simp
        | some answer =>
            rcases answer with ⟨position, output⟩
            simp only [ne_eq, Option.some_ne_none, not_false_eq_true, if_true]
            exact mul_le_mul_right (neighborVerificationContinuation_lower keyResult hkey request original
              signCache hsign encoding hvalid hreplay message position output searchCache hmem) _
      · have hzero := probOutput_eq_zero_of_not_mem_support hmem
        change _ ≤ Pr[= (answer, searchCache) | search] * _
        rw [hzero]
        simp

noncomputable def signedNeighborExperiment
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec) (request : Generic.SignRequest)
    (message : Message) : ProbComp Bool := do
  let result ← (simulateQ Generic.romImpl
    (Generic.Concrete.precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2
  match result.1 with
  | none => pure false
  | some original =>
      match Generic.Concrete.CacheView.decodedEncoding result.2 keyResult.1.2.parameter
        request.epoch (request.message, original.randomness) with
      | none => pure false
      | some encoding => neighborVerificationExperiment keyResult.1.1 request.epoch message original encoding result.2

theorem signedNeighborExperiment_lower
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅))
    (request : Generic.SignRequest) (message : Message) (hne : message ≠ request.message) :
    (127 / 128 : ℝ≥0∞) * ((6 / 7) * (2 / 5)) ≤
      Pr[= true | signedNeighborExperiment keyResult request message] := by
  classical
  let lower : ℝ≥0∞ := (6 / 7) * (2 / 5)
  let signing := (simulateQ Generic.romImpl
    (Generic.Concrete.precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2
  calc
    _ ≤ Pr[fun result => result.1 ≠ none | signing] * lower :=
      mul_le_mul_left (le_of_lt (Concrete.precomputedCappedSign_success_after_keygen keyResult hkey
        request.epoch request.message)) _
    _ ≤ _ := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      unfold signedNeighborExperiment
      rw [probOutput_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      rintro ⟨answer, signCache⟩
      by_cases hmem : (answer, signCache) ∈ support signing
      · cases answer with
        | none => simp
        | some original =>
            obtain ⟨encoding, hdecode, hreplay⟩ := Generic.Attack.signing_success_replay_at_keygen keyResult hkey
              request original signCache hmem
            simp only [ne_eq, Option.some_ne_none, not_false_eq_true, if_true, hdecode]
            exact mul_le_mul_right (neighborVerificationExperiment_lower keyResult hkey request original
              signCache hmem encoding (Generic.Concrete.CacheView.decodedEncoding_valid hdecode) hreplay message hne) _
      · have hzero := probOutput_eq_zero_of_not_mem_support hmem
        change _ ≤ Pr[= (answer, signCache) | signing] * _
        rw [hzero]
        simp

/-- info: 'XmssSecurity.Checksum.Attack.predecessorVerificationExperiment_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms predecessorVerificationExperiment_probability

end XmssSecurity.Checksum.Attack
