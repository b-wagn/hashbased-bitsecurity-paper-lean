import XmssSecurity.Proof.Checksum.Attack.OneRequest
import XmssSecurity.Proof.Checksum.Attack.MutationGame
import XmssSecurity.Proof.Common.EUFCMA.Reduction
import XmssSecurity.Proof.Generic.Attack.MutationVerification
import XmssSecurity.Proof.Generic.ConcreteQueryBound
import XmssSecurity.Proof.Checksum.Attack.ChainMutationSeeded
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability
import XmssSecurity.Proof.Checksum.SigningSuccess

/-! The fresh-message adversary: request a signature at `mutationRequest` and submit it unchanged
for a different message at the same epoch.

Every digest encodes, so the verifier recovers some endpoints from the signature, hashes them into
a leaf, and climbs the honest authentication path of the signature. The leaf is either the honest
one or fresh, and each of the `33` hash calls from the leaf up meets the honest path with
probability `2^-128`. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.Attack

open Concrete

def freshMessage : Message := 1

theorem freshMessage_ne_request : freshMessage ≠ Generic.Attack.mutationRequest.message := by decide

/-- Submit the returned signature for `freshMessage`; the private samples are not used. -/
def freshMessageForgery (answer : Option Generic.Signature) (_choice : ChainIndex × Digest) : Generic.Forgery :=
  ⟨Generic.Attack.mutationRequest.epoch, freshMessage, answer.getD Generic.Attack.fallbackSignature⟩

noncomputable abbrev freshAdversary : Generic.Adversary := oneRequestAdversary freshMessageForgery

theorem freshMessage_request_fresh (answer : Option Generic.Signature) (choice : ChainIndex × Digest) :
    ¬ EUFCMA.SigningTranscript.ContainsRequest [⟨Generic.Attack.mutationRequest, answer⟩]
      (freshMessageForgery answer choice) := by
  simp only [EUFCMA.SigningTranscript.ContainsRequest, List.mem_singleton, exists_eq_left]
  intro heq
  exact freshMessage_ne_request
    (congrArg (fun request : Generic.SignRequest => request.message) heq).symm

theorem freshMessage_not_contains (answer : Option Generic.Signature) (choice : ChainIndex × Digest) :
    ¬ Generic.SigningTranscript.Contains [⟨Generic.Attack.mutationRequest, answer⟩] (freshMessageForgery answer choice) :=
  fun h => freshMessage_request_fresh answer choice (EUFCMA.containsRequest_of_contains _ _ h)

theorem oneRequest_gameRest {Key : Type} (finish : Option Generic.Signature → ChainIndex × Digest → Generic.Forgery)
    (scheme : Generic.Scheme Key) (publicKey : PublicKey) (secretKey : Key) :
    Generic.Seeded.gameRest scheme (oneRequestAdversary finish) publicKey secretKey = (do
      let answer ← scheme.sign secretKey Generic.Attack.mutationRequest.epoch Generic.Attack.mutationRequest.message
      let choice ← worldPrivateSamples Generic.Attack.mutationChoice
      let forgery := finish answer choice
      let verified ← scheme.verify publicKey forgery.epoch forgery.message forgery.signature
      return decide (Generic.SigningTranscript.Valid [⟨Generic.Attack.mutationRequest, answer⟩] ∧
        ¬Generic.SigningTranscript.Contains [⟨Generic.Attack.mutationRequest, answer⟩] forgery) && verified) := by
  unfold Generic.Seeded.gameRest
  change (do
    let result ← (simulateQ (Generic.forwardOracles + Generic.signingOracle scheme secretKey)
      (oneRequestMain finish Generic.Attack.mutationChoice)).run
    let verified ← scheme.verify publicKey result.1.epoch result.1.message result.1.signature
    return decide (Generic.SigningTranscript.Valid result.2 ∧ ¬Generic.SigningTranscript.Contains result.2 result.1) && verified) = _
  rw [show oneRequestMain finish Generic.Attack.mutationChoice = (do
      let answer ← liftM ((OracleWorld + Generic.SigningSpec).query (.inr Generic.Attack.mutationRequest))
      let choice ← Generic.Attack.liftPrivateSamples Generic.Attack.mutationChoice
      pure (finish answer choice)) from rfl,
    oneRequestSamples_logged scheme secretKey Generic.Attack.mutationRequest Generic.Attack.mutationChoice finish]
  simp only [bind_assoc, pure_bind]

/-- The verification of the fresh forgery, from the signer's answer. -/
def freshOutcome (publicKey : PublicKey) (answer : Option Generic.Signature) : OracleComp HashSpec Bool := do
  let verified ← Generic.Concrete.verify publicKey Generic.Attack.mutationRequest.epoch freshMessage (answer.getD Generic.Attack.fallbackSignature)
  return decide (Generic.SigningTranscript.Valid [⟨Generic.Attack.mutationRequest, answer⟩]) && verified

theorem fresh_referenceRest_run (publicKey : PublicKey) (secretKey : Generic.SecretKey)
    (cache : QueryCache HashSpec) :
    (simulateQ Generic.romImpl (Generic.Seeded.gameRest Generic.Concrete.scheme freshAdversary publicKey secretKey)).run cache = (do
      let result ← (simulateQ Generic.romImpl
        (Generic.Concrete.precomputedCappedSign secretKey Generic.Attack.mutationRequest.epoch Generic.Attack.mutationRequest.message)).run cache
      let _choice ← Generic.Attack.mutationChoice
      (simulateQ randomOracle (freshOutcome publicKey result.1)).run result.2) := by
  rw [oneRequest_gameRest, simulateQ_bind, StateT.run_bind]
  apply bind_congr
  rintro ⟨answer, signCache⟩
  rw [simulateQ_bind, StateT.run_bind, worldPrivateSamples_run, bind_map_left]
  apply bind_congr
  intro choice
  have hroute : simulateQ Generic.romImpl
      (liftM (Generic.Concrete.verify publicKey Generic.Attack.mutationRequest.epoch freshMessage (answer.getD Generic.Attack.fallbackSignature) :
          OracleComp HashSpec Bool)) =
      simulateQ randomOracle (Generic.Concrete.verify publicKey Generic.Attack.mutationRequest.epoch freshMessage
        (answer.getD Generic.Attack.fallbackSignature) : OracleComp HashSpec Bool) :=
    QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) _
  unfold freshOutcome
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  change (simulateQ Generic.romImpl (liftM (Generic.Concrete.verify publicKey Generic.Attack.mutationRequest.epoch freshMessage
      (answer.getD Generic.Attack.fallbackSignature) : OracleComp HashSpec Bool))).run signCache >>= _ = _
  rw [hroute]
  simp only [simulateQ_pure, StateT.run_pure, freshMessage_not_contains, not_false_eq_true,
    and_true]

/-! ### The verification of the fresh forgery -/

/-- A lower bound on an event after a bind, from a lower bound after every result. -/
theorem le_probEvent_bind_of_forall {α β : Type} (mx : ProbComp α) (f : α → ProbComp β)
    (event : β → Prop) (bound : ℝ≥0∞) (h : ∀ x ∈ support mx, bound ≤ Pr[event | f x]) :
    bound ≤ Pr[event | mx >>= f] := by
  rw [probEvent_bind_eq_tsum]
  have hmass : ∑' x, Pr[= x | mx] = 1 := tsum_probOutput_eq_one' (by simp)
  calc
    bound = ∑' x, Pr[= x | mx] * bound := by rw [ENNReal.tsum_mul_right, hmass, one_mul]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases hx : x ∈ support mx
      · exact mul_le_mul' le_rfl (h x hx)
      · simp [probOutput_eq_zero_of_not_mem_support hx]

/-- A computation that does not query `target` leaves its cache entry unchanged. -/
theorem cache_eq_of_zero_query_bound {α : Type} (computation : OracleComp HashSpec α)
    (target : HashInput) (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hbound : computation.IsQueryBoundP (· = target) 0)
    (hmem : (result, finalCache) ∈ support ((simulateQ randomOracle computation).run initialCache)) :
    finalCache target = initialCache target := by
  cases hinitial : initialCache target with
  | none =>
      exact Generic.Concrete.CacheReplay.cache_none_of_zero_query_bound computation target initialCache
        finalCache result hbound hinitial hmem
  | some output =>
      exact Generic.Concrete.CacheReplay.randomOracle_cache_le computation initialCache
        (result, finalCache) hmem hinitial

/-- Recovering endpoints makes no query outside the chain addresses. -/
theorem recoverEndpoints_queryBound_zero_of_not_chain (parameter : PublicParameter)
    (leafIndex : LeafIndex) (encoding : Encoding) (signature : Generic.Signature) (domain : Generic.HashDomain)
    (hdomain : ∀ chain step, Generic.HashDomain.chain leafIndex chain step ≠ domain) (payload : HashInput) :
    (Generic.Concrete.recoverEndpoints parameter leafIndex encoding signature :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP
        (· = Generic.tweakableHashInput parameter domain payload) 0 := by
  apply OracleComp.IsQueryBoundP.of_imp (p' := Generic.AtHashAddress parameter domain)
  · rintro _ rfl
    exact (Generic.atHashAddress_tweakableHashInput_iff parameter domain domain payload).mpr rfl
  · unfold Generic.Concrete.recoverEndpoints
    exact Generic.Concrete.sequenceFin_queryBound_zero _ _ fun chain =>
      Generic.Concrete.chainWalk_queryBound_zero_of_avoids parameter leafIndex chain _ _ _ domain
        fun offset _ hvalid => hdomain chain _

/-- The fresh forgery's verification climbs the honest authentication path from a leaf that is
either honest or fresh. -/
noncomputable def freshPathLower : ℝ≥0∞ :=
  ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ +
    (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) *
      (1 - (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ treeHeight)

theorem freshPathLower_le_one : freshPathLower ≤ 1 := by
  unfold freshPathLower
  set p : ℝ≥0∞ := ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹
  have hp : p ≤ 1 := by norm_num [p, digestBits]
  calc
    _ ≤ p + (1 - p) * 1 := add_le_add le_rfl (mul_le_mul' le_rfl tsub_le_self)
    _ = 1 := by rw [mul_one, add_tsub_cancel_of_le hp]

set_option maxHeartbeats 2000000 in
theorem freshVerification_lower
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅))
    (signature : Generic.Signature) (finalCache : QueryCache HashSpec)
    (hsign : (some signature, finalCache) ∈ support ((simulateQ Generic.romImpl
      (Generic.Concrete.precomputedCappedSign keyResult.1.2 Generic.Attack.mutationRequest.epoch Generic.Attack.mutationRequest.message)).run
        keyResult.2))
    (message : Message) :
    freshPathLower ≤ Pr[fun result => result.1 = true |
      (simulateQ randomOracle (Generic.Concrete.verify keyResult.1.1 Generic.Attack.mutationRequest.epoch message signature :
        OracleComp HashSpec Bool)).run finalCache] := by
  classical
  obtain ⟨encoding, _hdecode, hsignature⟩ :=
    Generic.Attack.signing_success_replay_at_keygen keyResult hkey Generic.Attack.mutationRequest signature finalCache hsign
  have hparameter := Generic.Deciding.keygen_publicKey_parameter_eq keyResult hkey
  have hle := Generic.xmssRom_cache_le _ keyResult.2 (some signature, finalCache) hsign
  let leafIndex := Generic.Attack.mutationRequest.epoch
  let chain : ChainIndex := ⟨0, by decide⟩
  let inputs := Generic.Attack.mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding
    signature.randomness
  let honest := Generic.Attack.mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain (encoding chain)
  let start := Generic.Attack.mutationChainSteps (encoding chain) + 1
  let honestEndpoints := Generic.Concrete.CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
    keyResult.1.2.chainStart leafIndex
  have hagree := Generic.Attack.mutationReplayInputs_preserved_by_signing keyResult.2 keyResult.1.2 leafIndex
    chain encoding signature.randomness leafIndex Generic.Attack.mutationRequest.message (some signature)
    finalCache hsign
  -- Split the verification into the encoding, the endpoints, the leaf, and the path.
  rw [Generic.Concrete.verify_eq_decode]
  simp only [Generic.Code.decodeDigest, Checksum.decodeDigest]
  rw [simulateQ_bind, StateT.run_bind]
  apply le_probEvent_bind_of_forall
  rintro ⟨digest, digestCache⟩ hdigest
  rw [simulateQ_bind, StateT.run_bind]
  apply le_probEvent_bind_of_forall
  rintro ⟨endpoints, endpointsCache⟩ hendpoints
  -- Neither the encoding hash nor the chain walks touch the leaf and node addresses.
  have hpreserve : ∀ (domain : Generic.HashDomain), (∀ leaf, domain ≠ .encoding leaf) →
      (∀ leaf chain step, Generic.HashDomain.chain leaf chain step ≠ domain) →
      ∀ payload, endpointsCache (Generic.tweakableHashInput keyResult.1.1.parameter domain payload) =
        finalCache (Generic.tweakableHashInput keyResult.1.1.parameter domain payload) := by
    intro domain hencoding hchain payload
    rw [cache_eq_of_zero_query_bound _ _ digestCache endpointsCache endpoints
      (recoverEndpoints_queryBound_zero_of_not_chain _ _ _ _ domain
        (fun c s => hchain leafIndex c s) payload) hendpoints]
    refine cache_eq_of_zero_query_bound _ _ finalCache digestCache digest ?_ hdigest
    apply Generic.Concrete.encodingHash_queryBound_zero_at_other_input
    intro heq
    exact hencoding leafIndex (Generic.domain_eq_of_tweakableHashInput_eq _ heq).symm
  have hnode : ∀ i, start ≤ i → i < start + treeHeight → ∀ value,
      endpointsCache (inputs i value) = keyResult.2 (inputs i value) := by
    intro i hi hi' value
    have hlevel : i - start < treeHeight := by omega
    have hi'' : i = Generic.Attack.mutationChainSteps (encoding chain) + 1 + (i - start) := by omega
    rw [← hagree i (by omega) value]
    change endpointsCache (Generic.Attack.mutationPathInput _ _ _ _ _ _ i value) =
      finalCache (Generic.Attack.mutationPathInput _ _ _ _ _ _ i value)
    rw [hi'', Generic.Attack.mutationPathInput_node _ _ _ _ _ _ _ hlevel, ← hparameter]
    exact hpreserve _ (by simp) (by simp) _
  -- The authentication path is the node part of the mutation path.
  have hpath : ∀ leaf, (Generic.Concrete.verifyAfterLeaf keyResult.1.1 leafIndex signature leaf :
      OracleComp HashSpec Bool) =
      (fun root => decide (root = keyResult.1.1.root)) <$> Generic.Rom.hashPath inputs start treeHeight leaf := by
    intro leaf
    have h := Generic.Attack.mutationPath_authentication keyResult.1.2.parameter leafIndex chain (encoding chain)
      (Generic.Concrete.CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex signature.randomness encoding)
      honestEndpoints treeHeight le_rfl leaf
    unfold Generic.Concrete.verifyAfterLeaf
    rw [hparameter]
    conv_lhs => rw [hsignature]
    rw [← h, map_eq_bind_pure_comp]
    rfl
  have hhonest : ∀ i, start ≤ i → i < start + treeHeight →
      ∃ output, endpointsCache (inputs i (honest i)) = some output ∧
        Generic.truncateHash output = honest (i + 1) := by
    intro i hi hi'
    rw [hnode i hi hi']
    exact Generic.Attack.mutationReplayInputs_honest keyResult hkey leafIndex chain encoding signature.randomness
      i (by omega)
  have hfresh : ∀ i, start ≤ i → i < start + treeHeight → ∀ other, other ≠ honest i →
      endpointsCache (inputs i other) = none := by
    intro i hi hi' other hne
    rw [hnode i hi hi']
    exact Generic.Attack.mutationReplayInputs_fresh keyResult hkey leafIndex chain encoding signature.randomness
      i (by omega) other hne
  have hseparate : ∀ i, start ≤ i → i < start + treeHeight →
      ∀ j, start ≤ j → j < start + treeHeight → i ≠ j → ∀ left right,
        inputs i left ≠ inputs j right := fun i _ hi j _ hj hne left right =>
    Generic.Attack.mutationPathInput_separate _ _ _ _ _ _ i j (by omega) (by omega) hne left right
  have hroot : honest (start + treeHeight) = keyResult.1.1.root :=
    Generic.Attack.mutationHonestValue_root keyResult hkey leafIndex chain (encoding chain)
  -- The leaf hash is one query at the leaf address.
  let leafInput := Generic.Concrete.CacheView.leafInput keyResult.1.1.parameter leafIndex endpoints
  have hleafRun : ∀ cache : QueryCache HashSpec,
      (simulateQ randomOracle (do
        let leaf ← Generic.Concrete.leafHash keyResult.1.1.parameter leafIndex endpoints
        Generic.Concrete.verifyAfterLeaf keyResult.1.1 leafIndex signature leaf : OracleComp HashSpec Bool)).run cache =
      (randomOracle leafInput).run cache >>= fun result =>
        (simulateQ randomOracle (Generic.Concrete.verifyAfterLeaf keyResult.1.1 leafIndex signature
          (Generic.truncateHash result.1) : OracleComp HashSpec Bool)).run result.2 := by
    intro cache
    simp only [Generic.Concrete.leafHash, Generic.Concrete.tweakableHash, Generic.Concrete.oracleHash, bind_assoc, pure_bind, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind, HasQuery.instOfMonadLift_query]
    rfl
  rw [hleafRun]
  have hleafPreserved : endpointsCache leafInput = keyResult.2 leafInput := by
    rw [show leafInput = Generic.tweakableHashInput keyResult.1.1.parameter (.leaf leafIndex)
      (Generic.Concrete.leafPayload endpoints) from rfl, hpreserve _ (by simp) (by simp)]
    rw [Generic.Concrete.precomputedCappedSign] at hsign
    refine Generic.Concrete.precomputedSignBoundedAttempts_preserves_unqueriedInput signingAttemptLimit keyResult.1.2
      leafIndex Generic.Attack.mutationRequest.message _ (fun randomness heq => ?_) keyResult.2 finalCache
      (some signature) hsign
    rw [hparameter] at heq
    unfold Generic.Concrete.CacheView.encodingInput at heq
    have := Generic.domain_eq_of_tweakableHashInput_eq _ heq
    simp at this
  -- The path from a leaf value, as a hash path.
  have hpathRun : ∀ (leaf : Digest) (cache : QueryCache HashSpec),
      Pr[fun result => result.1 = true |
        (simulateQ randomOracle (Generic.Concrete.verifyAfterLeaf keyResult.1.1 leafIndex signature leaf :
          OracleComp HashSpec Bool)).run cache] =
      Pr[fun result : Digest × QueryCache HashSpec => result.1 = honest (start + treeHeight) |
        (simulateQ randomOracle (Generic.Rom.hashPath inputs start treeHeight leaf)).run cache] := by
    intro leaf cache
    rw [hpath, simulateQ_map, StateT.run_map, probEvent_map, hroot]
    simp [Function.comp_def]
  by_cases hhonestEndpoints : endpoints = honestEndpoints
  · -- The honest leaf is cached, and the honest path leads to the root.
    obtain ⟨output, houtput, htruncate⟩ := Generic.Attack.mutationReplayInputs_honest keyResult hkey leafIndex
      chain encoding signature.randomness (Generic.Attack.mutationChainSteps (encoding chain)) (by omega)
    have hinput : Generic.Attack.mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding
        signature.randomness (Generic.Attack.mutationChainSteps (encoding chain))
        (Generic.Attack.mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain (encoding chain)
          (Generic.Attack.mutationChainSteps (encoding chain))) = leafInput := by
      unfold Generic.Attack.mutationReplayInputs
      rw [Generic.Attack.mutationPathInput_leaf, Generic.Attack.mutationHonestValue_endpoint, Function.update_eq_self]
      simp only [leafInput, hhonestEndpoints, honestEndpoints, hparameter]
    rw [hinput] at houtput
    rw [QueryImpl.withCaching_run_some _ (hleafPreserved.trans houtput), pure_bind, hpathRun,
      htruncate, Generic.Attack.hashPath_run_honest inputs honest start treeHeight endpointsCache hhonest]
    simp only [probEvent_pure, if_true]
    exact freshPathLower_le_one
  · -- A fresh leaf meets the honest path with the remaining `33` hash calls.
    have hnone : endpointsCache leafInput = none := by
      rw [hleafPreserved]
      let oldKeyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec :=
        ((keyResult.1.1, Generic.Concrete.erasePrecomputation keyResult.1.2), keyResult.2)
      have hold : oldKeyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.keygen).run ∅) :=
        Generic.Concrete.precomputedKeygen_support_oldKeygen keyResult (by
          simpa only [Generic.Concrete.scheme] using hkey)
      rw [show leafInput = Generic.Concrete.CacheView.leafInput keyResult.1.2.parameter leafIndex endpoints by
        simp only [leafInput, hparameter]]
      exact Generic.Concrete.keygen_cache_leafInput_eq_none_of_ne oldKeyResult hold leafIndex endpoints
        hhonestEndpoints
    rw [Generic.randomOracle_run_none_eq_uniformHashOutput _ _ hnone, Generic.uniformHashOutput, bind_map_left,
      probEvent_bind_eq_tsum]
    have hnodeInput : ∀ i, start ≤ i → i < start + treeHeight → ∀ value,
        inputs i value ≠ leafInput := by
      intro i hi hi' value heq
      have hlevel : i - start < treeHeight := by omega
      have hi'' : i = Generic.Attack.mutationChainSteps (encoding chain) + 1 + (i - start) := by omega
      change Generic.Attack.mutationPathInput _ _ _ _ _ _ i value = _ at heq
      rw [hi'', Generic.Attack.mutationPathInput_node _ _ _ _ _ _ _ hlevel] at heq
      simp only [Generic.Concrete.CacheView.nodeInput, leafInput, Generic.Concrete.CacheView.leafInput, hparameter] at heq
      have := Generic.domain_eq_of_tweakableHashInput_eq _ heq
      simp at this
    have hstep (output : HashOutput) :
        Pr[fun result => result.1 = true |
          (simulateQ randomOracle (Generic.Concrete.verifyAfterLeaf keyResult.1.1 leafIndex signature
            (Generic.truncateHash output) : OracleComp HashSpec Bool)).run
              (endpointsCache.cacheQuery leafInput output)] =
          if Generic.truncateHash output = honest start then 1
          else 1 - (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ treeHeight := by
      rw [hpathRun]
      apply Generic.Rom.hashPath_hit_probability inputs honest start treeHeight (Generic.truncateHash output) _
        hseparate
      · intro i hi hi'
        obtain ⟨answer, hanswer, htarget⟩ := hhonest i hi hi'
        exact ⟨answer, by rw [QueryCache.cacheQuery_of_ne _ _ (hnodeInput i hi hi' _)]; exact hanswer,
          htarget⟩
      · intro i hi hi' other hother
        rw [QueryCache.cacheQuery_of_ne _ _ (hnodeInput i hi hi' _)]
        exact hfresh i hi hi' other hother
    simp_rw [hstep]
    have hhit : Pr[fun output : HashOutput => Generic.truncateHash output = honest start | $ᵗ HashOutput] =
        ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ := Generic.Rom.uniform_truncate_probability _
    have hmiss := Generic.Rom.uniform_truncate_miss_probability (honest start)
    apply le_of_eq
    calc
      freshPathLower = Pr[fun output : HashOutput => Generic.truncateHash output = honest start |
            $ᵗ HashOutput] * 1 +
          Pr[fun output : HashOutput => Generic.truncateHash output ≠ honest start | $ᵗ HashOutput] *
            (1 - (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ treeHeight) := by
        rw [hhit, hmiss, mul_one]
        rfl
      _ = _ := by
        rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right,
          ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
        apply tsum_congr
        intro output
        by_cases h : Generic.truncateHash output = honest start <;> simp [h]


/-! ### The advantage of the fresh-message adversary -/

theorem freshOutcome_some (publicKey : PublicKey) (signature : Generic.Signature) :
    freshOutcome publicKey (some signature) =
      (Generic.Concrete.verify publicKey Generic.Attack.mutationRequest.epoch freshMessage signature : OracleComp HashSpec Bool) := by
  unfold freshOutcome
  simp only [Generic.Attack.chainMutation_transcript_valid, decide_true, Bool.true_and, Option.getD_some]
  rw [bind_pure]

theorem fresh_referenceRest_lower
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅)) :
    (127 / 128 : ℝ≥0∞) * freshPathLower ≤
      Pr[fun result => result.1 = true |
        (simulateQ Generic.romImpl (Generic.Seeded.gameRest Generic.Concrete.scheme freshAdversary
          keyResult.1.1 keyResult.1.2)).run keyResult.2] := by
  let signing := (simulateQ Generic.romImpl
    (Generic.Concrete.precomputedCappedSign keyResult.1.2 Generic.Attack.mutationRequest.epoch Generic.Attack.mutationRequest.message)).run keyResult.2
  rw [fresh_referenceRest_run]
  calc
    _ ≤ Pr[fun result => result.1 ≠ none | signing] * freshPathLower :=
      mul_le_mul_left (le_of_lt (Concrete.precomputedCappedSign_success_after_keygen keyResult hkey
        Generic.Attack.mutationRequest.epoch Generic.Attack.mutationRequest.message)) _
    _ ≤ _ := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right, probEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      rintro ⟨answer, finalCache⟩
      by_cases hmem : (answer, finalCache) ∈ support signing
      · cases answer with
        | none => simp
        | some signature =>
            simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_true]
            apply mul_le_mul' le_rfl
            apply le_probEvent_bind_of_forall
            intro _choice _
            rw [freshOutcome_some]
            exact freshVerification_lower keyResult hkey signature finalCache hmem freshMessage
      · rw [probOutput_eq_zero_of_not_mem_support hmem]
        simp

theorem fresh_reference_advantage_lower :
    (127 / 128 : ℝ≥0∞) * freshPathLower ≤ Generic.forgeAdvantage Generic.Concrete.scheme freshAdversary := by
  let lower : ℝ≥0∞ := (127 / 128) * freshPathLower
  let keys := (simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅
  have hmass : ∑' keyResult, Pr[= keyResult | keys] = 1 := tsum_probOutput_eq_one' (by simp)
  rw [Generic.forgeAdvantage_eq_gameWithCache]
  unfold Generic.gameWithCache Generic.gameCore
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  calc
    _ = ∑' keyResult, Pr[= keyResult | keys] * lower := by
      rw [ENNReal.tsum_mul_right, hmass, one_mul]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro keyResult
      by_cases hkey : keyResult ∈ support keys
      · exact mul_le_mul_right (fresh_referenceRest_lower keyResult hkey) _
      · have hzero := probOutput_eq_zero_of_not_mem_support hkey
        change _ ≤ Pr[= keyResult | keys] * _
        rw [hzero]
        simp

/-- `(127/128) · (p + (1 - p)(1 - (1 - p)^32)) > 32 p` for `p = 2^-128`. -/
theorem fresh_lower_exceeds_123 :
    (1 : ℝ≥0∞) / ((2 ^ 123 : ℕ) : ℝ≥0∞) < (127 / 128 : ℝ≥0∞) * freshPathLower := by
  set p : ℝ≥0∞ := ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹
  have hp : p ≤ 1 := by norm_num [p, digestBits]
  have hpow : (1 - p) ^ treeHeight ≤ 1 / (1 + (treeHeight : ℝ≥0∞) * p) :=
    Generic.Code.rejection_power_le p hp treeHeight
  have hlower : p + (1 - p) * (1 - 1 / (1 + (treeHeight : ℝ≥0∞) * p)) ≤ freshPathLower :=
    add_le_add le_rfl (mul_le_mul' le_rfl (tsub_le_tsub_left hpow 1))
  refine lt_of_lt_of_le ?_ (mul_le_mul' le_rfl hlower)
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  have hpReal : p.toReal = 1 / 2 ^ 128 := by norm_num [p, digestBits]
  have hsmall : 1 / (1 + (treeHeight : ℝ≥0∞) * p) ≤ 1 := by
    apply ENNReal.div_le_of_le_mul
    rw [one_mul]
    exact le_add_right le_rfl
  simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_add,
    ENNReal.toReal_sub_of_le hp ENNReal.one_ne_top,
    ENNReal.toReal_sub_of_le hsmall ENNReal.one_ne_top, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_natCast, hpReal]
  norm_num [treeHeight]

open Generic.DeterministicSigning in
theorem memoize_oneRequestMain (finish : Option Generic.Signature → ChainIndex × Digest → Generic.Forgery) :
    Generic.DeterministicSigning.memoize (oneRequestMain finish Generic.Attack.mutationChoice) ∅ = oneRequestMain finish Generic.Attack.mutationChoice := by
  unfold oneRequestMain
  rw [Generic.DeterministicSigning.memoize_request]
  simp only [QueryCache.empty_apply, bind_pure_comp, Generic.DeterministicSigning.memoize_map, memoize_liftPrivateSamples]

theorem memoAdversary_oneRequest (finish : Option Generic.Signature → ChainIndex × Digest → Generic.Forgery) :
    Generic.Seeded.memoAdversary (oneRequestAdversary finish) = oneRequestAdversary finish := by
  unfold Generic.Seeded.memoAdversary oneRequestAdversary
  congr 1
  funext publicKey
  exact memoize_oneRequestMain finish

theorem oneRequest_direct_zero (finish : Option Generic.Signature → ChainIndex × Digest → Generic.Forgery) :
    Generic.Direct.IsDirectQueryBound (oneRequestAdversary finish) 0 := by
  intro publicKey
  change (oneRequestMain finish Generic.Attack.mutationChoice).IsQueryBoundP _ _
  unfold oneRequestMain
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (Generic.Direct.not_isDirectHashQuery_sign _), fun answer => ?_⟩
  simpa only [Generic.Direct.not_isDirectHashQuery_sign, if_false, Nat.sub_zero, bind_pure_comp,
    OracleComp.isQueryBoundP_map_iff] using
      Generic.Attack.liftPrivateSamples_zero Generic.Attack.mutationChoice _ Generic.Direct.not_isDirectHashQuery_uniform

theorem oneRequest_seeded_advantage_eq_reference
    (finish : Option Generic.Signature → ChainIndex × Digest → Generic.Forgery) :
    Generic.forgeAdvantage Generic.Seeded.scheme (oneRequestAdversary finish) =
      Generic.forgeAdvantage Generic.Concrete.scheme (oneRequestAdversary finish) := by
  unfold Generic.forgeAdvantage
  apply probOutput_congr rfl
  calc
    _ = evalDist (Generic.Seeded.independentTableGame (oneRequestAdversary finish)) :=
      Generic.Seeded.evalDist_deterministic_eq_table_of_direct_zero _ (oneRequest_direct_zero finish)
    _ = _ := by
      simpa only [memoAdversary_oneRequest] using
        Generic.Seeded.evalDist_independentTableGame_memo (oneRequestAdversary finish)

theorem fresh_seeded_advantage_exceeds_123 :
    (1 : ℝ≥0∞) / ((2 ^ 123 : ℕ) : ℝ≥0∞) < Generic.forgeAdvantage Generic.Seeded.scheme freshAdversary := by
  rw [oneRequest_seeded_advantage_eq_reference]
  exact lt_of_lt_of_le fresh_lower_exceeds_123 fresh_reference_advantage_lower

/-- info: 'XmssSecurity.Checksum.Attack.fresh_seeded_advantage_exceeds_123' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fresh_seeded_advantage_exceeds_123

end XmssSecurity.Checksum.Attack
