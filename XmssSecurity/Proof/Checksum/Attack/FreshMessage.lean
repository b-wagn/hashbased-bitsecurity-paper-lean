import XmssSecurity.Proof.Checksum.Attack.OneRequest
import XmssSecurity.Proof.Checksum.Attack.MutationGame
import XmssSecurity.Proof.Common.EUFCMA.Reduction
import XmssSecurity.Proof.Checksum.Attack.MutationVerification
import XmssSecurity.Proof.Checksum.ConcreteQueryBound
import XmssSecurity.Proof.Checksum.Attack.ChainMutationSeeded

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

theorem freshMessage_ne_request : freshMessage ≠ mutationRequest.message := by decide

/-- Submit the returned signature for `freshMessage`; the private samples are not used. -/
def freshMessageForgery (answer : Option Signature) (_choice : ChainIndex × Digest) : Forgery :=
  ⟨mutationRequest.epoch, freshMessage, answer.getD fallbackSignature⟩

noncomputable abbrev freshAdversary : Adversary := oneRequestAdversary freshMessageForgery

theorem freshMessage_request_fresh (answer : Option Signature) (choice : ChainIndex × Digest) :
    ¬ EUFCMA.SigningTranscript.ContainsRequest [⟨mutationRequest, answer⟩]
      (freshMessageForgery answer choice) := by
  simp only [EUFCMA.SigningTranscript.ContainsRequest, List.mem_singleton, exists_eq_left]
  intro heq
  exact freshMessage_ne_request
    (congrArg (fun request : XmssSecurity.Checksum.SignRequest => request.message) heq).symm

theorem freshMessage_not_contains (answer : Option Signature) (choice : ChainIndex × Digest) :
    ¬ SigningTranscript.Contains [⟨mutationRequest, answer⟩] (freshMessageForgery answer choice) :=
  fun h => freshMessage_request_fresh answer choice (EUFCMA.containsRequest_of_contains _ _ h)

theorem oneRequest_gameRest {Key : Type} (finish : Option Signature → ChainIndex × Digest → Forgery)
    (scheme : Scheme Key) (publicKey : PublicKey) (secretKey : Key) :
    Seeded.gameRest scheme (oneRequestAdversary finish) publicKey secretKey = (do
      let answer ← scheme.sign secretKey mutationRequest.epoch mutationRequest.message
      let choice ← worldPrivateSamples mutationChoice
      let forgery := finish answer choice
      let verified ← scheme.verify publicKey forgery.epoch forgery.message forgery.signature
      return decide (SigningTranscript.Valid [⟨mutationRequest, answer⟩] ∧
        ¬SigningTranscript.Contains [⟨mutationRequest, answer⟩] forgery) && verified) := by
  unfold Seeded.gameRest
  change (do
    let result ← (simulateQ (forwardOracles + signingOracle scheme secretKey)
      (oneRequestMain finish mutationChoice)).run
    let verified ← scheme.verify publicKey result.1.epoch result.1.message result.1.signature
    return decide (SigningTranscript.Valid result.2 ∧ ¬SigningTranscript.Contains result.2 result.1) && verified) = _
  rw [show oneRequestMain finish mutationChoice = (do
      let answer ← liftM ((OracleWorld + SigningSpec).query (.inr mutationRequest))
      let choice ← liftPrivateSamples mutationChoice
      pure (finish answer choice)) from rfl,
    oneRequestSamples_logged scheme secretKey mutationRequest mutationChoice finish]
  simp only [bind_assoc, pure_bind]

/-- The verification of the fresh forgery, from the signer's answer. -/
def freshOutcome (publicKey : PublicKey) (answer : Option Signature) : OracleComp HashSpec Bool := do
  let verified ← verify publicKey mutationRequest.epoch freshMessage (answer.getD fallbackSignature)
  return decide (SigningTranscript.Valid [⟨mutationRequest, answer⟩]) && verified

theorem fresh_referenceRest_run (publicKey : PublicKey) (secretKey : SecretKey)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (Seeded.gameRest Concrete.scheme freshAdversary publicKey secretKey)).run cache = (do
      let result ← (simulateQ romImpl
        (precomputedCappedSign secretKey mutationRequest.epoch mutationRequest.message)).run cache
      let _choice ← mutationChoice
      (simulateQ randomOracle (freshOutcome publicKey result.1)).run result.2) := by
  rw [oneRequest_gameRest, simulateQ_bind, StateT.run_bind]
  apply bind_congr
  rintro ⟨answer, signCache⟩
  rw [simulateQ_bind, StateT.run_bind, worldPrivateSamples_run, bind_map_left]
  apply bind_congr
  intro choice
  have hroute : simulateQ romImpl
      (liftM (verify publicKey mutationRequest.epoch freshMessage (answer.getD fallbackSignature) :
          OracleComp HashSpec Bool)) =
      simulateQ randomOracle (verify publicKey mutationRequest.epoch freshMessage
        (answer.getD fallbackSignature) : OracleComp HashSpec Bool) :=
    QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) _
  unfold freshOutcome
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, StateT.run_bind]
  change (simulateQ romImpl (liftM (verify publicKey mutationRequest.epoch freshMessage
      (answer.getD fallbackSignature) : OracleComp HashSpec Bool))).run signCache >>= _ = _
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
      exact CacheReplay.cache_none_of_zero_query_bound computation target initialCache
        finalCache result hbound hinitial hmem
  | some output =>
      exact CacheReplay.randomOracle_cache_le computation initialCache
        (result, finalCache) hmem hinitial

/-- Recovering endpoints makes no query outside the chain addresses. -/
theorem recoverEndpoints_queryBound_zero_of_not_chain (parameter : PublicParameter)
    (leafIndex : LeafIndex) (encoding : Encoding) (signature : Signature) (domain : HashDomain)
    (hdomain : ∀ chain step, HashDomain.chain leafIndex chain step ≠ domain) (payload : HashInput) :
    (recoverEndpoints parameter leafIndex encoding signature :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP
        (· = tweakableHashInput parameter domain payload) 0 := by
  apply OracleComp.IsQueryBoundP.of_imp (p' := AtHashAddress parameter domain)
  · rintro _ rfl
    exact (atHashAddress_tweakableHashInput_iff parameter domain domain payload).mpr rfl
  · unfold recoverEndpoints
    exact Concrete.sequenceFin_queryBound_zero _ _ fun chain =>
      Concrete.chainWalk_queryBound_zero_of_avoids parameter leafIndex chain _ _ _ domain
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
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (signature : Signature) (finalCache : QueryCache HashSpec)
    (hsign : (some signature, finalCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign keyResult.1.2 mutationRequest.epoch mutationRequest.message)).run
        keyResult.2))
    (message : Message) :
    freshPathLower ≤ Pr[fun result => result.1 = true |
      (simulateQ randomOracle (verify keyResult.1.1 mutationRequest.epoch message signature :
        OracleComp HashSpec Bool)).run finalCache] := by
  classical
  obtain ⟨encoding, _hdecode, hsignature⟩ :=
    signing_success_replay_at_keygen keyResult hkey mutationRequest signature finalCache hsign
  have hparameter := Deciding.keygen_publicKey_parameter_eq keyResult hkey
  have hle := xmssRom_cache_le _ keyResult.2 (some signature, finalCache) hsign
  let leafIndex := mutationRequest.epoch
  let chain : ChainIndex := ⟨0, by decide⟩
  let inputs := mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding
    signature.randomness
  let honest := mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain (encoding chain)
  let start := mutationChainSteps (encoding chain) + 1
  let honestEndpoints := CacheReplay.oneTimePublicKey keyResult.2 keyResult.1.2.parameter
    keyResult.1.2.chainStart leafIndex
  have hagree := mutationReplayInputs_preserved_by_signing keyResult.2 keyResult.1.2 leafIndex
    chain encoding signature.randomness leafIndex mutationRequest.message (some signature)
    finalCache hsign
  -- Split the verification into the encoding, the endpoints, the leaf, and the path.
  rw [verify_eq_decode]
  simp only [Checksum.decodeDigest]
  rw [simulateQ_bind, StateT.run_bind]
  apply le_probEvent_bind_of_forall
  rintro ⟨digest, digestCache⟩ hdigest
  rw [simulateQ_bind, StateT.run_bind]
  apply le_probEvent_bind_of_forall
  rintro ⟨endpoints, endpointsCache⟩ hendpoints
  -- Neither the encoding hash nor the chain walks touch the leaf and node addresses.
  have hpreserve : ∀ (domain : HashDomain), (∀ leaf, domain ≠ .encoding leaf) →
      (∀ leaf chain step, HashDomain.chain leaf chain step ≠ domain) →
      ∀ payload, endpointsCache (tweakableHashInput keyResult.1.1.parameter domain payload) =
        finalCache (tweakableHashInput keyResult.1.1.parameter domain payload) := by
    intro domain hencoding hchain payload
    rw [cache_eq_of_zero_query_bound _ _ digestCache endpointsCache endpoints
      (recoverEndpoints_queryBound_zero_of_not_chain _ _ _ _ domain
        (fun c s => hchain leafIndex c s) payload) hendpoints]
    refine cache_eq_of_zero_query_bound _ _ finalCache digestCache digest ?_ hdigest
    apply Concrete.encodingHash_queryBound_zero_at_other_input
    intro heq
    exact hencoding leafIndex (domain_eq_of_tweakableHashInput_eq _ heq).symm
  have hnode : ∀ i, start ≤ i → i < start + treeHeight → ∀ value,
      endpointsCache (inputs i value) = keyResult.2 (inputs i value) := by
    intro i hi hi' value
    have hlevel : i - start < treeHeight := by omega
    have hi'' : i = mutationChainSteps (encoding chain) + 1 + (i - start) := by omega
    rw [← hagree i (by omega) value]
    change endpointsCache (mutationPathInput _ _ _ _ _ _ i value) =
      finalCache (mutationPathInput _ _ _ _ _ _ i value)
    rw [hi'', mutationPathInput_node _ _ _ _ _ _ _ hlevel, ← hparameter]
    exact hpreserve _ (by simp) (by simp) _
  -- The authentication path is the node part of the mutation path.
  have hpath : ∀ leaf, (verifyAfterLeaf keyResult.1.1 leafIndex signature leaf :
      OracleComp HashSpec Bool) =
      (fun root => decide (root = keyResult.1.1.root)) <$> Rom.hashPath inputs start treeHeight leaf := by
    intro leaf
    have h := mutationPath_authentication keyResult.1.2.parameter leafIndex chain (encoding chain)
      (CacheReplay.signWithEncoding keyResult.2 keyResult.1.2 leafIndex signature.randomness encoding)
      honestEndpoints treeHeight le_rfl leaf
    unfold verifyAfterLeaf
    rw [hparameter]
    conv_lhs => rw [hsignature]
    rw [← h, map_eq_bind_pure_comp]
    rfl
  have hhonest : ∀ i, start ≤ i → i < start + treeHeight →
      ∃ output, endpointsCache (inputs i (honest i)) = some output ∧
        truncateHash output = honest (i + 1) := by
    intro i hi hi'
    rw [hnode i hi hi']
    exact mutationReplayInputs_honest keyResult hkey leafIndex chain encoding signature.randomness
      i (by omega)
  have hfresh : ∀ i, start ≤ i → i < start + treeHeight → ∀ other, other ≠ honest i →
      endpointsCache (inputs i other) = none := by
    intro i hi hi' other hne
    rw [hnode i hi hi']
    exact mutationReplayInputs_fresh keyResult hkey leafIndex chain encoding signature.randomness
      i (by omega) other hne
  have hseparate : ∀ i, start ≤ i → i < start + treeHeight →
      ∀ j, start ≤ j → j < start + treeHeight → i ≠ j → ∀ left right,
        inputs i left ≠ inputs j right := fun i _ hi j _ hj hne left right =>
    mutationPathInput_separate _ _ _ _ _ _ i j (by omega) (by omega) hne left right
  have hroot : honest (start + treeHeight) = keyResult.1.1.root :=
    mutationHonestValue_root keyResult hkey leafIndex chain (encoding chain)
  -- The leaf hash is one query at the leaf address.
  let leafInput := CacheView.leafInput keyResult.1.1.parameter leafIndex endpoints
  have hleafRun : ∀ cache : QueryCache HashSpec,
      (simulateQ randomOracle (do
        let leaf ← leafHash keyResult.1.1.parameter leafIndex endpoints
        verifyAfterLeaf keyResult.1.1 leafIndex signature leaf : OracleComp HashSpec Bool)).run cache =
      (randomOracle leafInput).run cache >>= fun result =>
        (simulateQ randomOracle (verifyAfterLeaf keyResult.1.1 leafIndex signature
          (truncateHash result.1) : OracleComp HashSpec Bool)).run result.2 := by
    intro cache
    simp only [leafHash, tweakableHash, oracleHash, bind_assoc, pure_bind, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind, HasQuery.instOfMonadLift_query]
    rfl
  rw [hleafRun]
  have hleafPreserved : endpointsCache leafInput = keyResult.2 leafInput := by
    rw [show leafInput = tweakableHashInput keyResult.1.1.parameter (.leaf leafIndex)
      (Concrete.leafPayload endpoints) from rfl, hpreserve _ (by simp) (by simp)]
    rw [precomputedCappedSign] at hsign
    refine precomputedSignBoundedAttempts_preserves_unqueriedInput signingAttemptLimit keyResult.1.2
      leafIndex mutationRequest.message _ (fun randomness heq => ?_) keyResult.2 finalCache
      (some signature) hsign
    rw [hparameter] at heq
    unfold CacheView.encodingInput at heq
    have := domain_eq_of_tweakableHashInput_eq _ heq
    simp at this
  -- The path from a leaf value, as a hash path.
  have hpathRun : ∀ (leaf : Digest) (cache : QueryCache HashSpec),
      Pr[fun result => result.1 = true |
        (simulateQ randomOracle (verifyAfterLeaf keyResult.1.1 leafIndex signature leaf :
          OracleComp HashSpec Bool)).run cache] =
      Pr[fun result : Digest × QueryCache HashSpec => result.1 = honest (start + treeHeight) |
        (simulateQ randomOracle (Rom.hashPath inputs start treeHeight leaf)).run cache] := by
    intro leaf cache
    rw [hpath, simulateQ_map, StateT.run_map, probEvent_map, hroot]
    simp [Function.comp_def]
  by_cases hhonestEndpoints : endpoints = honestEndpoints
  · -- The honest leaf is cached, and the honest path leads to the root.
    obtain ⟨output, houtput, htruncate⟩ := mutationReplayInputs_honest keyResult hkey leafIndex
      chain encoding signature.randomness (mutationChainSteps (encoding chain)) (by omega)
    have hinput : mutationReplayInputs keyResult.2 keyResult.1.2 leafIndex chain encoding
        signature.randomness (mutationChainSteps (encoding chain))
        (mutationHonestValue keyResult.2 keyResult.1.2 leafIndex chain (encoding chain)
          (mutationChainSteps (encoding chain))) = leafInput := by
      unfold mutationReplayInputs
      rw [mutationPathInput_leaf, mutationHonestValue_endpoint, Function.update_eq_self]
      simp only [leafInput, hhonestEndpoints, honestEndpoints, hparameter]
    rw [hinput] at houtput
    rw [QueryImpl.withCaching_run_some _ (hleafPreserved.trans houtput), pure_bind, hpathRun,
      htruncate, hashPath_run_honest inputs honest start treeHeight endpointsCache hhonest]
    simp only [probEvent_pure, if_true]
    exact freshPathLower_le_one
  · -- A fresh leaf meets the honest path with the remaining `33` hash calls.
    have hnone : endpointsCache leafInput = none := by
      rw [hleafPreserved]
      let oldKeyResult : (PublicKey × SecretKey) × QueryCache HashSpec :=
        ((keyResult.1.1, Concrete.erasePrecomputation keyResult.1.2), keyResult.2)
      have hold : oldKeyResult ∈ support ((simulateQ romImpl Concrete.keygen).run ∅) :=
        Concrete.precomputedKeygen_support_oldKeygen keyResult (by
          simpa only [Concrete.scheme] using hkey)
      rw [show leafInput = CacheView.leafInput keyResult.1.2.parameter leafIndex endpoints by
        simp only [leafInput, hparameter]]
      exact Concrete.keygen_cache_leafInput_eq_none_of_ne oldKeyResult hold leafIndex endpoints
        hhonestEndpoints
    rw [randomOracle_run_none_eq_uniformHashOutput _ _ hnone, uniformHashOutput, bind_map_left,
      probEvent_bind_eq_tsum]
    have hnodeInput : ∀ i, start ≤ i → i < start + treeHeight → ∀ value,
        inputs i value ≠ leafInput := by
      intro i hi hi' value heq
      have hlevel : i - start < treeHeight := by omega
      have hi'' : i = mutationChainSteps (encoding chain) + 1 + (i - start) := by omega
      change mutationPathInput _ _ _ _ _ _ i value = _ at heq
      rw [hi'', mutationPathInput_node _ _ _ _ _ _ _ hlevel] at heq
      simp only [CacheView.nodeInput, leafInput, CacheView.leafInput, hparameter] at heq
      have := domain_eq_of_tweakableHashInput_eq _ heq
      simp at this
    have hstep (output : HashOutput) :
        Pr[fun result => result.1 = true |
          (simulateQ randomOracle (verifyAfterLeaf keyResult.1.1 leafIndex signature
            (truncateHash output) : OracleComp HashSpec Bool)).run
              (endpointsCache.cacheQuery leafInput output)] =
          if truncateHash output = honest start then 1
          else 1 - (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ treeHeight := by
      rw [hpathRun]
      apply Rom.hashPath_hit_probability inputs honest start treeHeight (truncateHash output) _
        hseparate
      · intro i hi hi'
        obtain ⟨answer, hanswer, htarget⟩ := hhonest i hi hi'
        exact ⟨answer, by rw [QueryCache.cacheQuery_of_ne _ _ (hnodeInput i hi hi' _)]; exact hanswer,
          htarget⟩
      · intro i hi hi' other hother
        rw [QueryCache.cacheQuery_of_ne _ _ (hnodeInput i hi hi' _)]
        exact hfresh i hi hi' other hother
    simp_rw [hstep]
    have hhit : Pr[fun output : HashOutput => truncateHash output = honest start | $ᵗ HashOutput] =
        ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ := Rom.uniform_truncate_probability _
    have hmiss := Rom.uniform_truncate_miss_probability (honest start)
    apply le_of_eq
    calc
      freshPathLower = Pr[fun output : HashOutput => truncateHash output = honest start |
            $ᵗ HashOutput] * 1 +
          Pr[fun output : HashOutput => truncateHash output ≠ honest start | $ᵗ HashOutput] *
            (1 - (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ treeHeight) := by
        rw [hhit, hmiss, mul_one]
        rfl
      _ = _ := by
        rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right,
          ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
        apply tsum_congr
        intro output
        by_cases h : truncateHash output = honest start <;> simp [h]


/-! ### The advantage of the fresh-message adversary -/

theorem freshOutcome_some (publicKey : PublicKey) (signature : Signature) :
    freshOutcome publicKey (some signature) =
      (verify publicKey mutationRequest.epoch freshMessage signature : OracleComp HashSpec Bool) := by
  unfold freshOutcome
  simp only [chainMutation_transcript_valid, decide_true, Bool.true_and, Option.getD_some]
  rw [bind_pure]

theorem fresh_referenceRest_lower
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    (127 / 128 : ℝ≥0∞) * freshPathLower ≤
      Pr[fun result => result.1 = true |
        (simulateQ romImpl (Seeded.gameRest Concrete.scheme freshAdversary
          keyResult.1.1 keyResult.1.2)).run keyResult.2] := by
  let signing := (simulateQ romImpl
    (precomputedCappedSign keyResult.1.2 mutationRequest.epoch mutationRequest.message)).run keyResult.2
  rw [fresh_referenceRest_run]
  calc
    _ ≤ Pr[fun result => result.1 ≠ none | signing] * freshPathLower :=
      mul_le_mul_left (le_of_lt (precomputedCappedSign_success_after_keygen keyResult hkey
        mutationRequest.epoch mutationRequest.message)) _
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
    (127 / 128 : ℝ≥0∞) * freshPathLower ≤ forgeAdvantage Concrete.scheme freshAdversary := by
  let lower : ℝ≥0∞ := (127 / 128) * freshPathLower
  let keys := (simulateQ romImpl Concrete.scheme.keygen).run ∅
  have hmass : ∑' keyResult, Pr[= keyResult | keys] = 1 := tsum_probOutput_eq_one' (by simp)
  rw [forgeAdvantage_eq_gameWithCache]
  unfold gameWithCache gameCore
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
    Checksum.rejection_power_le p hp treeHeight
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

open DeterministicSigning in
theorem memoize_oneRequestMain (finish : Option Signature → ChainIndex × Digest → Forgery) :
    memoize (oneRequestMain finish mutationChoice) ∅ = oneRequestMain finish mutationChoice := by
  unfold oneRequestMain
  rw [memoize_request]
  simp only [QueryCache.empty_apply, bind_pure_comp, memoize_map, memoize_liftPrivateSamples]

theorem memoAdversary_oneRequest (finish : Option Signature → ChainIndex × Digest → Forgery) :
    Seeded.memoAdversary (oneRequestAdversary finish) = oneRequestAdversary finish := by
  unfold Seeded.memoAdversary oneRequestAdversary
  congr 1
  funext publicKey
  exact memoize_oneRequestMain finish

theorem oneRequest_direct_zero (finish : Option Signature → ChainIndex × Digest → Forgery) :
    Direct.IsDirectQueryBound (oneRequestAdversary finish) 0 := by
  intro publicKey
  change (oneRequestMain finish mutationChoice).IsQueryBoundP _ _
  unfold oneRequestMain
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (Direct.not_isDirectHashQuery_sign _), fun answer => ?_⟩
  simpa only [Direct.not_isDirectHashQuery_sign, if_false, Nat.sub_zero, bind_pure_comp,
    OracleComp.isQueryBoundP_map_iff] using
      liftPrivateSamples_zero mutationChoice _ Direct.not_isDirectHashQuery_uniform

theorem oneRequest_seeded_advantage_eq_reference
    (finish : Option Signature → ChainIndex × Digest → Forgery) :
    forgeAdvantage Seeded.scheme (oneRequestAdversary finish) =
      forgeAdvantage Concrete.scheme (oneRequestAdversary finish) := by
  unfold forgeAdvantage
  apply probOutput_congr rfl
  calc
    _ = evalDist (Seeded.independentTableGame (oneRequestAdversary finish)) :=
      Seeded.evalDist_deterministic_eq_table_of_direct_zero _ (oneRequest_direct_zero finish)
    _ = _ := by
      simpa only [memoAdversary_oneRequest] using
        Seeded.evalDist_independentTableGame_memo (oneRequestAdversary finish)

theorem fresh_seeded_advantage_exceeds_123 :
    (1 : ℝ≥0∞) / ((2 ^ 123 : ℕ) : ℝ≥0∞) < forgeAdvantage Seeded.scheme freshAdversary := by
  rw [oneRequest_seeded_advantage_eq_reference]
  exact lt_of_lt_of_le fresh_lower_exceeds_123 fresh_reference_advantage_lower

/-- info: 'XmssSecurity.Checksum.Attack.fresh_seeded_advantage_exceeds_123' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fresh_seeded_advantage_exceeds_123

end XmssSecurity.Checksum.Attack
