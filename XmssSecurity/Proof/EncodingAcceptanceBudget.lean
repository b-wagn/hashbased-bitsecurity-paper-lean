import XmssSecurity.Proof.ExpectedStateEvent
import XmssSecurity.Proof.EncodingProbability
import XmssSecurity.Proof.RandomOracle
import XmssSecurity.Proof.CappedEncodingExpectedBound
import XmssSecurity.Proof.KeygenCache
import XmssSecurity.Proof.PrecomputedBoundedSignCache

/-! Accepted encodings consume an expected encoding-query budget. In particular, cached
replies cannot create a new accepted encoding in an initially rejecting cache. -/

open OracleSpec OracleComp ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity

theorem Checksum.probEvent_validDigest_uniformHashOutput :
    Pr[fun output : HashOutput => ValidDigest (truncateHash output) | $ᵗ HashOutput] =
      acceptanceProbability := by
  change Pr[ValidDigest ∘ truncateHash | $ᵗ HashOutput] = _
  rw [← probEvent_map, probEvent_def, Rom.evalDist_truncate_uniformHashOutput,
    ← probEvent_def]
  exact probEvent_validDigest_uniform

def HasAcceptedEncoding (parameter : PublicParameter) (cache : QueryCache HashSpec) : Prop :=
  ∃ input output, cache input = some output ∧
    (encodingInputLeafIndex? parameter input).isSome ∧ Checksum.ValidDigest (truncateHash output)

noncomputable instance (parameter : PublicParameter) : DecidablePred (HasAcceptedEncoding parameter) :=
  Classical.decPred _

theorem hasAcceptedEncoding_cacheQuery_iff
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (hcache : ¬HasAcceptedEncoding parameter cache) :
    HasAcceptedEncoding parameter (cache.cacheQuery input output) ↔
      (encodingInputLeafIndex? parameter input).isSome ∧ Checksum.ValidDigest (truncateHash output) := by
  constructor
  · rintro ⟨candidate, answer, hanswer, hencoding, hvalid⟩
    by_cases heq : candidate = input
    · subst candidate
      rw [QueryCache.cacheQuery_self] at hanswer
      cases hanswer
      exact ⟨hencoding, hvalid⟩
    · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hanswer
      exact (hcache ⟨candidate, answer, hanswer, hencoding, hvalid⟩).elim
  · rintro ⟨hencoding, hvalid⟩
    exact ⟨input, output, QueryCache.cacheQuery_self _ _ _, hencoding, hvalid⟩

theorem hasAcceptedEncoding_romImpl_step_le
    (parameter : PublicParameter) (input : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (hcache : ¬HasAcceptedEncoding parameter cache) :
    Pr[fun result => HasAcceptedEncoding parameter result.2 | (romImpl input).run cache] ≤
      if CappedEncodingMonitor.IsEncodingHashQuery parameter input
        then Checksum.acceptanceProbability else 0 := by
  classical
  cases input with
  | inl uniformIndex =>
      have hrun : (unifFwdImpl HashSpec uniformIndex).run cache =
          (fun sample => (sample, cache)) <$>
            (liftM (unifSpec.query uniformIndex) : ProbComp _) := by
        simpa [simulateQ_query] using
          (unifFwdImpl.simulateQ_run (hashSpec := HashSpec)
            (liftM (unifSpec.query uniformIndex) : ProbComp _) cache)
      change Pr[fun result => HasAcceptedEncoding parameter result.2 |
        (unifFwdImpl HashSpec uniformIndex).run cache] ≤ _
      rw [hrun, probEvent_map]
      simp [hcache, CappedEncodingMonitor.IsEncodingHashQuery]
  | inr hashInput =>
      change Pr[fun result => HasAcceptedEncoding parameter result.2 |
        (randomOracle (spec := HashSpec) hashInput).run cache] ≤ _
      cases hentry : cache hashInput with
      | some output =>
          rw [QueryImpl.withCaching_run_some _ hentry]
          simp [hcache]
      | none =>
          rw [randomOracle_run_none_eq_uniformHashOutput _ _ hentry, probEvent_map]
          change Pr[fun output => HasAcceptedEncoding parameter
            (cache.cacheQuery hashInput output) | uniformHashOutput] ≤ _
          simp only [hasAcceptedEncoding_cacheQuery_iff _ _ _ _ hcache]
          by_cases hencoding : (encodingInputLeafIndex? parameter hashInput).isSome
          · simp only [hencoding, true_and, CappedEncodingMonitor.IsEncodingHashQuery_inr,
              if_true, uniformHashOutput]
            exact Checksum.probEvent_validDigest_uniformHashOutput.le
          · simp [hencoding, CappedEncodingMonitor.IsEncodingHashQuery_inr]

/-- This bound counts actual encoding queries, including adaptive honest signing attempts. -/
theorem probEvent_hasAcceptedEncoding_le_expectedQueries
    (parameter : PublicParameter) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hcache : ¬HasAcceptedEncoding parameter cache) :
    Pr[fun result => HasAcceptedEncoding parameter result.2 |
      (simulateQ romImpl computation).run cache] ≤
      Checksum.acceptanceProbability * expectedSimulatedQueryCount romImpl
        (CappedEncodingMonitor.IsEncodingHashQuery parameter) computation cache := by
  simpa only [if_neg hcache, zero_add] using
    probEvent_state_le_initial_add_expectedQueryCount romImpl
      (CappedEncodingMonitor.IsEncodingHashQuery parameter) (HasAcceptedEncoding parameter)
      Checksum.acceptanceProbability (hasAcceptedEncoding_romImpl_step_le parameter)
      computation cache

theorem not_hasAcceptedEncoding_of_no_encodingInputs
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hempty : ∀ leafIndex payload, cache (Concrete.CacheView.encodingInput parameter
      leafIndex payload) = none) : ¬HasAcceptedEncoding parameter cache := by
  rintro ⟨input, output, hcached, hencoding, _⟩
  cases hleaf : encodingInputLeafIndex? parameter input with
  | none => simp [hleaf] at hencoding
  | some leafIndex =>
      obtain ⟨payload, rfl⟩ :=
        exists_encodingInput_of_encodingInputLeafIndex?_eq_some parameter input leafIndex hleaf
      rw [hempty] at hcached
      contradiction

theorem Concrete.keygen_no_acceptedEncoding
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.keygen).run ∅)) :
    ¬HasAcceptedEncoding keyResult.1.2.parameter keyResult.2 :=
  not_hasAcceptedEncoding_of_no_encodingInputs _ _ (keygen_cache_none_encodingInput keyResult hkey)

theorem Concrete.precomputedKeygen_no_acceptedEncoding
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.precomputedKeygen).run ∅)) :
    ¬HasAcceptedEncoding keyResult.1.2.parameter keyResult.2 :=
  not_hasAcceptedEncoding_of_no_encodingInputs _ _
    (precomputedKeygen_cache_none_encodingInput keyResult hkey)

theorem hasAcceptedEncoding_of_decode
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (message : Message) (randomness : Randomness) (encoding : Encoding)
    (hdecode : Concrete.CacheView.decodedEncoding cache parameter leafIndex (message, randomness) =
        some encoding) : HasAcceptedEncoding parameter cache := by
  obtain ⟨output, hcached⟩ := Concrete.CacheView.encodingInput_cached_of_decode_some cache
    parameter leafIndex message randomness encoding hdecode
  refine ⟨Concrete.CacheView.encodingInput parameter leafIndex (message, randomness),
    output, hcached, by simp, encoding, ?_⟩
  simpa [Concrete.CacheView.encodingHash, Concrete.CacheView.digestAt, hcached] using hdecode

theorem Concrete.precomputedCappedSign_hasAcceptedEncoding_of_success
    (secretKey : SecretKey) (request : SignRequest)
    (initialCache finalCache : QueryCache HashSpec) (signature : Signature)
    (hmem : (some signature, finalCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign secretKey request.epoch request.message)).run initialCache)) :
    HasAcceptedEncoding secretKey.parameter finalCache := by
  obtain ⟨encoding, hdecode⟩ := precomputedCappedSign_success_decode secretKey request
    initialCache finalCache signature hmem
  exact hasAcceptedEncoding_of_decode _ _ _ _ _ _ hdecode

theorem Concrete.precomputedCappedSign_success_le_expectedEncodingQueries
    (secretKey : SecretKey) (request : SignRequest) (cache : QueryCache HashSpec)
    (hcache : ¬HasAcceptedEncoding secretKey.parameter cache) :
    Pr[fun result : Option Signature × QueryCache HashSpec => result.1 ≠ none |
      (simulateQ romImpl (precomputedCappedSign secretKey request.epoch request.message)).run cache] ≤
      Checksum.acceptanceProbability * expectedSimulatedQueryCount romImpl
        (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter)
        (precomputedCappedSign secretKey request.epoch request.message) cache := by
  apply le_trans _ (probEvent_hasAcceptedEncoding_le_expectedQueries _ _ _ hcache)
  apply probEvent_mono
  rintro ⟨result, finalCache⟩ hresult hsuccess
  cases result with
  | none => exact (hsuccess rfl).elim
  | some signature =>
      exact precomputedCappedSign_hasAcceptedEncoding_of_success secretKey request cache
        finalCache signature hresult

/-- info: 'XmssSecurity.probEvent_hasAcceptedEncoding_le_expectedQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_hasAcceptedEncoding_le_expectedQueries

/-- info: 'XmssSecurity.Concrete.precomputedCappedSign_success_le_expectedEncodingQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Concrete.precomputedCappedSign_success_le_expectedEncodingQueries

end XmssSecurity
