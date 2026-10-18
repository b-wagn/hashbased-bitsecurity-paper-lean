import XmssSecurity.Proof.Common.ExpectedStateEvent
import XmssSecurity.Proof.TargetSum.EncodingProbability
import XmssSecurity.Proof.Generic.RandomOracle
import XmssSecurity.Proof.Generic.CappedEncodingExpectedBound
import XmssSecurity.Proof.Generic.KeygenCache
import XmssSecurity.Proof.Generic.PrecomputedBoundedSignCache
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.CacheDecode
/-! Accepted encodings consume an expected encoding-query budget. In particular, cached
replies cannot create a new accepted encoding in an initially rejecting cache. -/

open OracleSpec OracleComp ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum

theorem TargetSum.probEvent_validDigest_uniformHashOutput :
    Pr[fun output : HashOutput => Generic.Code.ValidDigest (Generic.truncateHash output) | $ᵗ HashOutput] =
      acceptanceProbability := by
  change Pr[Generic.Code.ValidDigest ∘ Generic.truncateHash | $ᵗ HashOutput] = _
  rw [← probEvent_map, probEvent_def, Generic.Rom.evalDist_truncate_uniformHashOutput,
    ← probEvent_def]
  exact probEvent_validDigest_uniform

def HasAcceptedEncoding (parameter : PublicParameter) (cache : QueryCache HashSpec) : Prop :=
  ∃ input output, cache input = some output ∧
    (Generic.encodingInputLeafIndex? parameter input).isSome ∧ Generic.Code.ValidDigest (Generic.truncateHash output)

noncomputable instance (parameter : PublicParameter) : DecidablePred (HasAcceptedEncoding parameter) :=
  Classical.decPred _

theorem hasAcceptedEncoding_cacheQuery_iff
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (hcache : ¬HasAcceptedEncoding parameter cache) :
    HasAcceptedEncoding parameter (cache.cacheQuery input output) ↔
      (Generic.encodingInputLeafIndex? parameter input).isSome ∧ Generic.Code.ValidDigest (Generic.truncateHash output) := by
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
    Pr[fun result => HasAcceptedEncoding parameter result.2 | (Generic.romImpl input).run cache] ≤
      if Generic.CappedEncodingMonitor.IsEncodingHashQuery parameter input
        then TargetSum.acceptanceProbability else 0 := by
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
      simp [hcache, Generic.CappedEncodingMonitor.IsEncodingHashQuery]
  | inr hashInput =>
      change Pr[fun result => HasAcceptedEncoding parameter result.2 |
        (randomOracle (spec := HashSpec) hashInput).run cache] ≤ _
      cases hentry : cache hashInput with
      | some output =>
          rw [QueryImpl.withCaching_run_some _ hentry]
          simp [hcache]
      | none =>
          rw [Generic.randomOracle_run_none_eq_uniformHashOutput _ _ hentry, probEvent_map]
          change Pr[fun output => HasAcceptedEncoding parameter
            (cache.cacheQuery hashInput output) | Generic.uniformHashOutput] ≤ _
          simp only [hasAcceptedEncoding_cacheQuery_iff _ _ _ _ hcache]
          by_cases hencoding : (Generic.encodingInputLeafIndex? parameter hashInput).isSome
          · simp only [hencoding, true_and, Generic.CappedEncodingMonitor.IsEncodingHashQuery_inr,
              if_true, Generic.uniformHashOutput]
            exact TargetSum.probEvent_validDigest_uniformHashOutput.le
          · simp [hencoding, Generic.CappedEncodingMonitor.IsEncodingHashQuery_inr]

/-- This bound counts actual encoding queries, including adaptive honest signing attempts. -/
theorem probEvent_hasAcceptedEncoding_le_expectedQueries
    (parameter : PublicParameter) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hcache : ¬HasAcceptedEncoding parameter cache) :
    Pr[fun result => HasAcceptedEncoding parameter result.2 |
      (simulateQ Generic.romImpl computation).run cache] ≤
      TargetSum.acceptanceProbability * expectedSimulatedQueryCount Generic.romImpl
        (Generic.CappedEncodingMonitor.IsEncodingHashQuery parameter) computation cache := by
  simpa only [if_neg hcache, zero_add] using
    probEvent_state_le_initial_add_expectedQueryCount Generic.romImpl
      (Generic.CappedEncodingMonitor.IsEncodingHashQuery parameter) (HasAcceptedEncoding parameter)
      TargetSum.acceptanceProbability (hasAcceptedEncoding_romImpl_step_le parameter)
      computation cache

theorem not_hasAcceptedEncoding_of_no_encodingInputs
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hempty : ∀ leafIndex payload, cache (Generic.Concrete.CacheView.encodingInput parameter
      leafIndex payload) = none) : ¬HasAcceptedEncoding parameter cache := by
  rintro ⟨input, output, hcached, hencoding, _⟩
  cases hleaf : Generic.encodingInputLeafIndex? parameter input with
  | none => simp [hleaf] at hencoding
  | some leafIndex =>
      obtain ⟨payload, rfl⟩ :=
        Generic.exists_encodingInput_of_encodingInputLeafIndex?_eq_some parameter input leafIndex hleaf
      rw [hempty] at hcached
      contradiction

theorem Concrete.precomputedKeygen_no_acceptedEncoding
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.precomputedKeygen).run ∅)) :
    ¬HasAcceptedEncoding keyResult.1.2.parameter keyResult.2 :=
  not_hasAcceptedEncoding_of_no_encodingInputs _ _
    (Generic.Concrete.precomputedKeygen_cache_none_encodingInput keyResult hkey)

theorem hasAcceptedEncoding_of_decode
    (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (message : Message) (randomness : Randomness) (encoding : Encoding)
    (hdecode : Generic.Concrete.CacheView.decodedEncoding cache parameter leafIndex
      (message, randomness) = some encoding) : HasAcceptedEncoding parameter cache := by
  obtain ⟨output, hcached⟩ := Generic.Concrete.CacheView.encodingInput_cached_of_decode_some cache
    parameter leafIndex message randomness encoding hdecode
  refine ⟨Generic.Concrete.CacheView.encodingInput parameter leafIndex (message, randomness),
    output, hcached, by simp, encoding, ?_⟩
  simpa [Generic.Concrete.CacheView.encodingHash, Generic.Concrete.CacheView.digestAt, hcached] using
    Generic.Concrete.CacheView.decodeDigest_of_decodedEncoding hdecode

/-- info: 'XmssSecurity.TargetSum.probEvent_hasAcceptedEncoding_le_expectedQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_hasAcceptedEncoding_le_expectedQueries

end XmssSecurity.TargetSum
