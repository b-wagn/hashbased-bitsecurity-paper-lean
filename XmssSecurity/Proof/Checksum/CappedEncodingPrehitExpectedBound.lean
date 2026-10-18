import XmssSecurity.Proof.Checksum.CappedEncodingExpectedBound
import XmssSecurity.Proof.Checksum.CappedEncodingPrehitProbability

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Checksum

set_option maxRecDepth 100000

theorem cachedEncodingInputCount_romImpl_step_le
    (parameter : PublicParameter) (input : OracleWorld.Domain)
    (initialCache : QueryCache HashSpec)
    (result : OracleWorld.Range input × QueryCache HashSpec)
    (hresult : result ∈ support ((romImpl input).run initialCache)) :
    cachedEncodingInputCount result.2 parameter ≤
      cachedEncodingInputCount initialCache parameter +
        if CappedEncodingMonitor.IsEncodingHashQuery parameter input then 1 else 0 := by
  cases input with
  | inl uniformIndex =>
      have hrun :
          (unifFwdImpl HashSpec uniformIndex).run initialCache =
            (fun sample => (sample, initialCache)) <$>
              (liftM (unifSpec.query uniformIndex) : ProbComp _) := by
        simpa [simulateQ_query] using
          (unifFwdImpl.simulateQ_run
            (hashSpec := HashSpec)
            (liftM (unifSpec.query uniformIndex) : ProbComp _) initialCache)
      change result ∈ support
        ((unifFwdImpl HashSpec uniformIndex).run initialCache) at hresult
      rw [hrun, support_map] at hresult
      obtain ⟨sampled, _hsampled, heq⟩ := hresult
      have hcache : initialCache = result.2 := congrArg Prod.snd heq
      rw [← hcache]
      simp [CappedEncodingMonitor.IsEncodingHashQuery]
  | inr hashInput =>
      rcases result with ⟨returned, finalCache⟩
      change HashOutput at returned
      change (returned, finalCache) ∈
        support ((randomOracle (spec := HashSpec) hashInput).run initialCache) at hresult
      cases hcache : initialCache hashInput with
      | none =>
          rw [QueryImpl.withCaching_run_none _ hcache, support_map,
            Set.mem_image] at hresult
          obtain ⟨sampled, _hsampled, heq⟩ := hresult
          have hfinal : finalCache = initialCache.cacheQuery hashInput sampled :=
            (congrArg Prod.snd heq).symm
          change cachedEncodingInputCount finalCache parameter ≤ _
          rw [hfinal]
          have hindicator :
              (if CappedEncodingMonitor.IsEncodingHashQuery parameter (.inr hashInput)
                then (1 : ℝ≥0∞) else 0) =
              if (encodingInputLeafIndex? parameter hashInput).isSome then 1 else 0 := by
            by_cases hencoding : (encodingInputLeafIndex? parameter hashInput).isSome
            · simp [CappedEncodingMonitor.IsEncodingHashQuery_inr, hencoding]
            · simp [CappedEncodingMonitor.IsEncodingHashQuery_inr, hencoding]
          rw [hindicator]
          exact cachedEncodingInputCount_cacheQuery_le initialCache parameter hashInput sampled
      | some cached =>
          rw [QueryImpl.withCaching_run_some _ hcache, support_pure,
            Set.mem_singleton_iff] at hresult
          have hfinal : finalCache = initialCache := congrArg Prod.snd hresult
          change cachedEncodingInputCount finalCache parameter ≤ _
          rw [hfinal]
          simp [CappedEncodingMonitor.IsEncodingHashQuery]

theorem Concrete.keygen_cachedEncodingInputCount_eq_zero
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    cachedEncodingInputCount keyResult.2 keyResult.1.2.parameter = 0 := by
  unfold cachedEncodingInputCount
  have hempty : cachedEncodingInputSet keyResult.2 keyResult.1.2.parameter = ∅ := by
    ext entry
    simp only [cachedEncodingInputSet, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hcache
    change keyResult.2 entry.1 = some entry.2 at hcache
    cases hleafIndex : encodingInputLeafIndex? keyResult.1.2.parameter entry.1 with
    | none => simp
    | some leafIndex =>
        intro _hisSome
        obtain ⟨payload, hinput⟩ :=
          exists_encodingInput_of_encodingInputLeafIndex?_eq_some
            keyResult.1.2.parameter entry.1 leafIndex hleafIndex
        have hmem' : keyResult ∈ support
            ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
          simpa [Concrete.scheme] using hmem
        have hnone := Concrete.precomputedKeygen_cache_none_encodingInput
          keyResult hmem' leafIndex payload
        rw [hinput] at hnone
        rw [hnone] at hcache
        exact (Option.some_ne_none entry.2) hcache.symm
  rw [hempty]
  simp

end XmssSecurity.Checksum
