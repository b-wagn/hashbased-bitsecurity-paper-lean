import XmssSecurity.Proof.Direct.EncodingQueries

/-! The prehit loss charged only to direct encoding queries. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity
namespace Direct

def IsEncodingQueryBound (adversary : Adversary) (E : ℕ) : Prop :=
  ∀ publicKey, (adversary.main publicKey).IsQueryBoundP
    (IsDirectEncodingQuery publicKey.parameter) E

theorem cappedCacheTracedMappedAdversary_freshLeafPrehit_le_encoding
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (n : ℕ)
    (hbound : computation.IsQueryBoundP (IsDirectEncodingQuery secretKey.parameter) n)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace) :
    Pr[fun result : α × (QueryCache HashSpec × SigningCacheTrace) =>
      FreshLeafPrehit secretKey initialTrace result.2.2 |
      (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace)] ≤
      (signingAttemptLimit : ℝ≥0∞) *
        (untracedEncodingEntryCount initialCache secretKey.parameter initialTrace + n) *
        ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace n with
  | pure value =>
      refine le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
      intro result hresult hevent
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      obtain ⟨_hnodup, entry, hentry, hleafIndex, _hprehit⟩ := hevent
      apply hleafIndex
      rw [SigningCacheTrace.leafIndices, List.mem_map]
      exact ⟨entry, hentry, rfl⟩
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      obtain ⟨hpos, hnext⟩ := hbound
      rw [simulateQ_bind, StateT.run_bind]
      have hsupport : ∀ middle ∈ support
          ((simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
            (liftM ((OracleWorld + SigningSpec).query input))).run
              (initialCache, initialTrace)),
          middle ∈ support
            ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
              (initialCache, initialTrace)) := by
        intro middle hmiddle
        simpa [simulateQ_query] using hmiddle
      cases input with
      | inl worldInput =>
          cases worldInput with
          | inl uniformInput =>
              apply probEvent_bind_le_of_forall
              intro middle hmiddle
              have hmiddle' := hsupport middle hmiddle
              have htrace := cappedCacheTracedMappedAdversaryImpl_query_trace_update
                publicKey secretKey _ initialCache initialTrace middle hmiddle'
              have hcache := uniform_query_cache_eq publicKey secretKey uniformInput
                initialCache _ (cappedCacheTracedMappedAdversaryImpl_query_base
                  publicKey secretKey _ initialCache initialTrace middle hmiddle')
              have hstate : middle.2 = (initialCache, initialTrace) := by
                rw [Prod.ext_iff]
                exact ⟨hcache, by simpa [signingCacheTraceUpdate] using htrace⟩
              have hbound' := hnext middle.1
              simp only [IsDirectEncodingQuery, if_false] at hbound'
              have := ih middle.1 n hbound' initialCache initialTrace
              rw [hstate]
              exact this
          | inr hashInput =>
              by_cases hencoding : IsDirectEncodingQuery secretKey.parameter (.inl (.inr hashInput))
              · have hn : 0 < n := hpos.resolve_left (not_not.mpr hencoding)
                apply probEvent_bind_le_of_forall
                rintro ⟨answer, cache, trace⟩ hmiddle
                have hmiddle' := hsupport _ hmiddle
                have htrace := cappedCacheTracedMappedAdversaryImpl_query_trace_update
                  publicKey secretKey _ initialCache initialTrace _ hmiddle'
                obtain ⟨newEntry, hsubset⟩ := hash_query_cache_subset publicKey secretKey
                  hashInput initialCache (answer, cache)
                  (cappedCacheTracedMappedAdversaryImpl_query_base
                    publicKey secretKey _ initialCache initialTrace _ hmiddle')
                have htrace' : trace = initialTrace := by
                  simpa [signingCacheTraceUpdate] using htrace
                subst htrace'
                have hbound' := hnext answer
                rw [if_pos hencoding] at hbound'
                have hstep := ih answer (n - 1) hbound' cache trace
                have hpot := untracedEncodingEntryCount_le_of_subset_insert initialCache
                  cache secretKey.parameter trace newEntry hsubset
                refine hstep.trans (mul_le_mul' (mul_le_mul' le_rfl ?_) le_rfl)
                calc
                  untracedEncodingEntryCount cache secretKey.parameter trace +
                      ((n - 1 : ℕ) : ℝ≥0∞) ≤
                    untracedEncodingEntryCount initialCache secretKey.parameter trace +
                      1 + ((n - 1 : ℕ) : ℝ≥0∞) := by gcongr
                  _ = untracedEncodingEntryCount initialCache secretKey.parameter trace +
                      (n : ℝ≥0∞) := by
                    have hnum : (1 : ℝ≥0∞) + ((n - 1 : ℕ) : ℝ≥0∞) = n := by
                      rw [← Nat.cast_one, ← Nat.cast_add, show 1 + (n - 1) = n by omega]
                    rw [add_assoc, hnum]
              · apply probEvent_bind_le_of_forall
                rintro ⟨answer, cache, trace⟩ hmiddle
                have hmiddle' := hsupport _ hmiddle
                have htrace := cappedCacheTracedMappedAdversaryImpl_query_trace_update
                  publicKey secretKey _ initialCache initialTrace _ hmiddle'
                have htrace' : trace = initialTrace := by
                  simpa [signingCacheTraceUpdate] using htrace
                subst htrace'
                have hbase := cappedCacheTracedMappedAdversaryImpl_query_base
                  publicKey secretKey _ initialCache trace _ hmiddle'
                have hpot := untracedEncodingEntryCount_hash_query_le publicKey secretKey hashInput
                  initialCache trace (answer, cache) hbase
                rw [if_neg hencoding, add_zero] at hpot
                have hbound' := hnext answer
                rw [if_neg hencoding] at hbound'
                exact (ih answer n hbound' cache trace).trans
                  (mul_le_mul' (mul_le_mul' le_rfl (add_le_add hpot le_rfl)) le_rfl)
      | inr request =>
          have hbound' : ∀ answer, (next answer).IsQueryBoundP (IsDirectEncodingQuery secretKey.parameter) n := by
            intro answer
            simpa [IsDirectEncodingQuery] using hnext answer
          by_cases hfresh : request.epoch ∈ initialTrace.leafIndices
          · refine le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
            intro result hresult hevent
            rw [mem_support_bind_iff] at hresult
            obtain ⟨middle, hmiddle, hresult⟩ := hresult
            have hmiddle' := hsupport middle hmiddle
            have htrace := cappedCacheTracedMappedAdversaryImpl_query_trace_update
              publicKey secretKey _ initialCache initialTrace middle hmiddle'
            obtain ⟨suffix, hfinalTrace⟩ :=
              cappedCacheTracedMappedAdversaryImpl_trace_eq_append publicKey secretKey
                (next middle.1) middle.2.1 middle.2.2 result hresult
            have hnodup := hevent.1
            rw [hfinalTrace, htrace] at hnodup
            simp only [signingCacheTraceUpdate, SigningCacheTrace.leafIndices_append] at hnodup
            have hsub : (initialTrace.leafIndices ++ [request.epoch]).Nodup := by
              simpa [SigningCacheTrace.leafIndices] using (List.nodup_append.mp hnodup).1
            rw [List.nodup_append] at hsub
            exact hsub.2.2 _ hfresh _ (by simp) rfl
          · have hk := cachedEncodingEntryCount_le_untraced secretKey.parameter initialCache
              initialTrace request.epoch hfresh
            by_cases htop : cachedEncodingEntryCount initialCache secretKey.parameter
                request.epoch = ⊤
            · have hpotTop : untracedEncodingEntryCount initialCache secretKey.parameter
                  initialTrace = ⊤ := top_le_iff.mp (htop ▸ hk)
              rw [hpotTop, top_add, ENNReal.mul_top (by simp [signingAttemptLimit]),
                ENNReal.top_mul (by simp)]
              exact le_top
            simp only [simulateQ_spec_query]
            refine (probEvent_bind_le_probEvent_add
                (p := fun middle : Option Signature ×
                    (QueryCache HashSpec × SigningCacheTrace) =>
                  (SigningCacheEntry.mk request middle.1 initialCache middle.2.1)
                    |>.EncodingInputPrehit secretKey)
                (ε := (signingAttemptLimit : ℝ≥0∞) *
                  (untracedEncodingEntryCount initialCache secretKey.parameter initialTrace -
                    cachedEncodingEntryCount initialCache secretKey.parameter request.epoch + n) *
                  ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹) ?_).trans ?_
            · rintro ⟨answer, cache, trace⟩ hmiddle hmiss
              have htrace := cappedCacheTracedMappedAdversaryImpl_query_trace_update
                publicKey secretKey _ initialCache initialTrace _ hmiddle
              have hbase := cappedCacheTracedMappedAdversaryImpl_query_base
                publicKey secretKey _ initialCache initialTrace _ hmiddle
              have hle := cappedCacheTracedMappedAdversaryImpl_query_cache_le
                publicKey secretKey _ (initialCache, initialTrace) _ hmiddle
              have hsign : (answer, cache) ∈ support
                  ((simulateQ romImpl
                    (Concrete.precomputedCappedSign secretKey request.epoch
                      request.message)).run initialCache) := hbase
              simp only [signingCacheTraceUpdate] at htrace
              subst htrace
              have hpot := cachedEncodingEntryCount_add_untraced_le secretKey request
                initialCache cache initialTrace answer hsign hle hfresh
              have hpot' : untracedEncodingEntryCount cache secretKey.parameter
                  (initialTrace ++ [SigningCacheEntry.mk request answer initialCache cache]) ≤
                  untracedEncodingEntryCount initialCache secretKey.parameter initialTrace -
                    cachedEncodingEntryCount initialCache secretKey.parameter request.epoch :=
                ENNReal.le_sub_of_add_le_left htop hpot
              refine (probEvent_mono ?_).trans
                ((ih answer n (hbound' answer) cache _).trans ?_)
              · intro result hresult hevent
                obtain ⟨suffix, hfinalTrace⟩ :=
                  cappedCacheTracedMappedAdversaryImpl_trace_eq_append publicKey secretKey
                    (next answer) cache _ result hresult
                let current := SigningCacheEntry.mk request answer initialCache cache
                have hcurrent : current ∈ result.2.2 := by
                  rw [hfinalTrace]
                  simp [current]
                obtain ⟨hnodup, witness, hwitness, hwitnessFresh, hwitnessPrehit⟩ := hevent
                refine ⟨hnodup, witness, hwitness, ?_, hwitnessPrehit⟩
                simp only [SigningCacheTrace.leafIndices_append, List.mem_append, not_or]
                refine ⟨hwitnessFresh, ?_⟩
                intro hmem
                have hleaf : witness.request.epoch = current.request.epoch := by
                  simpa [SigningCacheTrace.leafIndices, current] using hmem
                have hwitnessEq : witness = current :=
                  List.inj_on_of_nodup_map
                    (by simpa [SigningCacheTrace.leafIndices] using hnodup)
                    hwitness hcurrent hleaf
                apply hmiss
                simpa [current, hwitnessEq] using hwitnessPrehit
              · exact mul_le_mul' (mul_le_mul' le_rfl (add_le_add hpot' le_rfl)) le_rfl
            · refine (add_le_add
                (cappedCacheTracedSigningQuery_encodingInputPrehit_probability_le_cachedCount
                  publicKey secretKey request initialCache initialTrace) le_rfl).trans ?_
              rw [← add_mul, ← mul_add, ← add_assoc, add_tsub_cancel_of_le hk]


theorem cappedDetailedGameAfterKeygenWithSigningTrace_winning_prehit_le_encoding
    (adversary : Adversary) (D : ℕ) (hD : IsEncodingQueryBound adversary D)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    Pr[fun execution : GameOutcome ×
        (QueryCache HashSpec × SigningCacheTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
        execution.2.2.HasEncodingInputPrehit execution.1.secretKey |
      cappedDetailedGameAfterKeygenWithSigningTrace adversary keyResult.1.1
        keyResult.1.2 keyResult.2] ≤
      (signingAttemptLimit : ℝ≥0∞) * D * ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  have hencodingBound : (adversary.main keyResult.1.1).IsQueryBoundP
      (IsDirectEncodingQuery keyResult.1.2.parameter) D := by
    have hparameter : keyResult.1.1.parameter = keyResult.1.2.parameter := by
      obtain ⟨parameter, secret, root, hkeys, _hroot⟩ := Concrete.keygen_support_rootTree
        ((keyResult.1.1, Concrete.erasePrecomputation keyResult.1.2), keyResult.2)
        (Concrete.precomputedKeygen_support_oldKeygen keyResult hkeyResult)
      exact congrArg (fun result => result.1.parameter = result.2.parameter) hkeys ▸ rfl
    rw [← hparameter]
    exact hD keyResult.1.1
  unfold cappedDetailedGameAfterKeygenWithSigningTrace
  refine (probEvent_bind_le_probEvent
    (p := fun result : Forgery × (QueryCache HashSpec × SigningCacheTrace) =>
      result.2.2.leafIndices.Nodup ∧
        result.2.2.HasEncodingInputPrehit keyResult.1.2) ?_).trans ?_
  · intro adversaryResult hadversaryResult hprefix
    apply probEvent_eq_zero
    intro execution hexecution hevent
    have htail := hexecution
    rw [mem_support_bind_iff] at hexecution
    obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hexecution
    simp only [support_pure, Set.mem_singleton_iff] at hfinal
    subst execution
    apply hprefix
    refine ⟨?_, ?_⟩
    · have hvalid := hevent.1.signingTranscript_valid
      unfold SigningTranscript.Valid at hvalid
      simpa [SigningCacheTrace.leafIndices, SigningCacheTrace.toSigningLog,
        List.map_map, Function.comp_def] using hvalid
    · simpa [SigningCacheTrace.HasEncodingInputPrehit] using hevent.2
  · have hzero : untracedEncodingEntryCount keyResult.2 keyResult.1.2.parameter [] = 0 := by
      apply le_antisymm _ zero_le
      rw [← Concrete.keygen_cachedEncodingInputCount_eq_zero keyResult hkeyResult]
      unfold untracedEncodingEntryCount cachedEncodingInputCount
      exact ENat.toENNReal_mono (Set.encard_mono fun entry hentry => by
        obtain ⟨leafIndex, hleafIndex, _⟩ := hentry.2
        exact ⟨hentry.1, by simp [hleafIndex]⟩)
    refine (probEvent_mono'' ?_).trans
      ((cappedCacheTracedMappedAdversary_freshLeafPrehit_le_encoding keyResult.1.1 keyResult.1.2
        (adversary.main keyResult.1.1) D hencodingBound keyResult.2 []).trans ?_)
    · rintro result ⟨hnodup, entry, hentry, hprehit⟩
      exact ⟨hnodup, entry, hentry, by simp [SigningCacheTrace.leafIndices], hprehit⟩
    · rw [hzero, zero_add]

end Direct

theorem winningEncodingPrehit_probability_le_encoding (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsEncodingQueryBound adversary D) :
    Pr[WinningEncodingPrehitOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      (signingAttemptLimit : ℝ≥0∞) * D * ((2 ^ randomnessBits : Nat) : ℝ≥0∞)⁻¹ := by
  calc
    _ = Pr[fun execution : GameOutcome ×
          (QueryCache HashSpec × SigningCacheTrace) =>
        WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
          execution.2.2.HasEncodingInputPrehit execution.1.secretKey |
        cappedDetailedGameWithSigningTrace adversary] := by
      rw [← cappedDetailedGameWithEncodingTrace_projection, probEvent_map]
      rfl
    _ ≤ _ := by
      unfold cappedDetailedGameWithSigningTrace
      apply Direct.probEvent_bind_le_of_forall
      intro keyResult hkeyResult
      exact Direct.cappedDetailedGameAfterKeygenWithSigningTrace_winning_prehit_le_encoding
        adversary D hD keyResult hkeyResult

end XmssSecurity
