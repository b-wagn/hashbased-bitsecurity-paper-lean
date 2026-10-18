import XmssSecurity.Proof.Generic.Direct.EncodingPrehit
import XmssSecurity.Proof.Common.ExpectedQueryCount

/-! An expected-count version of the direct encoding-prehit bound. Keeping the count inside
the expectation lets adaptive encoding and structural queries share one direct-query budget. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Generic.Direct

variable [Code]

theorem probEvent_bind_le_probEvent_add_expected
    (head : ProbComp β) (continuation : β → ProbComp γ)
    (event : γ → Prop) (headEvent : β → Prop) (cost : β → ℝ≥0∞)
    (h : ∀ middle ∈ support head, ¬headEvent middle →
      Pr[event | continuation middle] ≤ cost middle) :
    Pr[event | head >>= continuation] ≤
      Pr[headEvent | head] + ∑' middle, Pr[= middle | head] * cost middle := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro middle
  by_cases hmiddle : middle ∈ support head
  · by_cases hevent : headEvent middle
    · simp only [hevent, if_true]
      exact (mul_le_mul' le_rfl probEvent_le_one).trans
        (by simp only [mul_one]; exact le_add_right le_rfl)
    · simp only [hevent, if_false, zero_add]
      exact mul_le_mul' le_rfl (h middle hmiddle hevent)
  · simp [probOutput_eq_zero_of_not_mem_support hmiddle]

theorem expected_const_add_mul_le
    (computation : ProbComp β) (constant rate : ℝ≥0∞) (cost : β → ℝ≥0∞) :
    (∑' result, Pr[= result | computation] * (constant + rate * cost result)) ≤
      constant + rate * ∑' result, Pr[= result | computation] * cost result := by
  simp_rw [mul_add, mul_left_comm (Pr[= _ | computation]) rate]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
  exact add_le_add ((mul_le_mul' tsum_probOutput_le_one le_rfl).trans_eq
    (one_mul constant)) le_rfl

noncomputable def encodingPrehitRate : ℝ≥0∞ :=
  (Code.signingAttemptLimit : ℝ≥0∞) * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹

theorem encodingPrehitRate_ne_zero : encodingPrehitRate ≠ 0 := by
  simp [encodingPrehitRate, Code.signingAttemptLimit_pos.ne']

theorem probEvent_bind_le_constant_add_expected
    (head : ProbComp β) (continuation : β → ProbComp γ)
    (event : γ → Prop) (constant rate : ℝ≥0∞) (cost : β → ℝ≥0∞)
    (h : ∀ middle ∈ support head,
      Pr[event | continuation middle] ≤ constant + rate * cost middle) :
    Pr[event | head >>= continuation] ≤
      constant + rate * ∑' middle, Pr[= middle | head] * cost middle := by
  rw [probEvent_bind_eq_tsum]
  refine (ENNReal.tsum_le_tsum fun middle => ?_).trans
    (expected_const_add_mul_le head constant rate cost)
  by_cases hmiddle : middle ∈ support head
  · exact mul_le_mul' le_rfl (h middle hmiddle)
  · simp [probOutput_eq_zero_of_not_mem_support hmiddle]

theorem cappedCacheTracedMappedAdversary_freshLeafPrehit_le_expected_encoding
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace) :
    Pr[fun result : α × (QueryCache HashSpec × SigningCacheTrace) =>
      FreshLeafPrehit secretKey initialTrace result.2.2 |
      (simulateQ (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
        computation).run (initialCache, initialTrace)] ≤
      encodingPrehitRate *
        (untracedEncodingEntryCount initialCache secretKey.parameter initialTrace +
          expectedSimulatedQueryCount
            (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
            (IsDirectEncodingQuery secretKey.parameter) computation (initialCache, initialTrace)) := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache initialTrace with
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
      rw [simulateQ_bind, StateT.run_bind, expectedSimulatedQueryCount_query_bind]
      simp only [simulateQ_spec_query]
      cases input with
      | inl worldInput =>
          rw [← add_assoc, mul_add]
          apply probEvent_bind_le_constant_add_expected
          intro middle hmiddle
          have htrace := cappedCacheTracedMappedAdversaryImpl_query_trace_update
            publicKey secretKey (.inl worldInput) initialCache initialTrace middle hmiddle
          have htrace' : middle.2.2 = initialTrace := by
            simpa [signingCacheTraceUpdate] using htrace
          have hpot : untracedEncodingEntryCount middle.2.1 secretKey.parameter middle.2.2 ≤
              untracedEncodingEntryCount initialCache secretKey.parameter initialTrace +
                if IsDirectEncodingQuery secretKey.parameter (.inl worldInput) then 1 else 0 := by
            rw [htrace']
            have hbase := cappedCacheTracedMappedAdversaryImpl_query_base
              publicKey secretKey (.inl worldInput) initialCache initialTrace middle hmiddle
            cases worldInput with
            | inl uniformInput =>
                have hcache := uniform_query_cache_eq publicKey secretKey uniformInput
                  initialCache _ hbase
                change middle.2.1 = initialCache at hcache
                rw [hcache]
                simp only [IsDirectEncodingQuery, if_false, add_zero, le_refl]
            | inr hashInput =>
                exact untracedEncodingEntryCount_hash_query_le publicKey secretKey hashInput
                  initialCache initialTrace (middle.1, middle.2.1) hbase
          rcases middle with ⟨answer, cache, trace⟩
          dsimp only at htrace' hpot ⊢
          subst trace
          refine (ih answer cache initialTrace).trans ?_
          rw [← mul_add]
          apply mul_le_mul' le_rfl
          exact add_le_add hpot le_rfl
      | inr request =>
          simp only [IsDirectEncodingQuery, if_false, zero_add]
          by_cases hfresh : request.epoch ∈ initialTrace.leafIndices
          · refine le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
            intro result hresult hevent
            rw [mem_support_bind_iff] at hresult
            obtain ⟨middle, hmiddle, hresult⟩ := hresult
            have htrace := cappedCacheTracedMappedAdversaryImpl_query_trace_update
              publicKey secretKey _ initialCache initialTrace middle hmiddle
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
              rw [hpotTop, top_add, ENNReal.mul_top encodingPrehitRate_ne_zero]
              exact le_top
            let count := fun middle : Option Signature × (QueryCache HashSpec × SigningCacheTrace) =>
              expectedSimulatedQueryCount
                (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
                (IsDirectEncodingQuery secretKey.parameter) (next middle.1) middle.2
            let remainder := untracedEncodingEntryCount initialCache secretKey.parameter initialTrace -
              cachedEncodingEntryCount initialCache secretKey.parameter request.epoch
            refine (probEvent_bind_le_probEvent_add_expected _ _ _
              (fun middle => (SigningCacheEntry.mk request middle.1 initialCache middle.2.1)
                |>.EncodingInputPrehit secretKey)
              (fun middle => encodingPrehitRate * remainder + encodingPrehitRate * count middle)
              ?_).trans ?_
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
                  (initialTrace ++ [SigningCacheEntry.mk request answer initialCache cache]) ≤ remainder :=
                ENNReal.le_sub_of_add_le_left htop hpot
              refine (probEvent_mono ?_).trans ((ih answer cache _).trans ?_)
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
              · rw [← mul_add]
                exact mul_le_mul' le_rfl (add_le_add hpot' le_rfl)
            · have hprehit :=
                cappedCacheTracedSigningQuery_encodingInputPrehit_probability_le_cachedCount
                  publicKey secretKey request initialCache initialTrace
              have hrate : (Code.signingAttemptLimit : ℝ≥0∞) *
                  cachedEncodingEntryCount initialCache secretKey.parameter request.epoch *
                  ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ = encodingPrehitRate *
                  cachedEncodingEntryCount initialCache secretKey.parameter request.epoch := by
                unfold encodingPrehitRate
                ac_rfl
              rw [hrate] at hprehit
              refine (add_le_add hprehit
                (expected_const_add_mul_le _ (encodingPrehitRate * remainder)
                  encodingPrehitRate count)).trans_eq ?_
              rw [← add_assoc, ← mul_add, ← mul_add]
              congr 1
              dsimp only [remainder]
              rw [add_tsub_cancel_of_le hk]
              rfl

theorem expectedSimulatedQueryCount_extendState
    {ι : Type} {spec : OracleSpec ι} {α state auxiliary : Type}
    (implementation : QueryImpl spec (StateT state ProbComp))
    (update : (input : spec.Domain) → state → spec.Range input → state → auxiliary → auxiliary)
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (computation : OracleComp spec α) (initialState : state) (initialAuxiliary : auxiliary) :
    expectedSimulatedQueryCount (implementation.extendState update) predicate
        computation (initialState, initialAuxiliary) =
      expectedSimulatedQueryCount implementation predicate computation initialState := by
  induction computation using OracleComp.inductionOn generalizing initialState initialAuxiliary with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_query_bind,
        QueryImpl.extendState_apply, tsum_probOutput_bind_mul]
      simp_rw [tsum_probOutput_pure_mul, ih]

theorem cappedDetailedGameAfterKeygenWithSigningTrace_winning_prehit_le_expected_encoding
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅)) :
    Pr[fun execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace) =>
      WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
        execution.2.2.HasEncodingInputPrehit execution.1.secretKey |
      cappedDetailedGameAfterKeygenWithSigningTrace adversary keyResult.1.1
        keyResult.1.2 keyResult.2] ≤
      encodingPrehitRate * expectedSimulatedQueryCount
        (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
        (IsDirectEncodingQuery keyResult.1.2.parameter)
        (adversary.main keyResult.1.1) keyResult.2 := by
  unfold cappedDetailedGameAfterKeygenWithSigningTrace
  refine (probEvent_bind_le_probEvent
    (p := fun result : Forgery × (QueryCache HashSpec × SigningCacheTrace) =>
      result.2.2.leafIndices.Nodup ∧
        result.2.2.HasEncodingInputPrehit keyResult.1.2) ?_).trans ?_
  · intro adversaryResult hadversaryResult hprefix
    apply probEvent_eq_zero
    intro execution hexecution hevent
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
      ((cappedCacheTracedMappedAdversary_freshLeafPrehit_le_expected_encoding
        keyResult.1.1 keyResult.1.2 (adversary.main keyResult.1.1) keyResult.2 []).trans_eq ?_)
    · rintro result ⟨hnodup, entry, hentry, hprehit⟩
      exact ⟨hnodup, entry, hentry, by simp [SigningCacheTrace.leafIndices], hprehit⟩
    · rw [hzero, zero_add, cappedCacheTracedMappedAdversaryImpl,
        expectedSimulatedQueryCount_extendState]

noncomputable def expectedDirectEncodingQueries (adversary : Adversary) : ℝ≥0∞ :=
  ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
    expectedSimulatedQueryCount
      (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      (IsDirectEncodingQuery keyResult.1.2.parameter)
      (adversary.main keyResult.1.1) keyResult.2

theorem winningEncodingPrehit_probability_le_expected_direct_encoding (adversary : Adversary) :
    Pr[WinningEncodingPrehitOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      encodingPrehitRate * expectedDirectEncodingQueries adversary := by
  calc
    _ ≤ Pr[fun execution : GameOutcome × (QueryCache HashSpec × SigningCacheTrace) =>
        WinningOutcomeBadEventOccurs execution.2.1 execution.1 .encoding ∧
          execution.2.2.HasEncodingInputPrehit execution.1.secretKey |
        cappedDetailedGameWithSigningTrace adversary] := by
      rw [← cappedDetailedGameWithEncodingTrace_projection, probEvent_map]
      exact probEvent_mono fun execution _ h => h.hasEncodingInputPrehit
    _ ≤ _ := by
      unfold cappedDetailedGameWithSigningTrace expectedDirectEncodingQueries
      rw [probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro keyResult
      rw [← mul_assoc, mul_comm encodingPrehitRate, mul_assoc]
      by_cases hkeyResult : keyResult ∈ support
          ((simulateQ romImpl Concrete.scheme.keygen).run ∅)
      · exact mul_le_mul' le_rfl
          (cappedDetailedGameAfterKeygenWithSigningTrace_winning_prehit_le_expected_encoding
            adversary keyResult hkeyResult)
      · simp [probOutput_eq_zero_of_not_mem_support hkeyResult]

end XmssSecurity.Generic.Direct
