import XmssSecurity.Proof.Checksum.CappedJointExactLoss
import XmssSecurity.Proof.Checksum.Direct.Basic

/-!
# Encoding prehits charged to the adversary's direct hash queries

The encoding-prehit term of the second lane is bounded by
`signingAttemptLimit · D / 2^randomnessBits`, where `D` is a syntactic bound on the adversary's own
hash queries (`Direct.IsDirectQueryBound`).

The potential `untracedEncodingEntryCount cache parameter trace` counts the encoding-domain cache
entries at leaves not yet signed. Key generation caches no encoding input, the signer only adds
encoding entries at the leaf it signs (which then leaves the potential), and each direct hash
query adds at most one entry; a signing request at a fresh leaf `ℓ` pays
`signingAttemptLimit · (entries at ℓ) / 2^randomnessBits` and removes those entries from the
potential.
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.Checksum

set_option maxRecDepth 100000

namespace Direct

/-- Encoding-domain cache entries at leaves that are not yet in the signing trace. -/
def untracedEncodingEntrySet (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (trace : SigningCacheTrace) : Set ((t : HashSpec.Domain) × HashSpec.Range t) :=
  {entry ∈ cache.toSet | ∃ leafIndex,
    encodingInputLeafIndex? parameter entry.1 = some leafIndex ∧
      leafIndex ∉ trace.leafIndices}

noncomputable def untracedEncodingEntryCount (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (trace : SigningCacheTrace) : ℝ≥0∞ :=
  ((untracedEncodingEntrySet cache parameter trace).encard : ℝ≥0∞)

/-- A prehit at a leaf that was not yet signed in `initialTrace`, with distinct signed leaves. -/
def FreshLeafPrehit (secretKey : SecretKey) (initialTrace finalTrace : SigningCacheTrace) :
    Prop :=
  finalTrace.leafIndices.Nodup ∧
    ∃ entry ∈ finalTrace, entry.request.epoch ∉ initialTrace.leafIndices ∧
      entry.EncodingInputPrehit secretKey

theorem cappedCacheTracedMappedAdversaryImpl_query_base
    (publicKey : PublicKey) (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (result : (OracleWorld + SigningSpec).Range input ×
      (QueryCache HashSpec × SigningCacheTrace))
    (hresult : result ∈ support
      ((cappedCacheTracedMappedAdversaryImpl publicKey secretKey input).run
        (initialCache, initialTrace))) :
    (result.1, result.2.1) ∈ support
      ((cappedUnloggedMappedAdversaryImpl publicKey secretKey input).run initialCache) := by
  rw [cappedCacheTracedMappedAdversaryImpl, QueryImpl.extendState_apply,
    mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbase, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact hbase

theorem uniform_query_cache_eq
    (publicKey : PublicKey) (secretKey : SecretKey)
    (uniformInput : unifSpec.Domain)
    (initialCache : QueryCache HashSpec)
    (result : (OracleWorld + SigningSpec).Range (.inl (.inl uniformInput)) ×
      QueryCache HashSpec)
    (hmem : result ∈ support
      ((cappedUnloggedMappedAdversaryImpl publicKey secretKey
        (.inl (.inl uniformInput))).run initialCache)) :
    result.2 = initialCache := by
  have hrun :
      (unifFwdImpl HashSpec uniformInput).run initialCache =
        (fun sample => (sample, initialCache)) <$>
          (liftM (unifSpec.query uniformInput) : ProbComp _) := by
    simpa [simulateQ_query] using
      (unifFwdImpl.simulateQ_run
        (hashSpec := HashSpec)
        (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
  change result ∈ support
    ((unifFwdImpl HashSpec uniformInput).run initialCache) at hmem
  rw [hrun, support_map] at hmem
  obtain ⟨sample, _hsample, heq⟩ := hmem
  exact (congrArg Prod.snd heq).symm

theorem hash_query_cache_subset
    (publicKey : PublicKey) (secretKey : SecretKey)
    (hashInput : HashInput)
    (initialCache : QueryCache HashSpec)
    (result : (OracleWorld + SigningSpec).Range (.inl (.inr hashInput)) ×
      QueryCache HashSpec)
    (hmem : result ∈ support
      ((cappedUnloggedMappedAdversaryImpl publicKey secretKey
        (.inl (.inr hashInput))).run initialCache)) :
    ∃ newEntry, result.2.toSet ⊆ insert newEntry initialCache.toSet := by
  rcases result with ⟨returned, finalCache⟩
  change HashOutput at returned
  change (returned, finalCache) ∈
    support ((randomOracle (spec := HashSpec) hashInput).run initialCache) at hmem
  cases hcache : initialCache hashInput with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hcache, support_map,
        Set.mem_image] at hmem
      obtain ⟨sampled, _hsampled, heq⟩ := hmem
      have hfinal : finalCache = initialCache.cacheQuery hashInput sampled :=
        (congrArg Prod.snd heq).symm
      refine ⟨⟨hashInput, sampled⟩, ?_⟩
      change finalCache.toSet ⊆ _
      rw [hfinal]
      exact QueryCache.toSet_cacheQuery_subset_insert initialCache hashInput sampled
  | some cached =>
      rw [QueryImpl.withCaching_run_some _ hcache, support_pure,
        Set.mem_singleton_iff] at hmem
      have hfinal : finalCache = initialCache := congrArg Prod.snd hmem
      refine ⟨⟨hashInput, cached⟩, ?_⟩
      change finalCache.toSet ⊆ _
      rw [hfinal]
      exact Set.subset_insert _ _

theorem untracedEncodingEntryCount_le_of_subset_insert
    (initialCache finalCache : QueryCache HashSpec) (parameter : PublicParameter)
    (trace : SigningCacheTrace) (newEntry : (t : HashSpec.Domain) × HashSpec.Range t)
    (hsubset : finalCache.toSet ⊆ insert newEntry initialCache.toSet) :
    untracedEncodingEntryCount finalCache parameter trace ≤
      untracedEncodingEntryCount initialCache parameter trace + 1 := by
  unfold untracedEncodingEntryCount
  have hsub : untracedEncodingEntrySet finalCache parameter trace ⊆
      insert newEntry (untracedEncodingEntrySet initialCache parameter trace) := by
    intro entry hentry
    rcases hsubset hentry.1 with heq | hold
    · exact Or.inl heq
    · exact Or.inr ⟨hold, hentry.2⟩
  have hencard := (Set.encard_mono hsub).trans
    (Set.encard_insert_le (untracedEncodingEntrySet initialCache parameter trace) newEntry)
  have hcast := ENat.toENNReal_mono hencard
  simpa [ENat.toENNReal_add] using hcast

/-- After a signing request at a fresh leaf, the entries at that leaf plus the new potential are
at most the old potential. -/
theorem cachedEncodingEntryCount_add_untraced_le
    (secretKey : SecretKey) (request : SignRequest)
    (initialCache finalCache : QueryCache HashSpec) (initialTrace : SigningCacheTrace)
    (signature : Option Signature)
    (hsign : (signature, finalCache) ∈ support
      ((simulateQ romImpl
        (Concrete.precomputedCappedSign secretKey request.epoch request.message)).run
          initialCache))
    (hle : initialCache ≤ finalCache)
    (hfresh : request.epoch ∉ initialTrace.leafIndices) :
    cachedEncodingEntryCount initialCache secretKey.parameter request.epoch +
        untracedEncodingEntryCount finalCache secretKey.parameter
          (initialTrace ++ [SigningCacheEntry.mk request signature initialCache finalCache]) ≤
      untracedEncodingEntryCount initialCache secretKey.parameter initialTrace := by
  classical
  let parameter := secretKey.parameter
  let fiber := {entry ∈ initialCache.toSet |
    encodingInputLeafIndex? parameter entry.1 = some request.epoch}
  let newTrace := initialTrace ++ [SigningCacheEntry.mk request signature initialCache finalCache]
  have hnewLeaf : newTrace.leafIndices = initialTrace.leafIndices ++ [request.epoch] := by
    simp [newTrace, SigningCacheTrace.leafIndices]
  have hfiber : fiber ⊆ untracedEncodingEntrySet initialCache parameter initialTrace := by
    intro entry hentry
    exact ⟨hentry.1, request.epoch, hentry.2, hfresh⟩
  have hrest : untracedEncodingEntrySet finalCache parameter newTrace ⊆
      untracedEncodingEntrySet initialCache parameter initialTrace := by
    rintro ⟨input, output⟩ ⟨hcache, leafIndex, hleafIndex, hnotMem⟩
    rw [hnewLeaf, List.mem_append, not_or] at hnotMem
    have hne : request.epoch ≠ leafIndex := by
      intro heq
      apply hnotMem.2
      simp [heq]
    refine ⟨?_, leafIndex, hleafIndex, hnotMem.1⟩
    change initialCache input = some output
    change finalCache input = some output at hcache
    obtain ⟨payload, hpayload⟩ :=
      exists_encodingInput_of_encodingInputLeafIndex?_eq_some parameter input leafIndex
        hleafIndex
    cases hinitial : initialCache input with
    | none =>
        have hnone := Concrete.precomputedCappedSign_preserves_other_leafIndex_encodingInput
          secretKey request.epoch leafIndex request.message payload initialCache finalCache
          signature hsign hne (by rw [hpayload]; exact hinitial)
        rw [hpayload, hcache] at hnone
        exact (Option.some_ne_none _ hnone).elim
    | some cached =>
        have hfinal : finalCache input = some cached := hle hinitial
        rw [hcache] at hfinal
        rw [Option.some.inj hfinal]
  have hdisjoint : Disjoint fiber (untracedEncodingEntrySet finalCache parameter newTrace) := by
    rw [Set.disjoint_left]
    rintro entry hleft ⟨_hcache, leafIndex, hleafIndex, hnotMem⟩
    have heq : request.epoch = leafIndex := Option.some.inj (hleft.2.symm.trans hleafIndex)
    apply hnotMem
    rw [hnewLeaf]
    simp [heq]
  have hunion := Set.encard_union_eq hdisjoint
  have hencard : fiber.encard + (untracedEncodingEntrySet finalCache parameter newTrace).encard ≤
      (untracedEncodingEntrySet initialCache parameter initialTrace).encard := by
    rw [← hunion]
    exact Set.encard_mono (Set.union_subset hfiber hrest)
  have hcast := ENat.toENNReal_mono hencard
  rw [ENat.toENNReal_add] at hcast
  exact hcast

theorem cachedEncodingEntryCount_le_untraced
    (parameter : PublicParameter) (cache : QueryCache HashSpec) (trace : SigningCacheTrace)
    (leafIndex : LeafIndex) (hfresh : leafIndex ∉ trace.leafIndices) :
    cachedEncodingEntryCount cache parameter leafIndex ≤
      untracedEncodingEntryCount cache parameter trace := by
  unfold cachedEncodingEntryCount untracedEncodingEntryCount
  exact ENat.toENNReal_mono (Set.encard_mono fun entry hentry =>
    ⟨hentry.1, leafIndex, hentry.2, hfresh⟩)

theorem probEvent_bind_le_of_forall {β γ : Type}
    (head : ProbComp β) (continuation : β → ProbComp γ) (event : γ → Prop) (bound : ℝ≥0∞)
    (h : ∀ middle ∈ support head, Pr[event | continuation middle] ≤ bound) :
    Pr[event | head >>= continuation] ≤ bound := by
  have := probEvent_bind_le_probEvent_add (mx := head) (my := continuation) (q := event)
    (p := fun _ => False) (ε := bound) (fun middle hmiddle _ => h middle hmiddle)
  simpa using this

/-- The risk of a fresh-leaf prehit along the adversary's run is at most
`signingAttemptLimit · (potential + n) / 2^randomnessBits`, for a program with at most `n` direct
hash queries. -/
theorem cappedCacheTracedMappedAdversary_freshLeafPrehit_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (n : ℕ)
    (hbound : computation.IsQueryBoundP IsDirectHashQuery n)
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
              simp only [not_isDirectHashQuery_uniform, if_false] at hbound'
              have := ih middle.1 n hbound' initialCache initialTrace
              rw [hstate]
              exact this
          | inr hashInput =>
              have hn : 0 < n := by simpa using hpos
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
              simp only [isDirectHashQuery_hash, if_true] at hbound'
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
                  rw [add_assoc]
                  congr 1
                  have : (n : ℝ≥0∞) = ((1 + (n - 1) : ℕ) : ℝ≥0∞) := by
                    congr 1
                    omega
                  rw [this]
                  push_cast
                  rfl
      | inr request =>
          have hbound' : ∀ answer, (next answer).IsQueryBoundP IsDirectHashQuery n := by
            intro answer
            simpa using hnext answer
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

/-- After key generation, the winning prehit event has probability at most
`signingAttemptLimit · D / 2^randomnessBits`. -/
theorem cappedDetailedGameAfterKeygenWithSigningTrace_winning_prehit_le_direct
    (adversary : Adversary) (D : ℕ) (hD : IsDirectQueryBound adversary D)
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
      ((cappedCacheTracedMappedAdversary_freshLeafPrehit_le keyResult.1.1 keyResult.1.2
        (adversary.main keyResult.1.1) D (hD _) keyResult.2 []).trans ?_)
    · rintro result ⟨hnodup, entry, hentry, hprehit⟩
      exact ⟨hnodup, entry, hentry, by simp [SigningCacheTrace.leafIndices], hprehit⟩
    · rw [hzero, zero_add]

end Direct

/-- The encoding-prehit term of the second lane, charged to the adversary's direct hash
queries only: at most `signingAttemptLimit · D / 2^randomnessBits = D / 2^128`. -/
theorem winningEncodingPrehit_probability_le_direct (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
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
      exact Direct.cappedDetailedGameAfterKeygenWithSigningTrace_winning_prehit_le_direct
        adversary D hD keyResult hkeyResult

end XmssSecurity.Checksum
