import XmssSecurity.Proof.TargetSum.FirstLaneEncodingCache
import XmssSecurity.Proof.TargetSum.EncodingCacheCount
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Fresh encoding observations count exactly the new encoding-cache entries in
the ideal first-lane execution. Repeated inputs contribute neither a sample nor an entry. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.CappedChain

open FirstLaneOracleSimulation

def EncodingCountGrowth (parameter : PublicParameter) (initial final : QueryCache HashSpec)
    (trace : FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex) : Prop :=
  cachedEncodingInputCount final parameter = cachedEncodingInputCount initial parameter +
    (trace.encodingActions.length : ℝ≥0∞)

theorem EncodingCountGrowth.refl (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    EncodingCountGrowth parameter cache cache [] := by
  simp [EncodingCountGrowth, FirstLaneOracleSimulation.ActionTrace.encodingActions]

theorem EncodingCountGrowth.trans {parameter : PublicParameter}
    {initial middle final : QueryCache HashSpec} {head tail : FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex}
    (hhead : EncodingCountGrowth parameter initial middle head)
    (htail : EncodingCountGrowth parameter middle final tail) :
    EncodingCountGrowth parameter initial final (head ++ tail) := by
  change cachedEncodingInputCount final parameter = _
  rw [htail, hhead, FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append, Nat.cast_add, add_assoc]

theorem globalFirstLaneFreshEncodingQuery_encodingCountGrowth
    (table : CappedChain.GlobalChainValueIndex → Digest) (parameter : PublicParameter)
    (kind : EncodingSampleKind) (hkind : kind ≠ .side) (leafIndex : LeafIndex) (input : HashInput)
    (state : CappedChain.GlobalCausalHashState)
    (hencoding : (encodingInputLeafIndex? parameter input).isSome)
    (hfresh : state.cache input = none)
    (result : (HashOutput × CappedChain.GlobalCausalHashState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (CappedChain.globalFirstLaneFreshEncodingQuery kind leafIndex input state)).run)) :
    EncodingCountGrowth parameter state.cache result.1.2.cache result.2 := by
  cases kind with
  | side => exact (hkind rfl).elim
  | query | sign =>
      unfold CappedChain.globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingQuery, FirstLaneOracleSimulation.encodingSignAttemptQuery, FirstLaneOracleSimulation.eagerTraceImpl, FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment, QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
      obtain ⟨output, _, rfl⟩ := hresult
      simpa [EncodingCountGrowth, FirstLaneOracleSimulation.ActionTrace.encodingActions, FirstLaneOracleSimulation.traceFragment,
        CappedChain.GlobalCausalHashState.setCache] using
        cachedEncodingInputCount_cacheQuery_eq_add_one state.cache parameter input output hencoding hfresh

theorem globalFirstLaneEncodingHashQuery_encodingCountGrowth
    (table : CappedChain.GlobalChainValueIndex → Digest) (secretKey : Generic.SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (state : CappedChain.GlobalCausalHashState)
    (result : (HashOutput × CappedChain.GlobalCausalHashState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (CappedChain.globalFirstLaneEncodingHashQuery secretKey leafIndex message randomness state)).run)) :
    EncodingCountGrowth secretKey.parameter state.cache result.1.2.cache result.2 := by
  unfold CappedChain.globalFirstLaneEncodingHashQuery at hresult
  cases hcache : state.cache (Concrete.CacheView.encodingInput secretKey.parameter leafIndex
      (message, randomness)) with
  | some output =>
      simp [hcache] at hresult
      subst result
      exact EncodingCountGrowth.refl _ _
  | none =>
      simp only [hcache] at hresult
      exact globalFirstLaneFreshEncodingQuery_encodingCountGrowth table secretKey.parameter .sign
        (by decide) _ _ _ (by simp) hcache result hresult

theorem globalFirstLaneHashQuery_encodingCountGrowth
    (table high : CappedChain.GlobalChainValueIndex → Digest) (secretKey : Generic.SecretKey) (input : HashInput)
    (state : CappedChain.GlobalCausalHashState)
    (result : (HashOutput × CappedChain.GlobalCausalHashState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (CappedChain.globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state)).run)) :
    EncodingCountGrowth secretKey.parameter state.cache result.1.2.cache result.2 := by
  cases hencoding : encodingInputLeafIndex? secretKey.parameter input with
  | some leafIndex =>
      rw [CappedChain.globalFirstLaneAttackerHashQueryFromHighRun_eq_some _ _ _ _ _ hencoding] at hresult
      cases hcached : state.cache input with
      | some output =>
          rw [CappedChain.globalFirstLaneAttackerHashQueryAtLeafIndex_eq_cached _ _ _ _ _ hcached] at hresult
          simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hresult
          subst result
          change EncodingCountGrowth secretKey.parameter state.cache
            (CappedChain.globalCausalRecordedState secretKey input state).cache []
          rw [CappedChain.globalCausalRecordedState_cache]
          exact EncodingCountGrowth.refl _ _
      | none =>
          rw [CappedChain.globalFirstLaneAttackerHashQueryAtLeafIndex_eq_fresh _ _ _ _ hcached] at hresult
          have h := globalFirstLaneFreshEncodingQuery_encodingCountGrowth table secretKey.parameter .query
            (by decide) leafIndex input (CappedChain.globalCausalRecordedState secretKey input state)
            (by simp [hencoding]) (by simpa only [CappedChain.globalCausalRecordedState_cache] using hcached)
            result hresult
          simpa only [CappedChain.globalCausalRecordedState_cache] using h
  | none =>
      rw [CappedChain.globalFirstLaneAttackerHashQueryFromHighRun_eq_none _ _ _ _ hencoding] at hresult
      have htrace := CappedChain.globalFirstLaneLiftRevealProbe_encodingActions_eq_nil table _ result hresult
      have hprojected := CappedChain.globalFirstLaneLiftRevealProbe_mem_eagerTrace_support table _ result hresult
      rcases globalCausalAttackerHashQueryFromHigh_cache_shape table high secretKey input state
        (result.1, result.2.chainActions) hprojected with hsame | ⟨output, hupdated⟩
      · change result.1.2.cache = state.cache at hsame
        simp [EncodingCountGrowth, htrace, hsame]
      · change result.1.2.cache = state.cache.cacheQuery input output at hupdated
        simpa only [EncodingCountGrowth, hupdated, htrace, List.length_nil, Nat.cast_zero,
          add_zero] using cachedEncodingInputCount_cacheQuery_eq_of_nonencoding
            state.cache secretKey.parameter input output hencoding

theorem globalFirstLaneSigningAttempt_encodingCountGrowth
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : CappedChain.GlobalCausalHashState)
    (result : (Option Generic.Signature × CappedChain.GlobalCausalHashState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (CappedChain.globalFirstLaneSigningAttempt key request state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.cache result.1.2.cache result.2 := by
  obtain ⟨randomness, encoded, hencoded, hcases⟩ :=
    CappedChain.globalFirstLaneSigningAttempt_support_decompose table key request state result hresult
  have hgrowth := globalFirstLaneEncodingHashQuery_encodingCountGrowth table key.secretKey request.epoch
    request.message randomness state encoded hencoded
  rcases hcases with ⟨_hreject, rfl⟩ | ⟨encoding, revealed, _hdecode, hreveal, hrevealed, rfl⟩
  · exact hgrowth
  · have hcache : revealed.1.2.cache = encoded.1.2.cache := by
      rw [hrevealed, CappedChain.globalSignatureRevealResult_cache]
    have htrace := CappedChain.globalFirstLaneLiftRevealProbe_encodingActions_eq_nil table _ revealed hreveal
    simpa only [EncodingCountGrowth, hcache, FirstLaneOracleSimulation.ActionTrace.encodingActions_append, htrace,
      List.append_nil] using hgrowth

theorem globalFirstLaneSignBoundedAttempts_encodingCountGrowth (attempts : ℕ)
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : CappedChain.GlobalCausalHashState)
    (result : (Option Generic.Signature × CappedChain.GlobalCausalHashState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (CappedChain.globalFirstLaneSignBoundedAttempts attempts key request state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.cache result.1.2.cache result.2 := by
  induction attempts generalizing state result with
  | zero =>
      simp [CappedChain.globalFirstLaneSignBoundedAttempts] at hresult
      subst result
      exact EncodingCountGrowth.refl _ _
  | succ attempts ih =>
      rw [CappedChain.globalFirstLaneSignBoundedAttempts, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨attempt, hattempt, hcontinuation⟩ := hresult
      rw [support_map] at hcontinuation
      obtain ⟨tailResult, htail, rfl⟩ := hcontinuation
      have hhead := globalFirstLaneSigningAttempt_encodingCountGrowth table key request state attempt hattempt
      cases hoption : attempt.1.1 with
      | some signature =>
          simp [hoption] at htail
          subst tailResult
          simpa only [Prod.map_apply, id_eq, List.append_nil] using hhead
      | none =>
          simp only [hoption] at htail
          exact hhead.trans (ih attempt.1.2 tailResult htail)

theorem globalExactTracedLift_encodingCountGrowth
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT CappedChain.GlobalCausalHashState (OracleComp CappedChain.GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : CappedChain.GlobalHighDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedChain.GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedChain.globalExactTracedLift key input base).run state)).run))
    (hbase : ∀ baseResult ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) (base.run state.causalState)).run),
      EncodingCountGrowth key.secretKey.parameter state.causalState.cache
        baseResult.1.2.cache baseResult.2) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  obtain ⟨baseResult, hsupport, rfl⟩ :=
    CappedChain.globalExactTracedLift_eager_support_decompose table key input base state result hresult
  simpa only [CappedChain.globalExactTracedNextState, CappedChain.GlobalHighDirectTracedState.causalState_mk] using hbase baseResult hsupport

theorem globalFirstLaneExactTraced_uniform_encodingCountGrowth
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : CappedChain.GlobalChainEdgeIndex → Digest) (n : ℕ) (state : CappedChain.GlobalHighDirectTracedState)
    (result : (Fin (n + 1) × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh (.inl (.inl n))).run state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  apply globalExactTracedLift_encodingCountGrowth table key (.inl (.inl n))
    (CappedChain.globalFirstLaneUniformImpl n) state result hresult
  intro baseResult hbase
  rw [CappedChain.globalFirstLaneUniformImpl_run, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hbase
  obtain ⟨head, hhead, htail⟩ := hbase
  simp [FirstLaneOracleSimulation.uniformQuery, FirstLaneOracleSimulation.eagerTraceImpl, FirstLaneOracleSimulation.eagerImpl, FirstLaneOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
  obtain ⟨output, _, rfl⟩ := hhead
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at htail
  subst baseResult
  change EncodingCountGrowth _ _ _ []
  exact EncodingCountGrowth.refl _ _

theorem globalFirstLaneExactTraced_hash_encodingCountGrowth
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : CappedChain.GlobalChainEdgeIndex → Digest) (input : HashInput) (state : CappedChain.GlobalHighDirectTracedState)
    (result : (HashOutput × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh (.inl (.inr input))).run state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  rw [CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl_hash_eq_run] at hresult
  apply globalExactTracedLift_encodingCountGrowth table key (.inl (.inr input))
    (StateT.mk (CappedChain.globalFirstLaneAttackerHashQueryFromHighRun
      (CappedChain.globalChainValueHighTableOfEdges edgeHigh) key.secretKey input)) state result hresult
  intro baseResult hbase
  rw [StateT.run_mk] at hbase
  exact globalFirstLaneHashQuery_encodingCountGrowth table (CappedChain.globalChainValueHighTableOfEdges edgeHigh)
    key.secretKey input state.causalState baseResult hbase

theorem globalFirstLaneExactTraced_signing_encodingCountGrowth
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : CappedChain.GlobalChainEdgeIndex → Digest) (request : SignRequest) (state : CappedChain.GlobalHighDirectTracedState)
    (result : (Option Generic.Signature × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh (.inr request)).run state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  unfold CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl CappedChain.globalFirstLaneExactTracedSigningImpl at hresult
  apply globalExactTracedLift_encodingCountGrowth table key (.inr request)
    (CappedChain.globalFirstLaneSigningImpl key request) state result hresult
  intro baseResult hbase
  rw [CappedChain.globalFirstLaneSigningImpl] at hbase
  exact globalFirstLaneSignBoundedAttempts_encodingCountGrowth signingAttemptLimit table key request
    state.causalState baseResult hbase

theorem globalFirstLaneExactTraced_query_encodingCountGrowth
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : CappedChain.GlobalChainEdgeIndex → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (state : CappedChain.GlobalHighDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedChain.GlobalHighDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  cases input with
  | inl input =>
      cases input with
      | inl n =>
          exact globalFirstLaneExactTraced_uniform_encodingCountGrowth table key edgeHigh n state result hresult
      | inr input =>
          exact globalFirstLaneExactTraced_hash_encodingCountGrowth table key edgeHigh input state result hresult
  | inr request =>
      exact globalFirstLaneExactTraced_signing_encodingCountGrowth table key edgeHigh request state result hresult

theorem globalFirstLaneExactTraced_encodingCountGrowth
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : CappedChain.GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CappedChain.GlobalHighDirectTracedState)
    (result : (α × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((simulateQ (CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh) computation).run state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  exact simulateQ_eagerTrace_support_invariant table
    (CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh)
    (fun initial trace final => EncodingCountGrowth key.secretKey.parameter
      initial.causalState.cache final.causalState.cache trace)
    (fun initial => EncodingCountGrowth.refl _ _)
    (fun _ _ _ _ _ hhead htail => hhead.trans htail)
    (globalFirstLaneExactTraced_query_encodingCountGrowth table key edgeHigh) computation state result hresult

theorem globalFilteredCausalKeygenState_encodingCount_zero
    (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen) :
    cachedEncodingInputCount (CappedChain.globalFilteredCausalKeygenState key).cache key.secretKey.parameter = 0 := by
  classical
  apply cachedEncodingInputCount_eq_zero_of_no_encodingInputs
  intro leafIndex payload
  have hnone := Concrete.keygen_cache_none_encodingInput key.keyResult
    (CappedChain.trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey) leafIndex payload
  change key.cache (Concrete.CacheView.encodingInput key.secretKey.parameter leafIndex payload) = none at hnone
  change (if MerkleHashInput key.secretKey.parameter (Concrete.CacheView.encodingInput key.secretKey.parameter
      leafIndex payload) then key.cache (Concrete.CacheView.encodingInput key.secretKey.parameter leafIndex payload)
    else none) = none
  rw [hnone]
  split_ifs <;> rfl

theorem globalFirstLaneExactTraced_encodingCount_eq_trace
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (edgeHigh : CappedChain.GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (result : (α × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((simulateQ (CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh) computation).run
        (CappedChain.GlobalHighDirectTracedState.initial (CappedChain.globalFilteredCausalKeygenState key)))).run)) :
    cachedEncodingInputCount result.1.2.causalState.cache key.secretKey.parameter =
      (result.2.encodingActions.length : ℝ≥0∞) := by
  have h := globalFirstLaneExactTraced_encodingCountGrowth table key edgeHigh computation
    (CappedChain.GlobalHighDirectTracedState.initial (CappedChain.globalFilteredCausalKeygenState key)) result hresult
  change cachedEncodingInputCount result.1.2.causalState.cache key.secretKey.parameter =
    cachedEncodingInputCount (CappedChain.globalFilteredCausalKeygenState key).cache key.secretKey.parameter + _ at h
  simpa only [globalFilteredCausalKeygenState_encodingCount_zero key hkey, zero_add] using h

theorem SourceFirstLaneExactGoodStateRelation.encodingCount_eq
    {left : CappedChain.ProgrammedGlobalChainKeygenView}
    {right : CappedChain.ProgrammedGlobalChainKeygenView × (CappedChain.GlobalChainValueIndex → Digest)}
    {leftState : CappedChain.SourceExactTracedState} {rightState : CappedChain.GlobalHighDirectTracedState}
    {trace : FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex}
    (hstate : CappedChain.SourceFirstLaneExactGoodStateRelation left right leftState rightState trace) :
    cachedEncodingInputCount leftState.1.1.1 left.secretKey.parameter =
      cachedEncodingInputCount rightState.causalState.cache left.secretKey.parameter := by
  obtain ⟨monitor, _hobserved, _hagrees, _hrevealed, hcausal, _hretained⟩ := hstate.1.1
  apply cachedEncodingInputCount_eq_of_agree
  intro input hencoding
  obtain ⟨leafIndex, hleaf⟩ := Option.isSome_iff_exists.mp hencoding
  obtain ⟨⟨message, randomness⟩, hinput⟩ :=
    exists_encodingInput_of_encodingInputLeafIndex?_eq_some left.secretKey.parameter input leafIndex hleaf
  exact hcausal.1 input ⟨leafIndex, message, randomness, hinput.symm⟩

/-- info: 'XmssSecurity.TargetSum.CappedChain.globalFirstLaneExactTraced_encodingCountGrowth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms globalFirstLaneExactTraced_encodingCountGrowth

/-- info: 'XmssSecurity.TargetSum.CappedChain.globalFirstLaneExactTraced_encodingCount_eq_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms globalFirstLaneExactTraced_encodingCount_eq_trace

end XmssSecurity.TargetSum.CappedChain
