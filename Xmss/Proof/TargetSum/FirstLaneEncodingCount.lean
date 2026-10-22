import Xmss.Proof.TargetSum.FirstLaneEncodingCache
import Xmss.Proof.TargetSum.EncodingCacheCount
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Fresh encoding observations count exactly the new encoding-cache entries in
the ideal first-lane execution. Repeated inputs contribute neither a sample nor an entry. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open Xmss.Generic

namespace Xmss.TargetSum.CappedExecution

open FirstLaneOracleSimulation

def EncodingCountGrowth (parameter : PublicParameter) (initial final : QueryCache HashSpec)
    (trace : FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex) : Prop :=
  cachedEncodingInputCount final parameter = cachedEncodingInputCount initial parameter +
    (trace.encodingActions.length : ℝ≥0∞)

theorem EncodingCountGrowth.refl (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    EncodingCountGrowth parameter cache cache [] := by
  simp [EncodingCountGrowth, FirstLaneOracleSimulation.ActionTrace.encodingActions]

theorem EncodingCountGrowth.trans {parameter : PublicParameter}
    {initial middle final : QueryCache HashSpec} {head tail : FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex}
    (hhead : EncodingCountGrowth parameter initial middle head)
    (htail : EncodingCountGrowth parameter middle final tail) :
    EncodingCountGrowth parameter initial final (head ++ tail) := by
  change cachedEncodingInputCount final parameter = _
  rw [htail, hhead, FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append, Nat.cast_add, add_assoc]

theorem globalFirstLaneFreshEncodingQuery_encodingCountGrowth
    (table : CappedExecution.GlobalChainValueIndex → Digest) (parameter : PublicParameter)
    (kind : EncodingSampleKind) (hkind : kind ≠ .side) (leafIndex : LeafIndex) (input : HashInput)
    (state : CappedExecution.GlobalCausalHashState)
    (hencoding : (encodingInputLeafIndex? parameter input).isSome)
    (hfresh : state.cache input = none)
    (result : (Digest × CappedExecution.GlobalCausalHashState) × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (CappedExecution.globalFirstLaneFreshEncodingQuery kind leafIndex input state)).run)) :
    EncodingCountGrowth parameter state.cache result.1.2.cache result.2 := by
  cases kind with
  | side => exact (hkind rfl).elim
  | query | sign =>
      unfold CappedExecution.globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingQuery, FirstLaneOracleSimulation.encodingSignAttemptQuery, FirstLaneOracleSimulation.eagerTraceImpl, FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment, QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
      obtain ⟨output, _, rfl⟩ := hresult
      simpa [EncodingCountGrowth, FirstLaneOracleSimulation.ActionTrace.encodingActions, FirstLaneOracleSimulation.traceFragment,
        CappedExecution.GlobalCausalHashState.setCache] using
        cachedEncodingInputCount_cacheQuery_eq_add_one state.cache parameter input output hencoding hfresh

theorem globalFirstLaneEncodingHashQuery_encodingCountGrowth
    (table : CappedExecution.GlobalChainValueIndex → Digest) (secretKey : Generic.SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (state : CappedExecution.GlobalCausalHashState)
    (result : (Digest × CappedExecution.GlobalCausalHashState) × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (CappedExecution.globalFirstLaneEncodingHashQuery secretKey leafIndex message randomness state)).run)) :
    EncodingCountGrowth secretKey.parameter state.cache result.1.2.cache result.2 := by
  unfold CappedExecution.globalFirstLaneEncodingHashQuery at hresult
  cases hcache : state.cache (CacheView.encodingInput secretKey.parameter leafIndex
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
    (table : CappedExecution.GlobalChainValueIndex → Digest) (secretKey : Generic.SecretKey) (input : HashInput)
    (state : CappedExecution.GlobalCausalHashState)
    (result : (Digest × CappedExecution.GlobalCausalHashState) × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (CappedExecution.globalFirstLaneAttackerHashQueryRun secretKey input state)).run)) :
    EncodingCountGrowth secretKey.parameter state.cache result.1.2.cache result.2 := by
  cases hencoding : encodingInputLeafIndex? secretKey.parameter input with
  | some leafIndex =>
      rw [CappedExecution.globalFirstLaneAttackerHashQueryRun_eq_some _ _ _ _ hencoding] at hresult
      cases hcached : state.cache input with
      | some output =>
          rw [CappedExecution.globalFirstLaneAttackerHashQueryAtLeafIndex_eq_cached _ _ _ _ _ hcached] at hresult
          simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hresult
          subst result
          change EncodingCountGrowth secretKey.parameter state.cache
            (CappedExecution.globalCausalRecordedState secretKey input state).cache []
          rw [CappedExecution.globalCausalRecordedState_cache]
          exact EncodingCountGrowth.refl _ _
      | none =>
          rw [CappedExecution.globalFirstLaneAttackerHashQueryAtLeafIndex_eq_fresh _ _ _ _ hcached] at hresult
          have h := globalFirstLaneFreshEncodingQuery_encodingCountGrowth table secretKey.parameter .query
            (by decide) leafIndex input (CappedExecution.globalCausalRecordedState secretKey input state)
            (by simp [hencoding]) (by simpa only [CappedExecution.globalCausalRecordedState_cache] using hcached)
            result hresult
          simpa only [CappedExecution.globalCausalRecordedState_cache] using h
  | none =>
      rw [CappedExecution.globalFirstLaneAttackerHashQueryRun_eq_none _ _ _ hencoding] at hresult
      have htrace := CappedExecution.globalFirstLaneLiftRevealProbe_encodingActions_eq_nil table _ result hresult
      have hprojected := CappedExecution.globalFirstLaneLiftRevealProbe_mem_eagerTrace_support table _ result hresult
      rcases globalCausalAttackerHashQuery_cache_shape table secretKey input state
        (result.1, result.2.chainActions) hprojected with hsame | ⟨output, hupdated⟩
      · change result.1.2.cache = state.cache at hsame
        simp [EncodingCountGrowth, htrace, hsame]
      · change result.1.2.cache = state.cache.cacheQuery input output at hupdated
        simpa only [EncodingCountGrowth, hupdated, htrace, List.length_nil, Nat.cast_zero,
          add_zero] using cachedEncodingInputCount_cacheQuery_eq_of_nonencoding
            state.cache secretKey.parameter input output hencoding

theorem globalFirstLaneSigningAttempt_encodingCountGrowth
    (table : CappedExecution.GlobalChainValueIndex → Digest) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : CappedExecution.GlobalCausalHashState)
    (result : (Option Generic.Signature × CappedExecution.GlobalCausalHashState) × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (CappedExecution.globalFirstLaneSigningAttempt key request state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.cache result.1.2.cache result.2 := by
  obtain ⟨randomness, encoded, hencoded, hcases⟩ :=
    CappedExecution.globalFirstLaneSigningAttempt_support_decompose table key request state result hresult
  have hgrowth := globalFirstLaneEncodingHashQuery_encodingCountGrowth table key.secretKey request.epoch
    request.message randomness state encoded hencoded
  rcases hcases with ⟨_hreject, rfl⟩ | ⟨encoding, revealed, _hdecode, hreveal, hrevealed, rfl⟩
  · exact hgrowth
  · have hcache : revealed.1.2.cache = encoded.1.2.cache := by
      rw [hrevealed, CappedExecution.globalSignatureRevealResult_cache]
    have htrace := CappedExecution.globalFirstLaneLiftRevealProbe_encodingActions_eq_nil table _ revealed hreveal
    simpa only [EncodingCountGrowth, hcache, FirstLaneOracleSimulation.ActionTrace.encodingActions_append, htrace,
      List.append_nil] using hgrowth

theorem globalFirstLaneSignBoundedAttempts_encodingCountGrowth (attempts : ℕ)
    (table : CappedExecution.GlobalChainValueIndex → Digest) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : CappedExecution.GlobalCausalHashState)
    (result : (Option Generic.Signature × CappedExecution.GlobalCausalHashState) × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (CappedExecution.globalFirstLaneSignBoundedAttempts attempts key request state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.cache result.1.2.cache result.2 := by
  induction attempts generalizing state result with
  | zero =>
      simp [CappedExecution.globalFirstLaneSignBoundedAttempts] at hresult
      subst result
      exact EncodingCountGrowth.refl _ _
  | succ attempts ih =>
      rw [CappedExecution.globalFirstLaneSignBoundedAttempts, simulateQ_bind,
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
    (table : CappedExecution.GlobalChainValueIndex → Digest) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT CappedExecution.GlobalCausalHashState (OracleComp CappedExecution.GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : CappedExecution.GlobalDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedExecution.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedExecution.globalExactTracedLift key input base).run state)).run))
    (hbase : ∀ baseResult ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) (base.run state.causalState)).run),
      EncodingCountGrowth key.secretKey.parameter state.causalState.cache
        baseResult.1.2.cache baseResult.2) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  obtain ⟨baseResult, hsupport, rfl⟩ :=
    CappedExecution.globalExactTracedLift_eager_support_decompose table key input base state result hresult
  simpa only [CappedExecution.globalExactTracedNextState, CappedExecution.GlobalDirectTracedState.causalState_mk] using hbase baseResult hsupport

theorem globalFirstLaneExactTraced_uniform_encodingCountGrowth
    (table : CappedExecution.GlobalChainValueIndex → Digest) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (n : ℕ) (state : CappedExecution.GlobalDirectTracedState)
    (result : (Fin (n + 1) × CappedExecution.GlobalDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl key (.inl (.inl n))).run state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  apply globalExactTracedLift_encodingCountGrowth table key (.inl (.inl n))
    (CappedExecution.globalFirstLaneUniformImpl n) state result hresult
  intro baseResult hbase
  rw [CappedExecution.globalFirstLaneUniformImpl_run, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hbase
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
    (table : CappedExecution.GlobalChainValueIndex → Digest) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (input : HashInput) (state : CappedExecution.GlobalDirectTracedState)
    (result : (Digest × CappedExecution.GlobalDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl key (.inl (.inr input))).run state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  rw [CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl_hash_eq_run] at hresult
  apply globalExactTracedLift_encodingCountGrowth table key (.inl (.inr input))
    (StateT.mk (CappedExecution.globalFirstLaneAttackerHashQueryRun
      key.secretKey input)) state result hresult
  intro baseResult hbase
  rw [StateT.run_mk] at hbase
  exact globalFirstLaneHashQuery_encodingCountGrowth table
    key.secretKey input state.causalState baseResult hbase

theorem globalFirstLaneExactTraced_signing_encodingCountGrowth
    (table : CappedExecution.GlobalChainValueIndex → Digest) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : CappedExecution.GlobalDirectTracedState)
    (result : (Option Generic.Signature × CappedExecution.GlobalDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl key (.inr request)).run state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  unfold CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl CappedExecution.globalFirstLaneExactTracedSigningImpl at hresult
  apply globalExactTracedLift_encodingCountGrowth table key (.inr request)
    (CappedExecution.globalFirstLaneSigningImpl key request) state result hresult
  intro baseResult hbase
  rw [CappedExecution.globalFirstLaneSigningImpl] at hbase
  exact globalFirstLaneSignBoundedAttempts_encodingCountGrowth signingAttemptLimit table key request
    state.causalState baseResult hbase

theorem globalFirstLaneExactTraced_query_encodingCountGrowth
    (table : CappedExecution.GlobalChainValueIndex → Digest) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CappedExecution.GlobalDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedExecution.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl key input).run state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  cases input with
  | inl input =>
      cases input with
      | inl n =>
          exact globalFirstLaneExactTraced_uniform_encodingCountGrowth table key n state result hresult
      | inr input =>
          exact globalFirstLaneExactTraced_hash_encodingCountGrowth table key input state result hresult
  | inr request =>
      exact globalFirstLaneExactTraced_signing_encodingCountGrowth table key request state result hresult

theorem globalFirstLaneExactTraced_encodingCountGrowth
    (table : CappedExecution.GlobalChainValueIndex → Digest) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CappedExecution.GlobalDirectTracedState)
    (result : (α × CappedExecution.GlobalDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((simulateQ (CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl key) computation).run state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  exact simulateQ_eagerTrace_support_invariant table
    (CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl key)
    (fun initial trace final => EncodingCountGrowth key.secretKey.parameter
      initial.causalState.cache final.causalState.cache trace)
    (fun initial => EncodingCountGrowth.refl _ _)
    (fun _ _ _ _ _ hhead htail => hhead.trans htail)
    (globalFirstLaneExactTraced_query_encodingCountGrowth table key) computation state result hresult

theorem globalFilteredCausalKeygenState_encodingCount_zero
    (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen) :
    cachedEncodingInputCount (CappedExecution.globalFilteredCausalKeygenState key).cache key.secretKey.parameter = 0 := by
  classical
  apply cachedEncodingInputCount_eq_zero_of_no_encodingInputs
  intro leafIndex payload
  have hnone := Keygen.keygen_cache_none_encodingInput key.keyResult
    (CappedExecution.trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey) leafIndex payload
  change key.cache (CacheView.encodingInput key.secretKey.parameter leafIndex payload) = none at hnone
  change (if MerkleHashInput key.secretKey.parameter (CacheView.encodingInput key.secretKey.parameter
      leafIndex payload) then key.cache (CacheView.encodingInput key.secretKey.parameter leafIndex payload)
    else none) = none
  rw [hnone]
  split_ifs <;> rfl

theorem globalFirstLaneExactTraced_encodingCount_eq_trace
    (table : CappedExecution.GlobalChainValueIndex → Digest) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (result : (α × CappedExecution.GlobalDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((simulateQ (CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl key) computation).run
        (CappedExecution.GlobalDirectTracedState.initial (CappedExecution.globalFilteredCausalKeygenState key)))).run)) :
    cachedEncodingInputCount result.1.2.causalState.cache key.secretKey.parameter =
      (result.2.encodingActions.length : ℝ≥0∞) := by
  have h := globalFirstLaneExactTraced_encodingCountGrowth table key computation
    (CappedExecution.GlobalDirectTracedState.initial (CappedExecution.globalFilteredCausalKeygenState key)) result hresult
  change cachedEncodingInputCount result.1.2.causalState.cache key.secretKey.parameter =
    cachedEncodingInputCount (CappedExecution.globalFilteredCausalKeygenState key).cache key.secretKey.parameter + _ at h
  simpa only [globalFilteredCausalKeygenState_encodingCount_zero key hkey, zero_add] using h

theorem SourceFirstLaneExactGoodStateRelation.encodingCount_eq
    {left : CappedExecution.ProgrammedGlobalChainKeygenView}
    {right : CappedExecution.ProgrammedGlobalChainKeygenView × (CappedExecution.GlobalChainValueIndex → Digest)}
    {leftState : CappedExecution.SourceExactTracedState} {rightState : CappedExecution.GlobalDirectTracedState}
    {trace : FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex}
    (hstate : CappedExecution.SourceFirstLaneExactGoodStateRelation left right leftState rightState trace) :
    cachedEncodingInputCount leftState.1.1.1 left.secretKey.parameter =
      cachedEncodingInputCount rightState.causalState.cache left.secretKey.parameter := by
  obtain ⟨monitor, _hobserved, _hagrees, _hrevealed, hcausal, _hretained⟩ := hstate.1.1
  apply cachedEncodingInputCount_eq_of_agree
  intro input hencoding
  obtain ⟨leafIndex, hleaf⟩ := Option.isSome_iff_exists.mp hencoding
  obtain ⟨⟨message, randomness⟩, hinput⟩ :=
    exists_encodingInput_of_encodingInputLeafIndex?_eq_some left.secretKey.parameter input leafIndex hleaf
  exact hcausal.1 input ⟨leafIndex, message, randomness, hinput.symm⟩

/-- info: 'Xmss.TargetSum.CappedExecution.globalFirstLaneExactTraced_encodingCountGrowth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms globalFirstLaneExactTraced_encodingCountGrowth

/-- info: 'Xmss.TargetSum.CappedExecution.globalFirstLaneExactTraced_encodingCount_eq_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms globalFirstLaneExactTraced_encodingCount_eq_trace

end Xmss.TargetSum.CappedExecution
