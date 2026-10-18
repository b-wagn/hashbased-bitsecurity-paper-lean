import XmssSecurity.Proof.TargetSum.FirstLaneEncodingCache
import XmssSecurity.Proof.TargetSum.EncodingCacheCount
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Fresh encoding observations count exactly the new encoding-cache entries in
the ideal first-lane execution. Repeated inputs contribute neither a sample nor an entry. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.CappedChain

open FirstLaneOracleSimulation

def EncodingCountGrowth (parameter : PublicParameter) (initial final : QueryCache HashSpec)
    (trace : Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex) : Prop :=
  Generic.cachedEncodingInputCount final parameter = Generic.cachedEncodingInputCount initial parameter +
    (trace.encodingActions.length : ℝ≥0∞)

theorem EncodingCountGrowth.refl (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    EncodingCountGrowth parameter cache cache [] := by
  simp [EncodingCountGrowth, Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions]

theorem EncodingCountGrowth.trans {parameter : PublicParameter}
    {initial middle final : QueryCache HashSpec} {head tail : Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex}
    (hhead : EncodingCountGrowth parameter initial middle head)
    (htail : EncodingCountGrowth parameter middle final tail) :
    EncodingCountGrowth parameter initial final (head ++ tail) := by
  change Generic.cachedEncodingInputCount final parameter = _
  rw [htail, hhead, Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append, Nat.cast_add, add_assoc]

theorem globalFirstLaneFreshEncodingQuery_encodingCountGrowth
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (parameter : PublicParameter)
    (kind : Generic.EncodingSampleKind) (hkind : kind ≠ .side) (leafIndex : LeafIndex) (input : HashInput)
    (state : Generic.CappedChain.GlobalCausalHashState)
    (hencoding : (Generic.encodingInputLeafIndex? parameter input).isSome)
    (hfresh : state.cache input = none)
    (result : (HashOutput × Generic.CappedChain.GlobalCausalHashState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      (Generic.CappedChain.globalFirstLaneFreshEncodingQuery kind leafIndex input state)).run)) :
    EncodingCountGrowth parameter state.cache result.1.2.cache result.2 := by
  cases kind with
  | side => exact (hkind rfl).elim
  | query | sign =>
      unfold Generic.CappedChain.globalFirstLaneFreshEncodingQuery at hresult
      simp [Generic.FirstLaneOracleSimulation.encodingQuery, Generic.FirstLaneOracleSimulation.encodingSignAttemptQuery, Generic.FirstLaneOracleSimulation.eagerTraceImpl, Generic.FirstLaneOracleSimulation.eagerImpl,
        Generic.FirstLaneOracleSimulation.traceFragment, QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
      obtain ⟨output, _, rfl⟩ := hresult
      simpa [EncodingCountGrowth, Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions, Generic.FirstLaneOracleSimulation.traceFragment,
        Generic.CappedChain.GlobalCausalHashState.setCache] using
        cachedEncodingInputCount_cacheQuery_eq_add_one state.cache parameter input output hencoding hfresh

theorem globalFirstLaneEncodingHashQuery_encodingCountGrowth
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (secretKey : Generic.SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (state : Generic.CappedChain.GlobalCausalHashState)
    (result : (HashOutput × Generic.CappedChain.GlobalCausalHashState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      (Generic.CappedChain.globalFirstLaneEncodingHashQuery secretKey leafIndex message randomness state)).run)) :
    EncodingCountGrowth secretKey.parameter state.cache result.1.2.cache result.2 := by
  unfold Generic.CappedChain.globalFirstLaneEncodingHashQuery at hresult
  cases hcache : state.cache (Generic.Concrete.CacheView.encodingInput secretKey.parameter leafIndex
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
    (table high : Generic.CappedChain.GlobalChainValueIndex → Digest) (secretKey : Generic.SecretKey) (input : HashInput)
    (state : Generic.CappedChain.GlobalCausalHashState)
    (result : (HashOutput × Generic.CappedChain.GlobalCausalHashState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      (Generic.CappedChain.globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state)).run)) :
    EncodingCountGrowth secretKey.parameter state.cache result.1.2.cache result.2 := by
  cases hencoding : Generic.encodingInputLeafIndex? secretKey.parameter input with
  | some leafIndex =>
      rw [Generic.CappedChain.globalFirstLaneAttackerHashQueryFromHighRun_eq_some _ _ _ _ _ hencoding] at hresult
      cases hcached : state.cache input with
      | some output =>
          rw [Generic.CappedChain.globalFirstLaneAttackerHashQueryAtLeafIndex_eq_cached _ _ _ _ _ hcached] at hresult
          simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hresult
          subst result
          change EncodingCountGrowth secretKey.parameter state.cache
            (Generic.CappedChain.globalCausalRecordedState secretKey input state).cache []
          rw [Generic.CappedChain.globalCausalRecordedState_cache]
          exact EncodingCountGrowth.refl _ _
      | none =>
          rw [Generic.CappedChain.globalFirstLaneAttackerHashQueryAtLeafIndex_eq_fresh _ _ _ _ hcached] at hresult
          have h := globalFirstLaneFreshEncodingQuery_encodingCountGrowth table secretKey.parameter .query
            (by decide) leafIndex input (Generic.CappedChain.globalCausalRecordedState secretKey input state)
            (by simp [hencoding]) (by simpa only [Generic.CappedChain.globalCausalRecordedState_cache] using hcached)
            result hresult
          simpa only [Generic.CappedChain.globalCausalRecordedState_cache] using h
  | none =>
      rw [Generic.CappedChain.globalFirstLaneAttackerHashQueryFromHighRun_eq_none _ _ _ _ hencoding] at hresult
      have htrace := Generic.CappedChain.globalFirstLaneLiftRevealProbe_encodingActions_eq_nil table _ result hresult
      have hprojected := Generic.CappedChain.globalFirstLaneLiftRevealProbe_mem_eagerTrace_support table _ result hresult
      rcases globalCausalAttackerHashQueryFromHigh_cache_shape table high secretKey input state
        (result.1, result.2.chainActions) hprojected with hsame | ⟨output, hupdated⟩
      · change result.1.2.cache = state.cache at hsame
        simp [EncodingCountGrowth, htrace, hsame]
      · change result.1.2.cache = state.cache.cacheQuery input output at hupdated
        simpa only [EncodingCountGrowth, hupdated, htrace, List.length_nil, Nat.cast_zero,
          add_zero] using cachedEncodingInputCount_cacheQuery_eq_of_nonencoding
            state.cache secretKey.parameter input output hencoding

theorem globalFirstLaneSigningAttempt_encodingCountGrowth
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (request : Generic.SignRequest) (state : Generic.CappedChain.GlobalCausalHashState)
    (result : (Option Generic.Signature × Generic.CappedChain.GlobalCausalHashState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      (Generic.CappedChain.globalFirstLaneSigningAttempt key request state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.cache result.1.2.cache result.2 := by
  obtain ⟨randomness, encoded, hencoded, hcases⟩ :=
    Generic.CappedChain.globalFirstLaneSigningAttempt_support_decompose table key request state result hresult
  have hgrowth := globalFirstLaneEncodingHashQuery_encodingCountGrowth table key.secretKey request.epoch
    request.message randomness state encoded hencoded
  rcases hcases with ⟨_hreject, rfl⟩ | ⟨encoding, revealed, _hdecode, hreveal, hrevealed, rfl⟩
  · exact hgrowth
  · have hcache : revealed.1.2.cache = encoded.1.2.cache := by
      rw [hrevealed, Generic.CappedChain.globalSignatureRevealResult_cache]
    have htrace := Generic.CappedChain.globalFirstLaneLiftRevealProbe_encodingActions_eq_nil table _ revealed hreveal
    simpa only [EncodingCountGrowth, hcache, Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions_append, htrace,
      List.append_nil] using hgrowth

theorem globalFirstLaneSignBoundedAttempts_encodingCountGrowth (attempts : ℕ)
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (request : Generic.SignRequest) (state : Generic.CappedChain.GlobalCausalHashState)
    (result : (Option Generic.Signature × Generic.CappedChain.GlobalCausalHashState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      (Generic.CappedChain.globalFirstLaneSignBoundedAttempts attempts key request state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.cache result.1.2.cache result.2 := by
  induction attempts generalizing state result with
  | zero =>
      simp [Generic.CappedChain.globalFirstLaneSignBoundedAttempts] at hresult
      subst result
      exact EncodingCountGrowth.refl _ _
  | succ attempts ih =>
      rw [Generic.CappedChain.globalFirstLaneSignBoundedAttempts, simulateQ_bind,
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
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + Generic.SigningSpec).Domain)
    (base : StateT Generic.CappedChain.GlobalCausalHashState (OracleComp Generic.CappedChain.GlobalFirstLaneWorld)
      ((OracleWorld + Generic.SigningSpec).Range input))
    (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : ((OracleWorld + Generic.SigningSpec).Range input × Generic.CappedChain.GlobalHighDirectTracedState) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalExactTracedLift key input base).run state)).run))
    (hbase : ∀ baseResult ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table) (base.run state.causalState)).run),
      EncodingCountGrowth key.secretKey.parameter state.causalState.cache
        baseResult.1.2.cache baseResult.2) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  obtain ⟨baseResult, hsupport, rfl⟩ :=
    Generic.CappedChain.globalExactTracedLift_eager_support_decompose table key input base state result hresult
  simpa only [Generic.CappedChain.globalExactTracedNextState, Generic.CappedChain.GlobalHighDirectTracedState.causalState_mk] using hbase baseResult hsupport

theorem globalFirstLaneExactTraced_uniform_encodingCountGrowth
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (n : ℕ) (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : (Fin (n + 1) × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh (.inl (.inl n))).run state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  apply globalExactTracedLift_encodingCountGrowth table key (.inl (.inl n))
    (Generic.CappedChain.globalFirstLaneUniformImpl n) state result hresult
  intro baseResult hbase
  rw [Generic.CappedChain.globalFirstLaneUniformImpl_run, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hbase
  obtain ⟨head, hhead, htail⟩ := hbase
  simp [Generic.FirstLaneOracleSimulation.uniformQuery, Generic.FirstLaneOracleSimulation.eagerTraceImpl, Generic.FirstLaneOracleSimulation.eagerImpl, Generic.FirstLaneOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
  obtain ⟨output, _, rfl⟩ := hhead
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at htail
  subst baseResult
  change EncodingCountGrowth _ _ _ []
  exact EncodingCountGrowth.refl _ _

theorem globalFirstLaneExactTraced_hash_encodingCountGrowth
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (input : HashInput) (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : (HashOutput × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh (.inl (.inr input))).run state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  rw [Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl_hash_eq_run] at hresult
  apply globalExactTracedLift_encodingCountGrowth table key (.inl (.inr input))
    (StateT.mk (Generic.CappedChain.globalFirstLaneAttackerHashQueryFromHighRun
      (Generic.CappedChain.globalChainValueHighTableOfEdges edgeHigh) key.secretKey input)) state result hresult
  intro baseResult hbase
  rw [StateT.run_mk] at hbase
  exact globalFirstLaneHashQuery_encodingCountGrowth table (Generic.CappedChain.globalChainValueHighTableOfEdges edgeHigh)
    key.secretKey input state.causalState baseResult hbase

theorem globalFirstLaneExactTraced_signing_encodingCountGrowth
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (request : Generic.SignRequest) (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : (Option Generic.Signature × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh (.inr request)).run state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  unfold Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl Generic.CappedChain.globalFirstLaneExactTracedSigningImpl at hresult
  apply globalExactTracedLift_encodingCountGrowth table key (.inr request)
    (Generic.CappedChain.globalFirstLaneSigningImpl key request) state result hresult
  intro baseResult hbase
  rw [Generic.CappedChain.globalFirstLaneSigningImpl] at hbase
  exact globalFirstLaneSignBoundedAttempts_encodingCountGrowth signingAttemptLimit table key request
    state.causalState baseResult hbase

theorem globalFirstLaneExactTraced_query_encodingCountGrowth
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (input : (OracleWorld + Generic.SigningSpec).Domain)
    (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : ((OracleWorld + Generic.SigningSpec).Range input × Generic.CappedChain.GlobalHighDirectTracedState) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state)).run)) :
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
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : (α × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((simulateQ (Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh) computation).run state)).run)) :
    EncodingCountGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  exact Generic.simulateQ_eagerTrace_support_invariant table
    (Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh)
    (fun initial trace final => EncodingCountGrowth key.secretKey.parameter
      initial.causalState.cache final.causalState.cache trace)
    (fun initial => EncodingCountGrowth.refl _ _)
    (fun _ _ _ _ _ hhead htail => hhead.trans htail)
    (globalFirstLaneExactTraced_query_encodingCountGrowth table key edgeHigh) computation state result hresult

theorem globalFilteredCausalKeygenState_encodingCount_zero
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen) :
    Generic.cachedEncodingInputCount (Generic.CappedChain.globalFilteredCausalKeygenState key).cache key.secretKey.parameter = 0 := by
  classical
  apply cachedEncodingInputCount_eq_zero_of_no_encodingInputs
  intro leafIndex payload
  have hnone := Generic.Concrete.keygen_cache_none_encodingInput key.keyResult
    (Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey) leafIndex payload
  change key.cache (Generic.Concrete.CacheView.encodingInput key.secretKey.parameter leafIndex payload) = none at hnone
  change (if Generic.MerkleHashInput key.secretKey.parameter (Generic.Concrete.CacheView.encodingInput key.secretKey.parameter
      leafIndex payload) then key.cache (Generic.Concrete.CacheView.encodingInput key.secretKey.parameter leafIndex payload)
    else none) = none
  rw [hnone]
  split_ifs <;> rfl

theorem globalFirstLaneExactTraced_encodingCount_eq_trace
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (result : (α × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((simulateQ (Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh) computation).run
        (Generic.CappedChain.GlobalHighDirectTracedState.initial (Generic.CappedChain.globalFilteredCausalKeygenState key)))).run)) :
    Generic.cachedEncodingInputCount result.1.2.causalState.cache key.secretKey.parameter =
      (result.2.encodingActions.length : ℝ≥0∞) := by
  have h := globalFirstLaneExactTraced_encodingCountGrowth table key edgeHigh computation
    (Generic.CappedChain.GlobalHighDirectTracedState.initial (Generic.CappedChain.globalFilteredCausalKeygenState key)) result hresult
  change Generic.cachedEncodingInputCount result.1.2.causalState.cache key.secretKey.parameter =
    Generic.cachedEncodingInputCount (Generic.CappedChain.globalFilteredCausalKeygenState key).cache key.secretKey.parameter + _ at h
  simpa only [globalFilteredCausalKeygenState_encodingCount_zero key hkey, zero_add] using h

theorem SourceFirstLaneExactGoodStateRelation.encodingCount_eq
    {left : Generic.CappedChain.ProgrammedGlobalChainKeygenView}
    {right : Generic.CappedChain.ProgrammedGlobalChainKeygenView × (Generic.CappedChain.GlobalChainValueIndex → Digest)}
    {leftState : Generic.CappedChain.SourceExactTracedState} {rightState : Generic.CappedChain.GlobalHighDirectTracedState}
    {trace : Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex}
    (hstate : Generic.CappedChain.SourceFirstLaneExactGoodStateRelation left right leftState rightState trace) :
    Generic.cachedEncodingInputCount leftState.1.1.1 left.secretKey.parameter =
      Generic.cachedEncodingInputCount rightState.causalState.cache left.secretKey.parameter := by
  obtain ⟨monitor, _hobserved, _hagrees, _hrevealed, hcausal, _hretained⟩ := hstate.1.1
  apply cachedEncodingInputCount_eq_of_agree
  intro input hencoding
  obtain ⟨leafIndex, hleaf⟩ := Option.isSome_iff_exists.mp hencoding
  obtain ⟨⟨message, randomness⟩, hinput⟩ :=
    Generic.exists_encodingInput_of_encodingInputLeafIndex?_eq_some left.secretKey.parameter input leafIndex hleaf
  exact hcausal.1 input ⟨leafIndex, message, randomness, hinput.symm⟩

/-- info: 'XmssSecurity.TargetSum.CappedChain.globalFirstLaneExactTraced_encodingCountGrowth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms globalFirstLaneExactTraced_encodingCountGrowth

/-- info: 'XmssSecurity.TargetSum.CappedChain.globalFirstLaneExactTraced_encodingCount_eq_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms globalFirstLaneExactTraced_encodingCount_eq_trace

end XmssSecurity.TargetSum.CappedChain
