import XmssSecurity.Proof.TargetSum.FirstLaneEncodingAcceptance
import XmssSecurity.Proof.TargetSum.Direct.DecidingAcceptedProbe

/-! Every accepted encoding in the first-lane cache has an accepted sampling observation. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.CappedChain

open FirstLaneOracleSimulation

def AcceptedEncodingGrowth (parameter : PublicParameter) (initial final : QueryCache HashSpec)
    (trace : ActionTrace GlobalChainValueIndex) : Prop :=
  HasAcceptedEncoding parameter final →
    HasAcceptedEncoding parameter initial ∨ TraceHasAcceptedEncoding trace

theorem AcceptedEncodingGrowth.refl (parameter : PublicParameter) (cache : QueryCache HashSpec) :
    AcceptedEncodingGrowth parameter cache cache [] := fun h => Or.inl h

theorem AcceptedEncodingGrowth.trans {parameter : PublicParameter}
    {initial middle final : QueryCache HashSpec} {head tail : ActionTrace GlobalChainValueIndex}
    (hhead : AcceptedEncodingGrowth parameter initial middle head)
    (htail : AcceptedEncodingGrowth parameter middle final tail) :
    AcceptedEncodingGrowth parameter initial final (head ++ tail) := by
  intro hfinal
  rcases htail hfinal with hmiddle | htail
  · rcases hhead hmiddle with hinitial | hhead
    · exact Or.inl hinitial
    · exact Or.inr ((traceHasAcceptedEncoding_append _ _).2 (Or.inl hhead))
  · exact Or.inr ((traceHasAcceptedEncoding_append _ _).2 (Or.inr htail))

theorem AcceptedEncodingGrowth.cacheQuery (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (input : HashInput) (output : HashOutput) (trace : ActionTrace GlobalChainValueIndex)
    (htrace : TargetSum.ValidDigest (truncateHash output) → TraceHasAcceptedEncoding trace) :
    AcceptedEncodingGrowth parameter cache (cache.cacheQuery input output) trace := by
  intro haccepted
  by_cases hinitial : HasAcceptedEncoding parameter cache
  · exact Or.inl hinitial
  · exact Or.inr (htrace ((hasAcceptedEncoding_cacheQuery_iff _ _ _ _ hinitial).1 haccepted).2)

theorem AcceptedEncodingGrowth.cacheQuery_nonencoding (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (input : HashInput) (output : HashOutput)
    (trace : ActionTrace GlobalChainValueIndex) (hinput : encodingInputLeafIndex? parameter input = none) :
    AcceptedEncodingGrowth parameter cache (cache.cacheQuery input output) trace := by
  intro haccepted
  by_cases hinitial : HasAcceptedEncoding parameter cache
  · exact Or.inl hinitial
  · have hencoding := ((hasAcceptedEncoding_cacheQuery_iff _ _ _ _ hinitial).1 haccepted).1
    simp [hinput] at hencoding

theorem randomOracle_support_cache_shape (input : HashInput) (cache : QueryCache HashSpec)
    (result : HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support ((randomOracle input).run cache)) :
    result.2 = cache ∨ ∃ output, result.2 = cache.cacheQuery input output := by
  cases hcached : cache input with
  | some output =>
      rw [QueryImpl.withCaching_run_some _ hcached] at hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Or.inl rfl
  | none =>
      rw [randomOracle_run_none_eq_uniformHashOutput _ _ hcached, support_map] at hresult
      obtain ⟨output, _, rfl⟩ := hresult
      exact Or.inr ⟨output, rfl⟩

theorem globalCausalAttackerHashQueryFromHigh_cache_shape
    (table high : GlobalChainValueIndex → Digest) (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) × RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((globalCausalAttackerHashQueryFromHigh high secretKey input).run state)).run)) :
    result.1.2.cache = state.cache ∨ ∃ output, result.1.2.cache = state.cache.cacheQuery input output := by
  generalize hplan : globalFilteredCausalAttackerHashPlan secretKey input state = plan
  cases plan with
  | cached output =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Or.inl (globalCausalRecordedState_cache secretKey input state)
  | redirect output =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Or.inr ⟨output, by
        simp only [globalFilteredCausalRedirectResultState, globalCausalRecordedState_cache]⟩
  | fresh =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
        simulate_eagerTrace_globalCausalHashQuery, support_map] at hresult
      obtain ⟨sample, hsample, rfl⟩ := hresult
      simp only [globalCausalRecordedState_cache] at hsample
      exact randomOracle_support_cache_shape input state.cache sample hsample
  | reveal index =>
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
        simulate_eagerTrace_globalCausalRevealHashQueryFromHigh] at hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Or.inr ⟨_, rfl⟩
  | probeThenFresh index target =>
      rw [simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
        table high secretKey input state index target hplan, support_map] at hresult
      obtain ⟨sample, hsample, rfl⟩ := hresult
      exact randomOracle_support_cache_shape input state.cache sample hsample

theorem globalFirstLaneFreshEncodingQuery_acceptedGrowth
    (table : GlobalChainValueIndex → Digest) (parameter : PublicParameter)
    (kind : EncodingSampleKind) (hkind : kind ≠ .side) (leafIndex : LeafIndex) (input : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) × ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      (globalFirstLaneFreshEncodingQuery kind leafIndex input state)).run)) :
    AcceptedEncodingGrowth parameter state.cache result.1.2.cache result.2 := by
  cases kind with
  | side => exact (hkind rfl).elim
  | query | sign =>
      unfold globalFirstLaneFreshEncodingQuery at hresult
      simp [encodingQuery, encodingSignAttemptQuery, eagerTraceImpl, eagerImpl,
        traceFragment, QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
      obtain ⟨output, _, rfl⟩ := hresult
      apply AcceptedEncodingGrowth.cacheQuery
      intro hvalid
      simpa [TraceHasAcceptedEncoding, traceFragment, acceptedEncodingAction, Prod.map] using hvalid

theorem globalFirstLaneEncodingHashQuery_acceptedGrowth
    (table : GlobalChainValueIndex → Digest) (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) × ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      (globalFirstLaneEncodingHashQuery secretKey leafIndex message randomness state)).run)) :
    AcceptedEncodingGrowth secretKey.parameter state.cache result.1.2.cache result.2 := by
  unfold globalFirstLaneEncodingHashQuery at hresult
  cases hcache : state.cache (Concrete.CacheView.encodingInput secretKey.parameter leafIndex
      (message, randomness)) with
  | some output =>
      simp [hcache] at hresult
      subst result
      exact AcceptedEncodingGrowth.refl _ _
  | none =>
      simp only [hcache] at hresult
      exact globalFirstLaneFreshEncodingQuery_acceptedGrowth table secretKey.parameter .sign
        (by decide) _ _ _ result hresult

theorem globalFirstLaneHashQuery_acceptedGrowth
    (table high : GlobalChainValueIndex → Digest) (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) × ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      (globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state)).run)) :
    AcceptedEncodingGrowth secretKey.parameter state.cache result.1.2.cache result.2 := by
  cases hencoding : encodingInputLeafIndex? secretKey.parameter input with
  | some leafIndex =>
      rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_some _ _ _ _ _ hencoding] at hresult
      cases hcached : state.cache input with
      | some output =>
          rw [globalFirstLaneAttackerHashQueryAtLeafIndex_eq_cached _ _ _ _ _ hcached] at hresult
          simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hresult
          subst result
          change AcceptedEncodingGrowth secretKey.parameter state.cache
            (globalCausalRecordedState secretKey input state).cache []
          rw [globalCausalRecordedState_cache]
          exact AcceptedEncodingGrowth.refl _ _
      | none =>
          rw [globalFirstLaneAttackerHashQueryAtLeafIndex_eq_fresh _ _ _ _ hcached] at hresult
          have h := globalFirstLaneFreshEncodingQuery_acceptedGrowth table secretKey.parameter .query
            (by decide) leafIndex input (globalCausalRecordedState secretKey input state) result hresult
          simpa only [globalCausalRecordedState_cache] using h
  | none =>
      rw [globalFirstLaneAttackerHashQueryFromHighRun_eq_none _ _ _ _ hencoding] at hresult
      have hprojected := globalFirstLaneLiftRevealProbe_mem_eagerTrace_support table _ result hresult
      rcases globalCausalAttackerHashQueryFromHigh_cache_shape table high secretKey input state
        (result.1, result.2.chainActions) hprojected with hsame | ⟨output, hupdated⟩
      · intro haccepted
        exact Or.inl (hsame ▸ haccepted)
      · change result.1.2.cache = state.cache.cacheQuery input output at hupdated
        rw [hupdated]
        exact AcceptedEncodingGrowth.cacheQuery_nonencoding _ _ _ _ _ hencoding

theorem globalFirstLaneSigningAttempt_acceptedGrowth
    (table : GlobalChainValueIndex → Digest) (key : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) × ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      (globalFirstLaneSigningAttempt key request state)).run)) :
    AcceptedEncodingGrowth key.secretKey.parameter state.cache result.1.2.cache result.2 := by
  obtain ⟨randomness, encoded, hencoded, hcases⟩ :=
    globalFirstLaneSigningAttempt_support_decompose table key request state result hresult
  have hgrowth := globalFirstLaneEncodingHashQuery_acceptedGrowth table key.secretKey request.epoch
    request.message randomness state encoded hencoded
  rcases hcases with ⟨_hreject, rfl⟩ | ⟨encoding, revealed, _hdecode, _hrevealed, hrevealed, rfl⟩
  · exact hgrowth
  · have hcache : revealed.1.2.cache = encoded.1.2.cache := by
      rw [hrevealed, globalSignatureRevealResult_cache]
    intro haccepted
    rw [hcache] at haccepted
    rcases hgrowth haccepted with hinitial | htrace
    · exact Or.inl hinitial
    · exact Or.inr ((traceHasAcceptedEncoding_append _ _).2 (Or.inl htrace))

theorem globalFirstLaneSignBoundedAttempts_acceptedGrowth (attempts : ℕ)
    (table : GlobalChainValueIndex → Digest) (key : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) × ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      (globalFirstLaneSignBoundedAttempts attempts key request state)).run)) :
    AcceptedEncodingGrowth key.secretKey.parameter state.cache result.1.2.cache result.2 := by
  induction attempts generalizing state result with
  | zero =>
      simp [globalFirstLaneSignBoundedAttempts] at hresult
      subst result
      exact AcceptedEncodingGrowth.refl _ _
  | succ attempts ih =>
      rw [globalFirstLaneSignBoundedAttempts, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨attempt, hattempt, hcontinuation⟩ := hresult
      rw [support_map] at hcontinuation
      obtain ⟨tailResult, htail, rfl⟩ := hcontinuation
      have hhead := globalFirstLaneSigningAttempt_acceptedGrowth table key request state attempt hattempt
      cases hoption : attempt.1.1 with
      | some signature =>
          simp [hoption] at htail
          subst tailResult
          simpa only [Prod.map_apply, id_eq, List.append_nil] using hhead
      | none =>
          simp only [hoption] at htail
          exact hhead.trans (ih attempt.1.2 tailResult htail)

theorem globalExactTracedLift_acceptedGrowth
    (table : GlobalChainValueIndex → Digest) (key : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalHighDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × GlobalHighDirectTracedState) ×
      ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      ((globalExactTracedLift key input base).run state)).run))
    (hbase : ∀ baseResult ∈ support ((simulateQ (eagerTraceImpl table) (base.run state.causalState)).run),
      AcceptedEncodingGrowth key.secretKey.parameter state.causalState.cache
        baseResult.1.2.cache baseResult.2) :
    AcceptedEncodingGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  obtain ⟨baseResult, hsupport, rfl⟩ :=
    globalExactTracedLift_eager_support_decompose table key input base state result hresult
  simpa only [globalExactTracedNextState, GlobalHighDirectTracedState.causalState_mk] using hbase baseResult hsupport

theorem globalFirstLaneExactTraced_uniform_acceptedGrowth
    (table : GlobalChainValueIndex → Digest) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (n : ℕ) (state : GlobalHighDirectTracedState)
    (result : (Fin (n + 1) × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      ((globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh (.inl (.inl n))).run state)).run)) :
    AcceptedEncodingGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  apply globalExactTracedLift_acceptedGrowth table key (.inl (.inl n))
    (globalFirstLaneUniformImpl n) state result hresult
  intro baseResult hbase
  rw [globalFirstLaneUniformImpl_run, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hbase
  obtain ⟨head, hhead, htail⟩ := hbase
  simp [uniformQuery, eagerTraceImpl, eagerImpl, traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
  obtain ⟨output, _, rfl⟩ := hhead
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at htail
  subst baseResult
  change AcceptedEncodingGrowth _ _ _ []
  exact AcceptedEncodingGrowth.refl _ _

theorem globalFirstLaneExactTraced_hash_acceptedGrowth
    (table : GlobalChainValueIndex → Digest) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (input : HashInput) (state : GlobalHighDirectTracedState)
    (result : (HashOutput × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      ((globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh (.inl (.inr input))).run state)).run)) :
    AcceptedEncodingGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  rw [globalFirstLaneExactTracedMappedAdversaryImpl_hash_eq_run] at hresult
  apply globalExactTracedLift_acceptedGrowth table key (.inl (.inr input))
    (StateT.mk (globalFirstLaneAttackerHashQueryFromHighRun
      (globalChainValueHighTableOfEdges edgeHigh) key.secretKey input)) state result hresult
  intro baseResult hbase
  rw [StateT.run_mk] at hbase
  exact globalFirstLaneHashQuery_acceptedGrowth table (globalChainValueHighTableOfEdges edgeHigh)
    key.secretKey input state.causalState baseResult hbase

theorem globalFirstLaneExactTraced_signing_acceptedGrowth
    (table : GlobalChainValueIndex → Digest) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (request : SignRequest) (state : GlobalHighDirectTracedState)
    (result : (Option Signature × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      ((globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh (.inr request)).run state)).run)) :
    AcceptedEncodingGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  unfold globalFirstLaneExactTracedMappedAdversaryImpl globalFirstLaneExactTracedSigningImpl at hresult
  apply globalExactTracedLift_acceptedGrowth table key (.inr request)
    (globalFirstLaneSigningImpl key request) state result hresult
  intro baseResult hbase
  rw [globalFirstLaneSigningImpl] at hbase
  exact globalFirstLaneSignBoundedAttempts_acceptedGrowth signingAttemptLimit table key request
    state.causalState baseResult hbase

theorem globalFirstLaneExactTraced_query_acceptedGrowth
    (table : GlobalChainValueIndex → Digest) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × GlobalHighDirectTracedState) ×
      ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      ((globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state)).run)) :
    AcceptedEncodingGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  cases input with
  | inl input =>
      cases input with
      | inl n =>
          exact globalFirstLaneExactTraced_uniform_acceptedGrowth table key edgeHigh n state result hresult
      | inr input =>
          exact globalFirstLaneExactTraced_hash_acceptedGrowth table key edgeHigh input state result hresult
  | inr request =>
      exact globalFirstLaneExactTraced_signing_acceptedGrowth table key edgeHigh request state result hresult

theorem globalFirstLaneExactTraced_acceptedGrowth
    (table : GlobalChainValueIndex → Digest) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalHighDirectTracedState)
    (result : (α × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh) computation).run state)).run)) :
    AcceptedEncodingGrowth key.secretKey.parameter state.causalState.cache
      result.1.2.causalState.cache result.2 := by
  exact simulateQ_eagerTrace_support_invariant table
    (globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh)
    (fun initial trace final => AcceptedEncodingGrowth key.secretKey.parameter
      initial.causalState.cache final.causalState.cache trace)
    (fun initial => AcceptedEncodingGrowth.refl _ _)
    (fun _ _ _ _ _ hhead htail => hhead.trans htail)
    (globalFirstLaneExactTraced_query_acceptedGrowth table key edgeHigh) computation state result hresult

theorem globalFilteredCausalKeygenState_no_acceptedEncoding
    (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen) :
    ¬HasAcceptedEncoding key.secretKey.parameter (globalFilteredCausalKeygenState key).cache := by
  classical
  apply not_hasAcceptedEncoding_of_no_encodingInputs
  intro leafIndex payload
  have hnone := Concrete.keygen_cache_none_encodingInput key.keyResult
    (trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey) leafIndex payload
  change key.cache (Concrete.CacheView.encodingInput key.secretKey.parameter leafIndex payload) = none at hnone
  change (if MerkleHashInput key.secretKey.parameter (Concrete.CacheView.encodingInput key.secretKey.parameter
      leafIndex payload) then key.cache (Concrete.CacheView.encodingInput key.secretKey.parameter leafIndex payload)
    else none) = none
  rw [hnone]
  split_ifs <;> rfl

theorem publicPrefix_acceptedEncoding_implies_trace (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (table : GlobalChainValueIndex → Digest) (edgeHigh : GlobalChainEdgeIndex → Digest)
    (result : (Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      (Deciding.publicPrefixExecution adversary key edgeHigh)).run))
    (haccepted : HasAcceptedEncoding key.secretKey.parameter result.1.2.causalState.cache) :
    TraceHasAcceptedEncoding result.2 := by
  have hgrowth := globalFirstLaneExactTraced_acceptedGrowth table key edgeHigh (adversary.main key.publicKey)
    (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) result hresult
  exact (hgrowth haccepted).resolve_left (globalFilteredCausalKeygenState_no_acceptedEncoding key hkey)

end XmssSecurity.TargetSum.CappedChain

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

theorem coupledPrefix_forgedEncodingAccepted_implies_trace (adversary : Adversary)
    (result : BaseHighKey × ((Forgery × GlobalHighDirectTracedState) × ActionTrace GlobalChainValueIndex))
    (hresult : result ∈ support (coupledFirstLaneProgram (publicPrefixExecution adversary)))
    (haccepted : CoupledPrefixForgedEncodingAccepted result) : TraceHasAcceptedEncoding result.2.2 := by
  unfold coupledFirstLaneProgram at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨key, hkey, hrest⟩ := hresult
  rw [mem_support_bind_iff] at hrest
  obtain ⟨execution, hexecution, hpure⟩ := hrest
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  apply publicPrefix_acceptedEncoding_implies_trace adversary key.1.1
    (coupledGlobalChainKeygenWithBaseHighFull_support_keyView key hkey) key.1.2 key.2 execution hexecution
  change (forgedEncoding execution.1.2.causalState.cache key.1.1.secretKey.parameter execution.1.1).isSome
    at haccepted
  cases hdecode : forgedEncoding execution.1.2.causalState.cache key.1.1.secretKey.parameter execution.1.1 with
  | none => simp [hdecode] at haccepted
  | some encoding => exact hasAcceptedEncoding_of_decode _ _ _ _ _ _ hdecode

theorem coupledPrefix_forgedEncodingAccepted_probability_le_expected (adversary : Adversary) :
    Pr[CoupledPrefixForgedEncodingAccepted | coupledFirstLaneProgram (publicPrefixExecution adversary)] ≤
      TargetSum.acceptanceProbability * expectedEagerQueryCount IsEncodingSample
        (publicFirstLaneProgram (publicPrefixExecution adversary)) := by
  calc
    _ ≤ Pr[fun result => TraceHasAcceptedEncoding result.2.2 |
        coupledFirstLaneProgram (publicPrefixExecution adversary)] :=
      probEvent_mono (coupledPrefix_forgedEncodingAccepted_implies_trace adversary)
    _ = Pr[fun result => TraceHasAcceptedEncoding result.2.2 |
        coupledFirstLaneProjection <$> coupledFirstLaneProgram (publicPrefixExecution adversary)] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun result => TraceHasAcceptedEncoding result.2.2 |
        eagerExperiment (publicFirstLaneProgram (publicPrefixExecution adversary))] :=
      probEvent_eq_of_evalDist_eq _ (evalDist_coupledFirstLaneProgram_projection _)
    _ ≤ _ := traceEncodingAcceptance_eager_probability_le_expected _

/-- The extra deciding probe is paid by accepted encoding samples from the same prefix,
with no unconditional additive probe allowance. -/
theorem decidingFirstLane_probability_le_expected_and_encodingSamples
    (adversary : Adversary) (D : ℕ) (hD : Direct.IsDirectQueryBound adversary D)
    (hcached : ∀ key ∈ support trajectoryProgrammedGlobalChainKeygen,
      ∀ prefixResult ∈ support (sourcePrefixExecution adversary key),
        prefixResult.2.1.1.1 (Concrete.CacheView.encodingInput key.secretKey.parameter
          prefixResult.1.epoch (prefixResult.1.message, prefixResult.1.signature.randomness)) ≠ none) :
    Pr[WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        (expectedCoupledHazards D (publicPrefixExecution adversary) +
          TargetSum.acceptanceProbability * expectedEagerQueryCount IsEncodingSample
            (publicFirstLaneProgram (publicPrefixExecution adversary))) := by
  refine (decidingFirstLane_probability_le_expected_prefix_and_accepted adversary D hD hcached).trans ?_
  exact mul_le_mul' le_rfl
    (add_le_add le_rfl (coupledPrefix_forgedEncodingAccepted_probability_le_expected adversary))

/-- info: 'XmssSecurity.TargetSum.Deciding.coupledPrefix_forgedEncodingAccepted_probability_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupledPrefix_forgedEncodingAccepted_probability_le_expected

/-- info: 'XmssSecurity.TargetSum.Deciding.decidingFirstLane_probability_le_expected_and_encodingSamples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decidingFirstLane_probability_le_expected_and_encodingSamples

end XmssSecurity.TargetSum.Deciding
