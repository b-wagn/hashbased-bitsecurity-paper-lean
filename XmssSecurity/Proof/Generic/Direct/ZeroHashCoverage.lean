import XmssSecurity.Proof.Generic.Direct.DecidingPrefixCoverage

/-! Without adversary hash queries, signing reveals only the returned chain positions.
No closure under walking a chain forward is needed. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Generic.CappedChain

variable [Code]

/-- The actual chain coordinates sent in signatures, without their forward suffixes. -/
def GlobalSentChainValueCovered (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) : Set GlobalChainValueIndex := fun index =>
  ∃ request signature encoding,
    SigningTranscript.Returned log request signature ∧
      Concrete.CacheView.decodedEncoding cache secretKey.parameter request.epoch
        (request.message, signature.randomness) = some encoding ∧
      index.2.1 = request.epoch ∧ index.2.2 = encoding index.1

theorem globalSentChainValueCovered_of_comparableCaches
    (parameter : PublicParameter) (leftCache rightCache : QueryCache HashSpec)
    (leftSecret rightSecret : SecretKey) (leftLog rightLog : QueryLog SigningSpec)
    (hleftParameter : leftSecret.parameter = parameter)
    (hrightParameter : rightSecret.parameter = parameter) (hlogs : rightLog = leftLog)
    (hcaches : HashCachesAgreeOn (GlobalSigningComparableHashInput parameter) leftCache rightCache)
    (index : GlobalChainValueIndex)
    (hindex : index ∈ GlobalSentChainValueCovered rightCache rightSecret rightLog) :
    index ∈ GlobalSentChainValueCovered leftCache leftSecret leftLog := by
  obtain ⟨request, signature, encoding, hreturned, hdecode, hepoch, hdigit⟩ := hindex
  refine ⟨request, signature, encoding, hlogs ▸ hreturned, ?_, hepoch, hdigit⟩
  rw [hleftParameter]
  rw [hrightParameter] at hdecode
  rw [Concrete.CacheView.decodedEncoding_eq_of_input_eq
    (hcaches _ ⟨request.epoch, request.message, signature.randomness, rfl⟩)]
  exact hdecode

theorem simulate_globalMonitored_noHash_support_covered_of_final
    (right : ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hzero : computation.IsQueryBoundP Direct.IsDirectHashQuery 0)
    (state : GlobalMonitoredTracedState) (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec) (finalTrace : AttackerActionTrace)
    (hcovered : GlobalMonitoredCausalStateCovered covered state.1)
    (hdirect : ∀ request signature encoding chain,
      AttackerAction.sign request (some signature) ∈ finalTrace →
      Concrete.CacheView.decodedEncoding finalCache right.1.secretKey.parameter request.epoch
        (request.message, signature.randomness) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalMonitoredMappedAdversaryImpl right) computation).run state))
    (hcacheLe : result.2.1.causal.cache ≤ finalCache)
    (htraceLe : ∀ action, action ∈ result.2.2 → action ∈ finalTrace) :
    GlobalMonitoredCausalStateCovered covered result.2.1 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hcovered
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hzero
      have hnot : ¬ Direct.IsDirectHashQuery input := hzero.1.resolve_right (by omega)
      simp only [simulateQ_query_bind, StateT.run_bind] at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      have hheadCacheLe : head.2.1.causal.cache ≤ finalCache :=
        (simulate_globalMonitoredMappedAdversary_support_cache_le right
          (next head.1) head.2 result htail).trans hcacheLe
      have hheadTraceLe : ∀ action, action ∈ head.2.2 → action ∈ finalTrace := by
        intro action haction
        exact htraceLe action (simulate_globalMonitoredMappedAdversary_support_trace_le right
          (next head.1) head.2 result htail action haction)
      have hheadCovered :=
        globalMonitoredMappedAdversaryImpl_support_covered_of_final_if_hash right input state
          covered finalCache hcovered (by
            rintro ⟨hashInput, rfl⟩
            exact (hnot rfl).elim) head hheadCacheLe
          (fun request signature encoding chain haction hdecode =>
            hdirect request signature encoding chain (hheadTraceLe _ haction) hdecode) hhead
      exact ih head.1 (by simpa [hnot] using hzero.2 head.1) head.2 hheadCovered result htail
        hcacheLe htraceLe

/-- In a hash-free prefix every revealed chain coordinate was actually sent in a signature. -/
theorem globalMonitoredAdversary_zeroHash_support_sentCovered
    (right : ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hzero : computation.IsQueryBoundP Direct.IsDirectHashQuery 0)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalMonitoredMappedAdversaryImpl right) computation).run
        (⟨globalFilteredCausalKeygenState right.1, []⟩, []))) :
    GlobalMonitoredCausalStateCovered
      (GlobalSentChainValueCovered result.2.1.causal.cache right.1.secretKey
        result.2.2.toSigningLog) result.2.1 := by
  apply simulate_globalMonitored_noHash_support_covered_of_final right computation hzero
    (⟨globalFilteredCausalKeygenState right.1, []⟩, [])
    (GlobalSentChainValueCovered result.2.1.causal.cache right.1.secretKey
      result.2.2.toSigningLog) result.2.1.causal.cache result.2.2
  · constructor
    · intro index value hrevealed
      simp [globalFilteredCausalKeygenState] at hrevealed
    · simp [GlobalCausalTraceRevealsCovered]
  · intro request signature encoding chain haction hdecode
    exact ⟨request, signature, encoding,
      result.2.2.sign_mem_toSigningLog request signature haction, hdecode, rfl, rfl⟩
  · exact hresult
  · exact le_rfl
  · exact fun _ hmem => hmem

/-- The same exact coverage property in the public first-lane oracle experiment. -/
theorem globalFirstLaneAdversary_zeroHash_support_sentCovered
    (keyView : ProgrammedGlobalChainKeygenView) (base : GlobalChainValueIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hzero : computation.IsQueryBoundP Direct.IsDirectHashQuery 0)
    (result : (α × GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
        ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl keyView) computation).run
          (GlobalDirectTracedState.initial (globalFilteredCausalKeygenState keyView)))).run)) :
    GlobalCausalTraceRevealsCovered
      (GlobalSentChainValueCovered result.1.2.causalState.cache keyView.secretKey
        result.1.2.attackerTrace.toSigningLog) result.2.chainActions := by
  have hmapped : (result.1, result.2.chainActions) ∈ support
      ((fun execution => (execution.1, execution.2.chainActions)) <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
          ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl keyView) computation).run
            (GlobalDirectTracedState.initial (globalFilteredCausalKeygenState keyView)))).run) := by
    rw [support_map]
    exact ⟨result, hresult, rfl⟩
  rw [simulate_globalFirstLaneEagerTrace_chainProjection] at hmapped
  rw [globalFirstLaneErases_simulateQ_run _ _
    (globalFirstLaneErase_exactTracedMappedAdversaryImpl keyView)] at hmapped
  let initial : GlobalMonitoredTracedState :=
    (⟨globalFilteredCausalKeygenState keyView, []⟩, [])
  have hprojection := map_simulate_globalMonitored_adversary_exact keyView base computation initial
  simp only [initial, List.nil_append, Prod.eta] at hprojection
  change _ = id <$> _ at hprojection
  rw [id_map] at hprojection
  simp only [GlobalDirectTracedState.initial, GlobalDirectTracedState.mk] at hmapped hprojection
  rw [← hprojection, support_map] at hmapped
  obtain ⟨monitoredResult, hmonitoredResult, heq⟩ := hmapped
  have hcovered := (globalMonitoredAdversary_zeroHash_support_sentCovered
    (keyView, base) computation hzero monitoredResult hmonitoredResult).2
  have hcache := congrArg (fun output => output.1.2.causalState.cache) heq
  have htrace := congrArg (fun output => output.1.2.attackerTrace) heq
  have hchain := congrArg Prod.snd heq
  dsimp only [GlobalDirectTracedState.causalState, GlobalDirectTracedState.attackerTrace]
    at hcache htrace hchain ⊢
  rw [← hcache, ← htrace, ← hchain]
  exact hcovered

end XmssSecurity.Generic.CappedChain
