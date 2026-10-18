import XmssSecurity.Proof.Generic.CappedExactFirstLaneSourceCoupling
import XmssSecurity.Proof.Generic.CappedGlobalFirstLaneExperiment
import XmssSecurity.Proof.Generic.CappedGlobalChainReduction
import XmssSecurity.Proof.Generic.CappedChain.DirectQueryAccounting
import XmssSecurity.Proof.Common.StateLens
import XmssSecurity.Proof.Generic.EagerTraceInvariant

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.Generic.CappedChain

variable [Code]

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

namespace GlobalDirectTracedState

abbrev mk (causalState : GlobalCausalHashState)
    (attackerTrace : AttackerActionTrace) : GlobalDirectTracedState :=
  (causalState, attackerTrace)

abbrev causalState (state : GlobalDirectTracedState) :
    GlobalCausalHashState := state.1

abbrev attackerTrace (state : GlobalDirectTracedState) :
    AttackerActionTrace := state.2

@[simp] theorem causalState_mk
    (causal : GlobalCausalHashState) (trace : AttackerActionTrace) :
    causalState (mk causal trace) = causal := rfl

@[simp] theorem attackerTrace_mk
    (causal : GlobalCausalHashState) (trace : AttackerActionTrace) :
    attackerTrace (mk causal trace) = trace := rfl

end GlobalDirectTracedState

@[simp] def GlobalDirectTracedState.initial (causalState : GlobalCausalHashState) :
    GlobalDirectTracedState :=
  ⟨causalState, []⟩

@[simp] def GlobalDirectTracedState.withCausalState (state : GlobalDirectTracedState)
    (causalState : GlobalCausalHashState) : GlobalDirectTracedState :=
  (causalState, state.2)

@[irreducible]
noncomputable def globalExactTracedNextState
    (_keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalDirectTracedState)
    (output : (OracleWorld + SigningSpec).Range input)
    (causalState : GlobalCausalHashState) : GlobalDirectTracedState :=
  GlobalDirectTracedState.mk causalState
    (state.attackerTrace ++ attackerActionFragment input output)

noncomputable def globalExactTracedLift {ι : Type} {world : OracleSpec ι}
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState
      (OracleComp world)
      ((OracleWorld + SigningSpec).Range input)) :
    StateT GlobalDirectTracedState
      (OracleComp world)
      ((OracleWorld + SigningSpec).Range input) :=
  StateT.mk fun state =>
    (fun result => (result.1,
      globalExactTracedNextState keyView input state result.1 result.2)) <$>
      base.run state.causalState

noncomputable def globalFirstLaneExactTracedSigningImpl
    (keyView : ProgrammedGlobalChainKeygenView) : QueryImpl SigningSpec
      (StateT GlobalDirectTracedState
        (OracleComp GlobalFirstLaneWorld)) :=
  fun request => globalExactTracedLift keyView (.inr request)
    (globalFirstLaneSigningImpl keyView request)

noncomputable def globalFirstLaneExactTracedOracleImpl
    (keyView : ProgrammedGlobalChainKeygenView) :
    QueryImpl OracleWorld
      (StateT GlobalDirectTracedState
        (OracleComp GlobalFirstLaneWorld)) :=
  fun input => globalExactTracedLift keyView (.inl input)
    (StateT.mk fun state =>
      globalFirstLaneOracleExecution keyView input state)

noncomputable def globalFirstLaneExactTracedMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalDirectTracedState
        (OracleComp GlobalFirstLaneWorld)) :=
  globalFirstLaneExactTracedOracleImpl keyView +
    globalFirstLaneExactTracedSigningImpl keyView

theorem globalFirstLaneErase_exactTracedLift
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (sourceBase : StateT GlobalCausalHashState
      (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (targetBase : StateT GlobalCausalHashState
      (OracleComp
        (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalDirectTracedState)
    (hbase : GlobalFirstLaneErases
      (sourceBase.run state.causalState)
      (targetBase.run state.causalState)) :
    GlobalFirstLaneErases
      ((globalExactTracedLift keyView input sourceBase).run state)
      ((globalExactTracedLift keyView input targetBase).run state) := by
  unfold globalExactTracedLift
  simp only [StateT.run_mk]
  apply hbase.bind
  intro result
  exact GlobalFirstLaneErases.pure _

theorem globalExactTracedLift_directMapped_eq
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalDirectTracedState) :
    (globalExactTracedLift keyView input
      (globalDirectBaseMappedAdversaryImpl keyView input)).run
        state =
      (globalDirectTracedMappedAdversaryImpl keyView input).run
        state := by
  simp [globalDirectTracedMappedAdversaryImpl,
    globalExactTracedLift, globalExactTracedNextState,
    map_eq_bind_pure_comp]

theorem globalFirstLaneErase_exactTracedMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalDirectTracedState) :
    GlobalFirstLaneErases
      ((globalFirstLaneExactTracedMappedAdversaryImpl keyView input
        ).run state)
      ((globalDirectTracedMappedAdversaryImpl keyView input
        ).run state) := by
  rcases input with worldInput | request
  · have hbase : GlobalFirstLaneErases
        ((StateT.mk fun causalState =>
          globalFirstLaneOracleExecution keyView worldInput
            causalState).run state.causalState)
        ((globalDirectBaseMappedAdversaryImpl keyView
          (.inl worldInput)).run state.causalState) := by
      change GlobalFirstLaneErases
        (globalFirstLaneOracleExecution keyView worldInput
          state.causalState)
        (globalDirectOracleExecution keyView worldInput
          state.causalState)
      exact globalFirstLaneOracleErasure keyView worldInput
        state.causalState
    have herasure := globalFirstLaneErase_exactTracedLift keyView
      (.inl worldInput)
      (StateT.mk fun causalState =>
        globalFirstLaneOracleExecution keyView worldInput causalState)
      (globalDirectBaseMappedAdversaryImpl keyView
        (.inl worldInput)) state hbase
    rw [globalExactTracedLift_directMapped_eq] at herasure
    exact herasure
  · have hbase : GlobalFirstLaneErases
        ((globalFirstLaneSigningImpl keyView request).run state.causalState)
        ((globalDirectBaseMappedAdversaryImpl keyView
          (.inr request)).run state.causalState) := by
      simpa [globalDirectBaseMappedAdversaryImpl] using
        globalFirstLaneErase_directSigningImpl keyView request
          state.causalState
    have herasure := globalFirstLaneErase_exactTracedLift keyView
      (.inr request) (globalFirstLaneSigningImpl keyView request)
      (globalDirectBaseMappedAdversaryImpl keyView
        (.inr request)) state hbase
    rw [globalExactTracedLift_directMapped_eq] at herasure
    exact herasure

noncomputable def firstLaneValidEncodingActions
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) :
    EncodingActionTrace :=
  CappedEncodingMonitor.validActions trace.encodingActions

theorem globalFirstLaneEncodingHashQuery_validTrace
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneEncodingHashQuery secretKey leafIndex message randomness
          state)).run)) :
    firstLaneValidEncodingActions result.2 =
      CappedEncodingMonitor.validActions
        (if state.cache (Concrete.CacheView.encodingInput secretKey.parameter
            leafIndex (message, randomness)) = none then
          [.sign leafIndex result.1.1]
        else []) := by
  unfold globalFirstLaneEncodingHashQuery at hresult
  cases hcache : state.cache
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex
        (message, randomness)) with
  | some output =>
      simp [hcache, firstLaneValidEncodingActions] at hresult ⊢
      exact hresult ▸ rfl
  | none =>
      simp only [if_pos]
      dsimp only at hresult
      simp only [hcache] at hresult
      unfold globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingSignAttemptQuery,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell,
        firstLaneValidEncodingActions] at hresult ⊢
      obtain ⟨output, _houtput, rfl⟩ := hresult
      rfl

theorem globalFirstLaneEncodingHashQuery_cacheGrowth
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneEncodingHashQuery secretKey leafIndex message randomness
          state)).run)) :
    CacheGrowthRepresented
      (fun payload => Concrete.CacheView.encodingInput secretKey.parameter
        leafIndex payload)
      (fun _ output => EncodingMonitor.ObservedAction.sign leafIndex output)
      state.cache result.1.2.cache result.2.encodingActions ∧
    result.1.2.cache
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex
        (message, randomness)) = some result.1.1 := by
  let sampledInput := Concrete.CacheView.encodingInput secretKey.parameter
    leafIndex (message, randomness)
  unfold globalFirstLaneEncodingHashQuery at hresult
  cases hcache : state.cache sampledInput with
  | some output =>
      simp [sampledInput, hcache] at hresult
      subst result
      exact ⟨CacheGrowthRepresented.refl _ _ _, hcache⟩
  | none =>
      dsimp only at hresult
      simp only [sampledInput] at hcache
      simp only [hcache] at hresult
      unfold globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingSignAttemptQuery,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      exact ⟨CacheGrowthRepresented.cacheQuery state.cache
        (message, randomness) output hcache (by simp),
        QueryCache.cacheQuery_self _ _ _⟩

theorem globalFirstLaneLiftRevealProbe_encodingProjection
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α) :
    Prod.map id FirstLaneOracleSimulation.ActionTrace.encodingActions <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (globalFirstLaneLiftRevealProbe computation)).run =
      (fun result => (result, ([] : EncodingActionTrace))) <$>
        simulateQ (RevealProbeOracleSimulation.eagerImpl table) computation := by
  rw [globalFirstLaneLiftRevealProbe, ← QueryImpl.simulateQ_compose]
  have htarget :
      (simulateQ ((RevealProbeOracleSimulation.eagerImpl table).withTraceAppend
        (fun _ _ => ([] : EncodingActionTrace))) computation).run =
        (fun result => (result, ([] : EncodingActionTrace))) <$>
          simulateQ (RevealProbeOracleSimulation.eagerImpl table) computation :=
    QueryImpl.run_simulateQ_withTraceAppend_const_empty
      (RevealProbeOracleSimulation.eagerImpl table) computation
  rw [← htarget]
  apply QueryImpl.mapLog_run_simulateQ_of_query
  · rfl
  · exact FirstLaneOracleSimulation.ActionTrace.encodingActions_append
  · intro input
    cases input <;>
      simp [globalFirstLaneRevealProbeImpl,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        FirstLaneOracleSimulation.ActionTrace.encodingActions,
        FirstLaneOracleSimulation.uniformQuery,
        FirstLaneOracleSimulation.probeQuery,
        FirstLaneOracleSimulation.revealQuery,
        RevealProbeOracleSimulation.eagerImpl,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell]

theorem globalFirstLaneLiftRevealProbe_encodingActions_eq_nil
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α)
    (result : α ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneLiftRevealProbe computation)).run)) :
    result.2.encodingActions = [] := by
  have hmapped : (result.1, result.2.encodingActions) ∈ support
      (Prod.map id FirstLaneOracleSimulation.ActionTrace.encodingActions <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (globalFirstLaneLiftRevealProbe computation)).run) := by
    rw [support_map]
    exact ⟨result, hresult, rfl⟩
  rw [globalFirstLaneLiftRevealProbe_encodingProjection] at hmapped
  rw [support_map] at hmapped
  obtain ⟨value, _hvalue, heq⟩ := hmapped
  exact congrArg Prod.snd heq.symm

theorem globalFirstLaneSignatureReveal_result_eq
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : Encoding)
    (signature : Signature) (state : GlobalCausalHashState)
    (result : (Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneLiftRevealProbe
          ((revealGlobalSignatureChains request encoding allChains signature).run
            state))).run)) :
    result.1 = globalSignatureRevealResult table request encoding allChains
      signature state := by
  have hprojected : (result.1, result.2.chainActions) ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneErase
          (globalFirstLaneLiftRevealProbe
            ((revealGlobalSignatureChains request encoding allChains
              signature).run state)))).run) := by
    rw [← simulate_globalFirstLaneEagerTrace_chainProjection, support_map]
    exact ⟨result, hresult, rfl⟩
  rw [globalFirstLaneErase_liftRevealProbe,
    simulate_eagerTrace_revealGlobalSignatureChains] at hprojected
  simp only [support_pure, Set.mem_singleton_iff] at hprojected
  exact congrArg Prod.fst hprojected

theorem globalFirstLaneSigningAttempt_support_decompose
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningAttempt keyView request state)).run)) :
    ∃ randomness encodedHead,
      encodedHead ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (globalFirstLaneEncodingHashQuery keyView.secretKey request.epoch
            request.message randomness state)).run) ∧
      ((Code.decodeDigest (encodedHead.1.1) = none ∧
          result = ((none, encodedHead.1.2), encodedHead.2)) ∨
        ∃ encoding revealedHead,
          Code.decodeDigest (encodedHead.1.1) =
              some encoding ∧
            revealedHead ∈ support
              ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
                (globalFirstLaneLiftRevealProbe
                  ((revealGlobalSignatureChains request encoding allChains
                    (Concrete.CacheReplay.signWithEncoding keyView.cache
                      keyView.secretKey request.epoch randomness encoding)).run
                        encodedHead.1.2))).run) ∧
            revealedHead.1 =
              globalSignatureRevealResult table request encoding allChains
                (Concrete.CacheReplay.signWithEncoding keyView.cache
                  keyView.secretKey request.epoch randomness encoding)
                encodedHead.1.2 ∧
            result = ((some revealedHead.1.1, revealedHead.1.2),
              encodedHead.2 ++ revealedHead.2)) := by
  unfold globalFirstLaneSigningAttempt at hresult
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨randomHead, hrandom, hrest⟩ := hresult
  rw [FirstLaneOracleSimulation.simulate_eagerTrace_liftProbComp,
    support_map] at hrandom
  obtain ⟨randomness, _hrandomness, rfl⟩ := hrandom
  simp only [List.nil_append] at hrest
  rw [show Prod.map id (fun x => x) =
    (id : ((Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) → _)
    from Prod.map_id, id_map, simulateQ_bind, WriterT.run_bind',
    mem_support_bind_iff] at hrest
  obtain ⟨encodedHead, hencoded, htail⟩ := hrest
  rw [support_map] at htail
  obtain ⟨tailResult, htail, rfl⟩ := htail
  refine ⟨randomness, encodedHead, hencoded, ?_⟩
  cases hdecode : Code.decodeDigest (encodedHead.1.1) with
  | none =>
      simp [hdecode] at htail
      subst tailResult
      refine Or.inl ⟨rfl, ?_⟩
      simp [Prod.map]
  | some encoding =>
      simp only [hdecode] at htail
      rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at htail
      obtain ⟨revealedHead, hrevealed, hpure⟩ := htail
      simp only at hpure
      subst tailResult
      have hrevealedResult := globalFirstLaneSignatureReveal_result_eq table
        request encoding
          (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
            request.epoch randomness encoding)
          encodedHead.1.2 revealedHead hrevealed
      refine Or.inr
        ⟨encoding, revealedHead, rfl, hrevealed, hrevealedResult, ?_⟩
      simp [Prod.map]

theorem globalFirstLaneAttackerHashQueryAtLeafIndex_trace
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (leafIndex : LeafIndex)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryAtLeafIndex secretKey input state leafIndex)
        ).run)) :
    result.2.encodingActions =
      if state.cache input = none then [.query leafIndex result.1.1] else [] := by
  cases hcache : state.cache input with
  | some output =>
      rw [globalFirstLaneAttackerHashQueryAtLeafIndex_eq_cached _ _ _ _ _ hcache]
        at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp [FirstLaneOracleSimulation.ActionTrace.encodingActions]
  | none =>
      rw [globalFirstLaneAttackerHashQueryAtLeafIndex_eq_fresh _ _ _ _ hcache]
        at hresult
      unfold globalFirstLaneFreshEncodingQuery at hresult
      simp [FirstLaneOracleSimulation.encodingQuery,
        FirstLaneOracleSimulation.eagerTraceImpl,
        FirstLaneOracleSimulation.eagerImpl,
        FirstLaneOracleSimulation.traceFragment,
        QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
      obtain ⟨output, _houtput, rfl⟩ := hresult
      simp [FirstLaneOracleSimulation.ActionTrace.encodingActions]

def GlobalFirstLaneSigningSummary
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  CacheGrowthRepresented
      (fun payload => Concrete.CacheView.encodingInput
        keyView.secretKey.parameter request.epoch payload)
      (fun _ output => EncodingMonitor.ObservedAction.sign
        request.epoch output)
      state.cache result.1.2.cache result.2.encodingActions ∧
    List.Sublist (CappedEncodingMonitor.validObservedSignLeafIndices
      result.2.encodingActions) [request.epoch] ∧
    (result.1.1 = none →
      CappedEncodingMonitor.validObservedSignLeafIndices
        result.2.encodingActions = [])

theorem globalFirstLaneSigningAttempt_summary
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningAttempt keyView request state)).run)) :
    GlobalFirstLaneSigningSummary keyView request state result := by
  obtain ⟨randomness, encodedHead, hencoded, hcases⟩ :=
    globalFirstLaneSigningAttempt_support_decompose table keyView request state
      result hresult
  have hgrowth := globalFirstLaneEncodingHashQuery_cacheGrowth table
    keyView.secretKey request.epoch request.message randomness state
      encodedHead hencoded
  have htrace := globalFirstLaneEncodingHashQuery_validTrace table
    keyView.secretKey request.epoch request.message randomness state
      encodedHead hencoded
  have htrace' : CappedEncodingMonitor.validActions
      encodedHead.2.encodingActions =
        CappedEncodingMonitor.validActions
          (if state.cache
              (Concrete.CacheView.encodingInput keyView.secretKey.parameter
                request.epoch (request.message, randomness)) = none then
            [.sign request.epoch encodedHead.1.1]
          else []) := by
    simpa [firstLaneValidEncodingActions] using htrace
  rcases hcases with hreject | haccept
  · obtain ⟨hdecode, hresultEq⟩ := hreject
    subst result
    have hinvalidDigest :
        ¬Code.ValidDigest (encodedHead.1.1) := by
      intro ⟨encoding, hencoding⟩
      rw [hdecode] at hencoding
      contradiction
    have hleafIndices : CappedEncodingMonitor.validObservedSignLeafIndices
        encodedHead.2.encodingActions = [] := by
      unfold CappedEncodingMonitor.validObservedSignLeafIndices
      rw [htrace']
      by_cases hcache : state.cache
          (Concrete.CacheView.encodingInput keyView.secretKey.parameter
            request.epoch (request.message, randomness)) = none
      · simp [hcache, CappedEncodingMonitor.validActions,
          CappedEncodingMonitor.ActionValid, hinvalidDigest,
          EncodingMonitor.observedSignLeafIndices]
      · simp [hcache, CappedEncodingMonitor.validActions,
          EncodingMonitor.observedSignLeafIndices]
    refine ⟨hgrowth.1, ?_, ?_⟩
    · rw [hleafIndices]
      simp
    · intro _hnone
      exact hleafIndices
  · obtain ⟨encoding, revealedHead, _hdecode, hrevealed,
      hrevealedResult, hresultEq⟩ := haccept
    subst result
    have hrevealTrace : revealedHead.2.encodingActions = [] :=
      globalFirstLaneLiftRevealProbe_encodingActions_eq_nil table _ _ hrevealed
    have hfinalCache : revealedHead.1.2.cache = encodedHead.1.2.cache := by
      rw [hrevealedResult, globalSignatureRevealResult_cache]
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · rw [hfinalCache]
        exact hgrowth.1.1
      · intro payload output hfresh hfinal
        rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
        apply List.mem_append_left
        apply hgrowth.1.2 payload output hfresh
        rw [← hfinalCache]
        exact hfinal
    · unfold CappedEncodingMonitor.validObservedSignLeafIndices
      rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
        hrevealTrace, List.append_nil, htrace']
      by_cases hcache : state.cache
          (Concrete.CacheView.encodingInput keyView.secretKey.parameter
            request.epoch (request.message, randomness)) = none
      · simp only [hcache, if_pos]
        change List.Sublist
          (CappedEncodingMonitor.validObservedSignLeafIndices
            [.sign request.epoch encodedHead.1.1]) [request.epoch]
        rw [CappedEncodingMonitor.validObservedSignLeafIndices_singleton_sign]
        split <;> simp
      · simp [hcache, CappedEncodingMonitor.validActions,
          EncodingMonitor.observedSignLeafIndices]
    · intro hnone
      contradiction

theorem globalFirstLaneSignBoundedAttempts_summary
    (attempts : Nat)
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSignBoundedAttempts attempts keyView request state)
        ).run)) :
    GlobalFirstLaneSigningSummary keyView request state result := by
  induction attempts generalizing state result with
  | zero =>
      simp [globalFirstLaneSignBoundedAttempts] at hresult
      subst result
      refine ⟨CacheGrowthRepresented.refl _ _ _, ?_, ?_⟩ <;>
        simp [CappedEncodingMonitor.validObservedSignLeafIndices,
          FirstLaneOracleSimulation.ActionTrace.encodingActions,
          CappedEncodingMonitor.validActions,
          EncodingMonitor.observedSignLeafIndices]
  | succ attempts ih =>
      rw [globalFirstLaneSignBoundedAttempts, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨attemptHead, hattempt, hcontinuation⟩ := hresult
      rw [support_map] at hcontinuation
      obtain ⟨tailResult, htail, rfl⟩ := hcontinuation
      have hhead := globalFirstLaneSigningAttempt_summary table keyView
        request state attemptHead hattempt
      cases hoption : attemptHead.1.1 with
      | some signature =>
          simp [hoption] at htail
          subst tailResult
          simpa [GlobalFirstLaneSigningSummary,
            FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
              using And.intro hhead.1 hhead.2.1
      | none =>
          simp only [hoption] at htail
          have htailSummary := ih attemptHead.1.2 tailResult htail
          refine ⟨?_, ?_, ?_⟩
          · simpa [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
              using hhead.1.trans htailSummary.1
          · change List.Sublist
              (CappedEncodingMonitor.validObservedSignLeafIndices
                (attemptHead.2 ++ tailResult.2).encodingActions)
              [request.epoch]
            rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
              CappedEncodingMonitor.validObservedSignLeafIndices_append,
              hhead.2.2 hoption]
            simpa using htailSummary.2.1
          · intro hfinal
            have htailNone : tailResult.1.1 = none := by
              simpa using hfinal
            change CappedEncodingMonitor.validObservedSignLeafIndices
              (attemptHead.2 ++ tailResult.2).encodingActions = []
            rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
              CappedEncodingMonitor.validObservedSignLeafIndices_append,
              hhead.2.2 hoption, htailSummary.2.2 htailNone]
            rfl

theorem globalFirstLaneSigningQuery_cacheGrowth
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningQuery keyView request state)).run)) :
    CacheGrowthRepresented
      (fun payload => Concrete.CacheView.encodingInput
        keyView.secretKey.parameter request.epoch payload)
      (fun _ output => EncodingMonitor.ObservedAction.sign
        request.epoch output)
      state.cache result.1.2.cache result.2.encodingActions :=
  (globalFirstLaneSignBoundedAttempts_summary Code.signingAttemptLimit table
    keyView request state result hresult).1

theorem globalFirstLaneSigningQuery_validSignLeafIndices_sublist_singleton
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningQuery keyView request state)).run)) :
    List.Sublist (CappedEncodingMonitor.validObservedSignLeafIndices
      result.2.encodingActions) [request.epoch] :=
  (globalFirstLaneSignBoundedAttempts_summary Code.signingAttemptLimit table
    keyView request state result hresult).2.1

theorem encodingActionTraceUpdate_sublist_of_observation_mem
    (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (initialState finalState : QueryCache HashSpec × SigningCacheTrace)
    (output : (OracleWorld + SigningSpec).Range input)
    (initialTrace externalTrace : EncodingActionTrace)
    (hrepresented : ∀ observation,
      encodingObservation? secretKey input initialState output finalState =
          some observation →
        observation ∈ externalTrace) :
    List.Sublist
      (encodingActionTraceUpdate secretKey input initialState output finalState
        initialTrace)
      (initialTrace ++ externalTrace) := by
  unfold encodingActionTraceUpdate
  cases hobservation : encodingObservation? secretKey input initialState output
      finalState with
  | none => exact List.sublist_append_left initialTrace externalTrace
  | some observation =>
      exact (List.Sublist.refl initialTrace).append
        (List.singleton_sublist.mpr (hrepresented observation hobservation))

theorem globalFirstLaneHashQuery_observation_mem
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (hashInput : HashInput)
    (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryRun keyView.secretKey
          hashInput state)).run))
    (observation : EncodingMonitor.ObservedAction)
    (hobservation : encodingObservation? keyView.secretKey
      (.inl (.inr hashInput) : (OracleWorld + SigningSpec).Domain)
      (state.cache, []) result.1.1 (result.1.2.cache, []) = some observation) :
    observation ∈ result.2.encodingActions := by
  cases hleafIndex : encodingInputLeafIndex? keyView.secretKey.parameter hashInput with
  | none =>
      by_cases hfresh : state.cache hashInput = none
      <;> simp [encodingObservation?, hfresh, hleafIndex] at hobservation
  | some leafIndex =>
      by_cases hfresh : state.cache hashInput = none
      · rw [globalFirstLaneAttackerHashQueryRun_eq_some _ _ _ leafIndex
          hleafIndex] at hresult
        have htrace := globalFirstLaneAttackerHashQueryAtLeafIndex_trace table
          keyView.secretKey hashInput state leafIndex result hresult
        have haction : EncodingMonitor.ObservedAction.query leafIndex result.1.1 ∈
            result.2.encodingActions := by
          simp [htrace, hfresh]
        have hobservation' : EncodingMonitor.ObservedAction.query leafIndex
            result.1.1 = observation := by
          exact Option.some.inj (by simpa [encodingObservation?, hfresh, hleafIndex]
            using hobservation)
        simpa [← hobservation'] using haction
      · simp [encodingObservation?, hfresh] at hobservation

theorem globalFirstLaneSigningQuery_observation_mem
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningQuery keyView request state)).run))
    (observation : EncodingMonitor.ObservedAction)
    (hobservation : encodingObservation? keyView.secretKey
      (.inr request : (OracleWorld + SigningSpec).Domain) (state.cache, [])
      result.1.1 (result.1.2.cache, []) = some observation) :
    observation ∈ result.2.encodingActions := by
  cases houtput : result.1.1 with
  | none => simp [encodingObservation?, houtput] at hobservation
  | some signature =>
      let signedInput := Concrete.CacheView.encodingInput
        keyView.secretKey.parameter request.epoch
          (request.message, signature.randomness)
      by_cases hfresh : state.cache signedInput = none
      · cases hfinal : result.1.2.cache signedInput with
        | none =>
            simp [encodingObservation?, signedInput, hfresh, hfinal, houtput]
              at hobservation
        | some hashOutput =>
            have hgrowth := globalFirstLaneSigningQuery_cacheGrowth table
              keyView request state result hresult
            have haction := hgrowth.2
              (request.message, signature.randomness) hashOutput
              (by simpa [signedInput] using hfresh)
              (by simpa [signedInput] using hfinal)
            have hobservation' : EncodingMonitor.ObservedAction.sign
                request.epoch hashOutput = observation := by
              exact Option.some.inj (by simpa [encodingObservation?, signedInput,
                hfresh, hfinal, houtput] using hobservation)
            simpa [← hobservation'] using haction
      · simp [encodingObservation?, signedInput, hfresh, houtput]
          at hobservation

theorem globalFirstLaneUniformQuery_trace_sublist
    (keyView : ProgrammedGlobalChainKeygenView) (n : Nat)
    (state : GlobalCausalHashState) (initialTrace : EncodingActionTrace)
    (result : (Fin (n + 1) × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) :
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey
        (.inl (.inl n) : (OracleWorld + SigningSpec).Domain) (state.cache, [])
          result.1.1 (result.1.2.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  simp [encodingActionTraceUpdate, encodingObservation?]

theorem globalFirstLaneHashQuery_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (hashInput : HashInput)
    (state : GlobalCausalHashState) (initialTrace : EncodingActionTrace)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryRun keyView.secretKey
          hashInput state)).run)) :
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey
        (.inl (.inr hashInput) : (OracleWorld + SigningSpec).Domain)
          (state.cache, []) result.1.1 (result.1.2.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  apply encodingActionTraceUpdate_sublist_of_observation_mem
  intro observation hobservation
  exact globalFirstLaneHashQuery_observation_mem table keyView
    hashInput state result hresult observation hobservation

theorem globalFirstLaneSigningQuery_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (state : GlobalCausalHashState) (initialTrace : EncodingActionTrace)
    (result : (Option Signature × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneSigningQuery keyView request state)).run)) :
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey
        (.inr request : (OracleWorld + SigningSpec).Domain) (state.cache, [])
          result.1.1 (result.1.2.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  apply encodingActionTraceUpdate_sublist_of_observation_mem
  intro observation hobservation
  exact globalFirstLaneSigningQuery_observation_mem table keyView request
    state result hresult observation hobservation

theorem globalExactTracedLift_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalDirectTracedState)
    (initialTrace : EncodingActionTrace)
    (result : ((OracleWorld + SigningSpec).Range input ×
      GlobalDirectTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView input base).run state)).run))
    (hbaseSub : ∀ baseResult,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run state.causalState)).run) →
      List.Sublist
        (encodingActionTraceUpdate keyView.secretKey input
          (state.causalState.cache, []) baseResult.1.1
            (baseResult.1.2.cache, []) initialTrace)
        (initialTrace ++ baseResult.2.encodingActions)) :
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey input
        (state.causalState.cache, []) result.1.1
          (result.1.2.causalState.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  unfold globalExactTracedLift at hresult
  rw [StateT.run_mk, simulateQ_map, WriterT.run_map', support_map] at hresult
  obtain ⟨baseResult, hbase, heq⟩ := hresult
  subst result
  unfold globalExactTracedNextState
  simpa using hbaseSub baseResult hbase

abbrev GlobalFirstLaneOracleTraceSublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) :
    Prop :=
  ∀ (input : OracleWorld.Domain)
    (state : GlobalCausalHashState) (encodingTrace : EncodingActionTrace)
    (result : (OracleWorld.Range input × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex),
    result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneOracleExecution keyView input state)).run) →
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey (.inl input)
        (state.cache, []) result.1.1 (result.1.2.cache, []) encodingTrace)
      (encodingTrace ++ result.2.encodingActions)

theorem globalFirstLaneOracleTraceSublist_holds
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) :
    GlobalFirstLaneOracleTraceSublist table keyView := by
  intro input state encodingTrace result hresult
  cases input with
  | inl n =>
      exact globalFirstLaneUniformQuery_trace_sublist keyView n state
        encodingTrace result
  | inr hashInput =>
      exact globalFirstLaneHashQuery_trace_sublist table keyView
        hashInput state encodingTrace result hresult

abbrev GlobalFirstLaneExactTracedOracleTraceSublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) :
    Prop :=
  ∀ (input : OracleWorld.Domain)
    (state : GlobalDirectTracedState)
    (initialTrace : EncodingActionTrace)
    (result : (OracleWorld.Range input × GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex),
    result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedOracleImpl keyView input).run
          state)).run) →
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey (.inl input)
        (state.causalState.cache, []) result.1.1
          (result.1.2.causalState.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions)

theorem globalFirstLaneExactTracedOracleTraceSublist_holds
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) :
    GlobalFirstLaneExactTracedOracleTraceSublist table keyView := by
  intro input state initialTrace result hresult
  unfold globalFirstLaneExactTracedOracleImpl at hresult
  apply globalExactTracedLift_trace_sublist table keyView
    (.inl input)
    (StateT.mk fun causalState =>
      globalFirstLaneOracleExecution keyView input causalState)
    state initialTrace result hresult
  exact globalFirstLaneOracleTraceSublist_holds table keyView
    input state.causalState initialTrace

theorem globalFirstLaneExactTracedSigningImpl_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (state : GlobalDirectTracedState)
    (initialTrace : EncodingActionTrace)
    (result : (SigningSpec.Range request × GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedSigningImpl keyView request).run state)
          ).run)) :
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey (.inr request)
        (state.causalState.cache, []) result.1.1
          (result.1.2.causalState.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  unfold globalFirstLaneExactTracedSigningImpl at hresult
  apply globalExactTracedLift_trace_sublist table keyView
    (.inr request) (globalFirstLaneSigningImpl keyView request) state
      initialTrace result hresult
  intro baseResult hbase
  exact globalFirstLaneSigningQuery_trace_sublist table keyView request
    state.causalState initialTrace baseResult hbase

theorem globalFirstLaneExactTracedMappedAdversaryImpl_query_trace_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalDirectTracedState)
    (initialTrace : EncodingActionTrace)
    (result : ((OracleWorld + SigningSpec).Range input ×
      GlobalDirectTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedMappedAdversaryImpl keyView input
          ).run state)).run)) :
    List.Sublist
      (encodingActionTraceUpdate keyView.secretKey input
        (state.causalState.cache, []) result.1.1
          (result.1.2.causalState.cache, []) initialTrace)
      (initialTrace ++ result.2.encodingActions) := by
  cases input with
  | inl worldInput =>
      exact globalFirstLaneExactTracedOracleTraceSublist_holds table keyView
        worldInput state initialTrace result hresult
  | inr request =>
      exact globalFirstLaneExactTracedSigningImpl_trace_sublist table keyView
        request state initialTrace result hresult

theorem globalFirstLaneLiftRevealProbe_mem_eagerTrace_support
    (table : GlobalChainValueIndex → Digest)
    (computation : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex) α)
    (result : α ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneLiftRevealProbe computation)).run)) :
    (result.1, result.2.chainActions) ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        computation).run) := by
  rw [← globalFirstLaneErase_liftRevealProbe computation,
    ← simulate_globalFirstLaneEagerTrace_chainProjection, support_map]
  exact ⟨result, hresult, rfl⟩

theorem globalFirstLaneUniformImpl_run
    (n : Nat) (state : GlobalCausalHashState) :
    (globalFirstLaneUniformImpl n).run state = (do
      let output ← FirstLaneOracleSimulation.uniformQuery n
      pure (output, state)) := by
  rfl

theorem globalFirstLaneUniformImpl_validSignLeafIndices_eq_nil
    (table : GlobalChainValueIndex → Digest) (n : Nat)
    (state : GlobalCausalHashState)
    (result : (Fin (n + 1) × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneUniformImpl n).run state)).run)) :
    CappedEncodingMonitor.validObservedSignLeafIndices
      result.2.encodingActions = [] := by
  rw [globalFirstLaneUniformImpl_run] at hresult
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨head, hhead, htail⟩ := hresult
  simp [FirstLaneOracleSimulation.uniformQuery,
    FirstLaneOracleSimulation.eagerTraceImpl,
    FirstLaneOracleSimulation.eagerImpl,
    FirstLaneOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
  obtain ⟨output, _houtput, rfl⟩ := hhead
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at htail
  subst result
  simp [CappedEncodingMonitor.validObservedSignLeafIndices,
    FirstLaneOracleSimulation.ActionTrace.encodingActions,
    CappedEncodingMonitor.validActions,
    EncodingMonitor.observedSignLeafIndices]

theorem globalFirstLaneHashRun_validSignLeafIndices_eq_nil
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey)
    (input : HashInput) (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        (globalFirstLaneAttackerHashQueryRun secretKey input state)
        ).run)) :
    CappedEncodingMonitor.validObservedSignLeafIndices
      result.2.encodingActions = [] := by
  cases hleafIndex : encodingInputLeafIndex? secretKey.parameter input with
  | none =>
      rw [globalFirstLaneAttackerHashQueryRun_eq_none secretKey
        input state hleafIndex] at hresult
      have htrace := globalFirstLaneLiftRevealProbe_encodingActions_eq_nil table
        ((globalCausalAttackerHashQuery secretKey input).run state)
          result hresult
      rw [htrace]
      simp [CappedEncodingMonitor.validObservedSignLeafIndices,
        CappedEncodingMonitor.validActions,
        EncodingMonitor.observedSignLeafIndices]
  | some leafIndex =>
      rw [globalFirstLaneAttackerHashQueryRun_eq_some secretKey
        input state leafIndex hleafIndex] at hresult
      have htrace := globalFirstLaneAttackerHashQueryAtLeafIndex_trace table
        secretKey input state leafIndex result hresult
      rw [htrace]
      split
      · exact CappedEncodingMonitor.validObservedSignLeafIndices_singleton_query
          leafIndex result.1.1
      · rfl

theorem globalExactTracedLift_eager_support_decompose
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input ×
      GlobalDirectTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView input base).run state)).run)) :
    ∃ baseResult : ((OracleWorld + SigningSpec).Range input ×
        GlobalCausalHashState) ×
          FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run state.causalState)).run) ∧
      result = ((baseResult.1.1,
        globalExactTracedNextState keyView input state baseResult.1.1
          baseResult.1.2), baseResult.2) := by
  unfold globalExactTracedLift at hresult
  rw [StateT.run_mk, simulateQ_map, WriterT.run_map', support_map] at hresult
  obtain ⟨baseResult, hbase, heq⟩ := hresult
  exact ⟨baseResult, hbase, heq.symm⟩

theorem globalFirstLaneExactTracedMappedAdversaryImpl_hash_eq_run
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : HashInput) :
    globalFirstLaneExactTracedMappedAdversaryImpl keyView
        (.inl (.inr input)) =
      globalExactTracedLift keyView (.inl (.inr input))
        (StateT.mk (globalFirstLaneAttackerHashQueryRun
          keyView.secretKey input)) := by
  rfl

theorem globalExactTracedHash_validSignLeafIndices_eq_nil
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : HashInput)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      Digest)
    (state : GlobalDirectTracedState)
    (result : (Digest × GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView (.inl (.inr input)) base).run
          state)).run))
    (hnil : ∀ baseResult,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run state.causalState)).run) →
      CappedEncodingMonitor.validObservedSignLeafIndices
        baseResult.2.encodingActions = []) :
    CappedEncodingMonitor.validObservedSignLeafIndices
      result.2.encodingActions = [] := by
  obtain ⟨baseResult, hbase, hresultEq⟩ :=
    globalExactTracedLift_eager_support_decompose table keyView
      (.inl (.inr input)) base state result hresult
  have htraceEq := congrArg (fun candidate =>
    CappedEncodingMonitor.validObservedSignLeafIndices
      candidate.2.encodingActions) hresultEq
  exact htraceEq.trans (hnil baseResult hbase)

theorem globalExactTracedHash_validSignLeafIndices_step
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : HashInput)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      Digest)
    (state : GlobalDirectTracedState)
    (result : (Digest × GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView (.inl (.inr input)) base).run
          state)).run))
    (hnil : ∀ baseResult,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run state.causalState)).run) →
      CappedEncodingMonitor.validObservedSignLeafIndices
        baseResult.2.encodingActions = []) :
    List.Sublist
      ((state.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignLeafIndices
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  have htrace :=
    globalExactTracedHash_validSignLeafIndices_eq_nil table keyView
      input base state result hresult hnil
  obtain ⟨_baseResult, _hbase, hresultEq⟩ :=
    globalExactTracedLift_eager_support_decompose table keyView
      (.inl (.inr input)) base state result hresult
  have hstateEq : result.1.2.attackerTrace =
      state.attackerTrace ++ [AttackerAction.hash input] := by
    have hstateEq' := congrArg (fun candidate =>
      candidate.1.2.attackerTrace) hresultEq
    simpa [globalExactTracedNextState, attackerActionFragment] using hstateEq'
  have hstate : result.1.2.attackerTrace.toSigningLog.map
      (fun entry => entry.1.epoch) =
      state.attackerTrace.toSigningLog.map (fun entry => entry.1.epoch) := by
    rw [hstateEq, AttackerActionTrace.toSigningLog_append, List.map_append]
    simp [AttackerActionTrace.toSigningLog, AttackerAction.signingEntry?]
  rw [htrace, List.append_nil, hstate]

theorem globalExactTracedLift_oracle_validSignLeafIndices_step
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (worldInput : OracleWorld.Domain)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      (OracleWorld.Range worldInput))
    (initialState : GlobalDirectTracedState)
    (result : (OracleWorld.Range worldInput ×
      GlobalDirectTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView (.inl worldInput) base).run
          initialState)).run))
    (hnil : ∀ baseResult,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run initialState.causalState)).run) →
      CappedEncodingMonitor.validObservedSignLeafIndices
        baseResult.2.encodingActions = []) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignLeafIndices
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  obtain ⟨baseResult, hbase, hresultEq⟩ :=
    globalExactTracedLift_eager_support_decompose table keyView
      (.inl worldInput) base initialState result hresult
  have houtputEq : result.1.1 = baseResult.1.1 := by
    simpa using congrArg (fun candidate => candidate.1.1) hresultEq
  have hstate : result.1.2.attackerTrace =
      initialState.attackerTrace ++
        attackerActionFragment (.inl worldInput) result.1.1 := by
    have hstateEq := congrArg (fun candidate =>
      candidate.1.2.attackerTrace) hresultEq
    simpa [globalExactTracedNextState, houtputEq] using hstateEq
  have htrace : CappedEncodingMonitor.validObservedSignLeafIndices
      result.2.encodingActions = [] := by
    have htraceEq := congrArg (fun candidate =>
      CappedEncodingMonitor.validObservedSignLeafIndices
        candidate.2.encodingActions) hresultEq
    rw [htraceEq]
    exact hnil baseResult hbase
  rw [htrace, List.append_nil, hstate,
    AttackerActionTrace.toSigningLog_append, List.map_append]
  simp [attackerActionFragment, AttackerActionTrace.toSigningLog,
    AttackerAction.signingEntry?]

theorem globalExactTracedLift_signing_validSignLeafIndices_step
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      (SigningSpec.Range request))
    (initialState : GlobalDirectTracedState)
    (result : (SigningSpec.Range request × GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalExactTracedLift keyView (.inr request) base).run
          initialState)).run))
    (hsub : ∀ baseResult,
      baseResult ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (base.run initialState.causalState)).run) →
      List.Sublist (CappedEncodingMonitor.validObservedSignLeafIndices
        baseResult.2.encodingActions) [request.epoch]) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignLeafIndices
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  obtain ⟨baseResult, hbase, hresultEq⟩ :=
    globalExactTracedLift_eager_support_decompose table keyView
      (.inr request) base initialState result hresult
  have houtputEq : result.1.1 = baseResult.1.1 := by
    simpa using congrArg (fun candidate => candidate.1.1) hresultEq
  have hstate : result.1.2.attackerTrace =
      initialState.attackerTrace ++
        attackerActionFragment (.inr request) result.1.1 := by
    have hstateEq := congrArg (fun candidate =>
      candidate.1.2.attackerTrace) hresultEq
    simpa [globalExactTracedNextState, houtputEq] using hstateEq
  have htraceSub : List.Sublist
      (CappedEncodingMonitor.validObservedSignLeafIndices
        result.2.encodingActions) [request.epoch] := by
    have htraceEq := congrArg (fun candidate =>
      CappedEncodingMonitor.validObservedSignLeafIndices
        candidate.2.encodingActions) hresultEq
    rw [htraceEq]
    exact hsub baseResult hbase
  have happended := (List.Sublist.refl
    (initialState.attackerTrace.toSigningLog.map
      fun entry => entry.1.epoch)).append htraceSub
  rw [hstate]
  simpa [AttackerActionTrace.toSigningLog_append,
    attackerActionFragment, AttackerActionTrace.toSigningLog,
    AttackerAction.signingEntry?] using happended

theorem globalFirstLaneExactTracedMappedAdversaryImpl_uniform_validSignLeafIndices_step
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (n : Nat)
    (initialState : GlobalDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
      GlobalDirectTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedMappedAdversaryImpl keyView
          (.inl (.inl n))).run initialState)).run)) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignLeafIndices
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  unfold globalFirstLaneExactTracedMappedAdversaryImpl
    globalFirstLaneExactTracedOracleImpl at hresult
  apply globalExactTracedLift_oracle_validSignLeafIndices_step table
    keyView (.inl n)
    (StateT.mk fun causalState =>
      globalFirstLaneOracleExecution keyView (.inl n) causalState)
    initialState result hresult
  intro baseResult hbase
  exact globalFirstLaneUniformImpl_validSignLeafIndices_eq_nil table n
    initialState.causalState baseResult hbase

theorem globalFirstLaneExactTracedMappedAdversaryImpl_signing_validSignLeafIndices_step
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest)
    (initialState : GlobalDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range (.inr request) ×
      GlobalDirectTracedState) ×
        FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((globalFirstLaneExactTracedMappedAdversaryImpl keyView
          (.inr request)).run initialState)).run)) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignLeafIndices
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  unfold globalFirstLaneExactTracedMappedAdversaryImpl
    globalFirstLaneExactTracedSigningImpl at hresult
  apply globalExactTracedLift_signing_validSignLeafIndices_step table
    keyView request (globalFirstLaneSigningImpl keyView request)
      initialState result hresult
  intro baseResult hbase
  exact globalFirstLaneSigningQuery_validSignLeafIndices_sublist_singleton table
    keyView request initialState.causalState baseResult hbase

theorem globalFirstLaneExactTracedMappedAdversary_validSignLeafIndices_sublist_of_hashRun
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (hashRun : HashInput → GlobalCausalHashState →
      OracleComp GlobalFirstLaneWorld (Digest × GlobalCausalHashState))
    (hhashEq : ∀ input,
      globalFirstLaneExactTracedMappedAdversaryImpl keyView
          (.inl (.inr input)) =
        globalExactTracedLift keyView (.inl (.inr input))
          (StateT.mk (hashRun input)))
    (hhashNil : ∀ input state result,
      result ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (hashRun input state)).run) →
      CappedEncodingMonitor.validObservedSignLeafIndices
        result.2.encodingActions = [])
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : GlobalDirectTracedState)
    (result : (α × GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ
          (globalFirstLaneExactTracedMappedAdversaryImpl keyView)
            computation).run initialState)).run)) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignLeafIndices
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  apply simulateQ_eagerTrace_support_invariant table
    (globalFirstLaneExactTracedMappedAdversaryImpl keyView)
    (fun initial trace final => List.Sublist
      ((initial.attackerTrace.toSigningLog.map fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignLeafIndices trace.encodingActions)
      (final.attackerTrace.toSigningLog.map fun entry => entry.1.epoch))
  · intro state
    simp [CappedEncodingMonitor.validObservedSignLeafIndices,
      FirstLaneOracleSimulation.ActionTrace.encodingActions,
      CappedEncodingMonitor.validActions, EncodingMonitor.observedSignLeafIndices]
  · intro initial middle final headTrace tailTrace hhead htail
    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
      CappedEncodingMonitor.validObservedSignLeafIndices_append]
    simpa [List.append_assoc] using
      (hhead.append (List.Sublist.refl
        (CappedEncodingMonitor.validObservedSignLeafIndices
          tailTrace.encodingActions))).trans htail
  · intro input state stepResult hstep
    cases input with
    | inl worldInput =>
        cases worldInput with
        | inl n =>
            exact
              globalFirstLaneExactTracedMappedAdversaryImpl_uniform_validSignLeafIndices_step
                table keyView n state stepResult hstep
        | inr hashInput =>
            rw [hhashEq] at hstep
            apply globalExactTracedHash_validSignLeafIndices_step table keyView
              hashInput (StateT.mk (hashRun hashInput)) state stepResult hstep
            intro baseResult hbase
            exact hhashNil hashInput state.causalState baseResult hbase
    | inr request =>
        exact
          globalFirstLaneExactTracedMappedAdversaryImpl_signing_validSignLeafIndices_step
            table keyView request state stepResult hstep
  · exact hresult

theorem globalFirstLaneExactTracedMappedAdversary_validSignLeafIndices_sublist
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialState : GlobalDirectTracedState)
    (result : (α × GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ
          (globalFirstLaneExactTracedMappedAdversaryImpl keyView)
            computation).run initialState)).run)) :
    List.Sublist
      ((initialState.attackerTrace.toSigningLog.map
          fun entry => entry.1.epoch) ++
        CappedEncodingMonitor.validObservedSignLeafIndices
          result.2.encodingActions)
      (result.1.2.attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch) := by
  exact
    globalFirstLaneExactTracedMappedAdversary_validSignLeafIndices_sublist_of_hashRun
      table keyView
        (globalFirstLaneAttackerHashQueryRun keyView.secretKey)
        (globalFirstLaneExactTracedMappedAdversaryImpl_hash_eq_run keyView)
        (globalFirstLaneHashRun_validSignLeafIndices_eq_nil table
          keyView.secretKey)
        computation initialState result hresult

set_option maxRecDepth 1000000

theorem globalExactTracedLift_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState
      (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalDirectTracedState)
    (fuel : Nat)
    (hbase : (base.run state.causalState).IsQueryBoundP
      FirstLaneOracleSimulation.IsHazardQuery fuel) :
    ((globalExactTracedLift keyView input base).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery fuel := by
  unfold globalExactTracedLift
  simp only [StateT.run_mk]
  rw [map_eq_bind_pure_comp]
  apply OracleComp.isQueryBoundP_bind (n := fuel) (m := 0) hbase
  intro result _hresult
  exact OracleComp.isQueryBoundP_pure
    (p := FirstLaneOracleSimulation.IsHazardQuery) _ 0

theorem globalFirstLaneExactTracedOracleImpl_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : OracleWorld.Domain)
    (state : GlobalDirectTracedState) :
    ((globalFirstLaneExactTracedOracleImpl keyView input).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        (if input matches .inr _ then 1 else 0) := by
  unfold globalFirstLaneExactTracedOracleImpl
  apply globalExactTracedLift_hazardBound
  exact globalFirstLaneOracleExecution_hazardBound keyView input
    state.causalState

theorem globalFirstLaneExactTracedSigningImpl_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest)
    (state : GlobalDirectTracedState) :
    ((globalFirstLaneExactTracedSigningImpl keyView request).run state)
      |>.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery 0 := by
  unfold globalFirstLaneExactTracedSigningImpl
  apply globalExactTracedLift_hazardBound
  exact globalFirstLaneSigningImpl_hazardBound keyView request
    state.causalState

theorem globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalDirectTracedState) :
    ((globalFirstLaneExactTracedMappedAdversaryImpl keyView input).run
      state).IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery
        (directHashActionCost input) := by
  rcases input with (worldInput | request)
  · rcases worldInput with uniformInput | hashInput
    · unfold globalFirstLaneExactTracedMappedAdversaryImpl
      simpa [directHashActionCost] using
        globalFirstLaneExactTracedOracleImpl_hazardBound keyView
          (.inl uniformInput) state
    · unfold globalFirstLaneExactTracedMappedAdversaryImpl
      simpa [directHashActionCost] using
        globalFirstLaneExactTracedOracleImpl_hazardBound keyView
          (.inr hashInput) state
  · unfold globalFirstLaneExactTracedMappedAdversaryImpl
    simpa [directHashActionCost] using
      globalFirstLaneExactTracedSigningImpl_hazardBound keyView request state

set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

theorem map_globalMonitored_adversary_exact_query
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState) :
    (fun result => ((result.1, GlobalDirectTracedState.mk
      result.2.1.causal result.2.2), result.2.1.trace)) <$>
        (globalMonitoredMappedAdversaryImpl
          (keyView, base) input).run state =
      (fun result : (((OracleWorld + SigningSpec).Range input ×
          GlobalDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalDirectTracedMappedAdversaryImpl keyView
            input).run (GlobalDirectTracedState.mk state.1.causal state.2))).run := by
  exact map_globalMonitored_adversary_full_query keyView base
    input state.1 state.2

theorem map_simulate_globalMonitored_exact_of_query
    {spec : OracleSpec ι}
    (table : GlobalChainValueIndex → Digest)
    (left : QueryImpl spec
      (StateT GlobalMonitoredTracedState ProbComp))
    (right : QueryImpl spec
      (StateT GlobalDirectTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))))
    (hquery : ∀ (input : spec.Domain)
      (state : GlobalMonitoredTracedState),
      (fun result : spec.Range input × GlobalMonitoredTracedState =>
        ((result.1, GlobalDirectTracedState.mk result.2.1.causal result.2.2),
          result.2.1.trace)) <$>
          (left input).run state =
        (fun result : ((spec.Range input ×
            GlobalDirectTracedState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (result.1, state.1.trace ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((right input).run
              (GlobalDirectTracedState.mk state.1.causal state.2))).run)
    (computation : OracleComp spec α)
    (state : GlobalMonitoredTracedState) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, GlobalDirectTracedState.mk result.2.1.causal result.2.2),
        result.2.1.trace)) <$>
        (simulateQ left computation).run state =
      (fun result : ((α × GlobalDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          ((simulateQ right computation).run
            (GlobalDirectTracedState.mk state.1.causal state.2))).run := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, StateT.run_bind, WriterT.run_bind', map_bind,
        simulateQ_spec_query]
      simp_rw [ih]
      let project := fun result :
          spec.Range input × GlobalMonitoredTracedState =>
        ((result.1, GlobalDirectTracedState.mk result.2.1.causal result.2.2),
          result.2.1.trace)
      let tail := fun head : ((spec.Range input ×
          GlobalDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (fun result => (result.1, head.2 ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
            ((simulateQ right (next head.1.1)).run head.1.2)).run
      change (do
        let head ← (left input).run state
        tail (project head)) = _
      rw [← bind_map_left project]
      have hhead := hquery input state
      change project <$> (left input).run state = _ at hhead
      rw [hhead, bind_map_left]
      apply bind_congr
      intro head
      simp [tail, Functor.map_map, List.append_assoc]

theorem map_simulate_globalMonitored_adversary_exact
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredTracedState) :
    (fun result : α × GlobalMonitoredTracedState =>
      ((result.1, GlobalDirectTracedState.mk result.2.1.causal result.2.2),
        result.2.1.trace)) <$>
        (simulateQ (globalMonitoredMappedAdversaryImpl
          (keyView, base)) computation).run state =
      (fun result : ((α × GlobalDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.1.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((simulateQ
            (globalDirectTracedMappedAdversaryImpl keyView)
            computation).run
              (GlobalDirectTracedState.mk state.1.causal state.2))).run := by
  apply map_simulate_globalMonitored_exact_of_query
  exact map_globalMonitored_adversary_exact_query keyView base

theorem globalExactEncodingEvent_implies_combinedHit
    (table : GlobalChainValueIndex → Digest)
    (encodingTrace : EncodingActionTrace)
    (attackerTrace : AttackerActionTrace)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hencodingSub : List.Sublist encodingTrace trace.encodingActions)
    (hvalidSub : List.Sublist
      (CappedEncodingMonitor.validObservedSignLeafIndices
        trace.encodingActions)
      (attackerTrace.toSigningLog.map
        fun entry => entry.1.epoch))
    (hvalid : SigningTranscript.Valid attackerTrace.toSigningLog)
    (hhit : CappedEncodingMonitor.runObserved EncodingMonitor.State.empty
      encodingTrace = true) :
    FirstLaneOracleSimulation.CombinedHit table trace := by
  apply Or.inl
  have hnodup :
      (CappedEncodingMonitor.validObservedSignLeafIndices
        trace.encodingActions).Nodup := by
    exact hvalidSub.nodup hvalid
  exact CappedEncodingMonitor.runObserved_empty_eq_true_mono_sublist
    hencodingSub hnodup hhit

end XmssSecurity.Generic.CappedChain
