import XmssSecurity.Proof.Generic.CappedGlobalChainReplay
import XmssSecurity.Proof.Generic.CappedGlobalCausalUniformTrace
import XmssSecurity.Proof.Generic.CappedChain.SourceDirectTrace
import XmssSecurity.Proof.Generic.CappedChain.ReturnedChainValueCoverage
import XmssSecurity.Proof.Generic.EncodingHashCacheReplay
import XmssSecurity.Proof.Generic.RunObservedAppend

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.Generic.CappedChain

variable [Code]

theorem relTriple_programmed_monitoredGlobalUniformQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalMonitoredCausalState)
    (hstate : GlobalMonitoredFilteredStateRelation left right leftCache
      rightState)
    (n : Nat) :
    RelTriple
      ((fun output : Fin (n + 1) => (output, leftCache)) <$>
        (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
      ((monitorGlobalCausalTrace fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
          ((globalCausalUniformImpl n).run causalState)).run).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.bad right.2) := by
  rcases hstate with
    ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal, hretained⟩
  apply relTriple_monitorGlobalCausalTrace_of_filtered_until_hit left right
    _ _ rightState monitor hmonitor hmonitorAgrees hrevealed
  · rw [simulate_eagerTrace_globalCausalUniformImpl]
    have hmapped : RelTriple
        ((fun output : Fin (n + 1) => (output, leftCache)) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
        ((fun output : Fin (n + 1) =>
          ((output, rightState.causal),
            ([] : RevealProbeOracleSimulation.ActionTrace
              GlobalChainValueIndex))) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
        (fun leftResult rightResult =>
          leftResult.1 = rightResult.1.1 ∧
            GlobalFilteredCausalStateRelation left right leftResult.2
              rightResult.1.2) := by
      apply relTriple_map
      apply relTriple_post_mono
        (relTriple_refl
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact ⟨rfl, hcausal⟩
    apply relTriple_post_mono hmapped
    intro leftResult rightResult hresult
    exact Or.inl hresult
  · intro result hresult
    rw [simulate_eagerTrace_globalCausalUniformImpl, support_map] at hresult
    obtain ⟨output, _houtput, rfl⟩ := hresult
    exact ⟨by trivial, ReplaysCausalReveals.nil rightState.causal.revealed⟩
  · intro result hresult
    rw [simulate_eagerTrace_globalCausalUniformImpl, support_map] at hresult
    obtain ⟨output, _houtput, rfl⟩ := hresult
    exact hretained

abbrev GlobalMonitoredTracedState :=
  GlobalMonitoredCausalState × AttackerActionTrace

def GlobalMonitoredTracedStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState) : Prop :=
  GlobalMonitoredFilteredStateRelation left right leftState.1 rightState.1 ∧
    leftState.2 = rightState.2

noncomputable def globalMonitoredBaseMappedAdversaryImpl
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalMonitoredCausalState ProbComp) := fun input =>
  match input with
  | .inl (.inl n) =>
      monitorGlobalCausalTrace fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
          ((globalCausalUniformImpl n).run causalState)).run
  | .inl (.inr hashInput) =>
      monitorGlobalCausalTrace fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
          ((globalCausalAttackerHashQuery right.1.secretKey
            hashInput).run causalState)).run
  | .inr request =>
      monitorGlobalCausalTrace fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.2)
          (globalFilteredCausalSigningQuery right.1 request
            causalState)).run

noncomputable def globalMonitoredMappedAdversaryImpl
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalMonitoredTracedState ProbComp) :=
  actionTracedStateImpl (globalMonitoredBaseMappedAdversaryImpl right)
    attackerActionFragment

theorem relTriple_globalActionTracedState_until_bad
    (input : (OracleWorld + SigningSpec).Domain)
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftImpl : QueryImpl (OracleWorld + SigningSpec)
      (StateT (QueryCache HashSpec) ProbComp))
    (rightImpl : QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalMonitoredCausalState ProbComp))
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState)
    (htrace : leftState.2 = rightState.2)
    (hcouple : RelTriple
      ((leftImpl input).run leftState.1)
      ((rightImpl input).run rightState.1)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.bad right.2)) :
    RelTriple
      ((actionTracedStateImpl leftImpl attackerActionFragment input).run
        leftState)
      ((actionTracedStateImpl rightImpl attackerActionFragment input).run
        rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad right.2) := by
  let wrapLeft := fun result : (OracleWorld + SigningSpec).Range input ×
      QueryCache HashSpec => (result.1,
    (result.2, leftState.2 ++ attackerActionFragment input result.1))
  let wrapRight := fun result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredCausalState => (result.1,
    (result.2, rightState.2 ++ attackerActionFragment input result.1))
  let post := fun leftResult : (OracleWorld + SigningSpec).Range input ×
      SourceTracedState => fun rightResult :
      (OracleWorld + SigningSpec).Range input × GlobalMonitoredTracedState =>
    (leftResult.1 = rightResult.1 ∧
      GlobalMonitoredTracedStateRelation left right leftResult.2
        rightResult.2) ∨ rightResult.2.1.bad right.2
  have hprepared : RelTriple
      ((leftImpl input).run leftState.1)
      ((rightImpl input).run rightState.1)
      (fun leftResult rightResult =>
        post (wrapLeft leftResult) (wrapRight rightResult)) := by
    apply relTriple_post_mono hcouple
    intro leftResult rightResult hresult
    rcases hresult with hgood | hbad
    · refine Or.inl ⟨hgood.1, hgood.2, ?_⟩
      change leftState.2 ++ attackerActionFragment input leftResult.1 =
        rightState.2 ++ attackerActionFragment input rightResult.1
      rw [htrace, hgood.1]
    · exact Or.inr hbad
  unfold actionTracedStateImpl
  simpa [wrapLeft, wrapRight, post, map_eq_bind_pure_comp] using
    (relTriple_map (R := post) (f := wrapLeft) (g := wrapRight) hprepared)

theorem relTriple_programmed_globalMonitored_action
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftState : SourceTracedState)
    (rightState : GlobalMonitoredTracedState)
    (hstate : GlobalMonitoredTracedStateRelation left right leftState
      rightState)
    (input : (OracleWorld + SigningSpec).Domain) :
    RelTriple
      ((sourceDirectTracedMappedAdversaryImpl left.publicKey
        (Concrete.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((globalMonitoredMappedAdversaryImpl right input).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredTracedStateRelation left right leftResult.2
            rightResult.2) ∨ rightResult.2.1.bad right.2) := by
  have liftBase := relTriple_globalActionTracedState_until_bad input left
    right (sourceDirectMappedAdversaryImpl left.publicKey
      (Concrete.materializePrecomputation left.cache left.secretKey))
      (globalMonitoredBaseMappedAdversaryImpl right) leftState rightState
        hstate.2
  rcases input with (worldInput | request)
  · rcases worldInput with n | hashInput
    · apply liftBase
      simpa [sourceDirectMappedAdversaryImpl,
        unloggedMappedAdversaryImpl_apply_inl,
        globalMonitoredBaseMappedAdversaryImpl, romImpl, unifFwdImpl,
        OracleComp.liftM_run_StateT] using
        (relTriple_programmed_monitoredGlobalUniformQuery left right
          leftState.1 rightState.1 hstate.1 n)
    · apply liftBase
      simpa [sourceDirectMappedAdversaryImpl,
        unloggedMappedAdversaryImpl_apply_inl,
        globalMonitoredBaseMappedAdversaryImpl, romImpl] using
        (relTriple_programmed_monitoredGlobalAttackerHashQuery_until_hit left
          right hrel hleftSupport hrightSupport leftState.1 rightState.1
            hstate.1 hashInput)
  · apply liftBase
    simpa [sourceDirectMappedAdversaryImpl,
      unloggedMappedAdversaryImpl_apply_inr,
      globalMonitoredBaseMappedAdversaryImpl] using
      (relTriple_programmed_monitoredGlobalSigningQuery left right hrel
        hleftSupport hrightSupport leftState.1 rightState.1 hstate.1 request)

theorem globalMonitoredTracedStateRelation_initial
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    GlobalMonitoredTracedStateRelation left right (left.cache, [])
      (⟨globalFilteredCausalKeygenState right.1, []⟩, []) := by
  refine ⟨globalMonitoredFilteredStateRelation_initial left right left.cache
    (globalFilteredCausalKeygenState right.1) ?_ ?_ ?_, rfl⟩
  · exact programmedGlobal_filteredKeygen_stateRelation left right hrel
      hleftSupport hrightSupport
  · exact globalFilteredCausalKeygenState_merkleRetained right.1
  · intro index
    simp [globalFilteredCausalKeygenState]

def GlobalCausalRevealsCovered
    (covered : Set GlobalChainValueIndex)
    (state : GlobalCausalHashState) : Prop :=
  ∀ index value, state.revealed index = some value → index ∈ covered

def GlobalCausalTraceRevealsCovered
    (covered : Set GlobalChainValueIndex)
    (trace : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex) : Prop :=
  ∀ index value,
    RevealProbeOracleSimulation.ObservedAction.reveal index value ∈ trace →
      index ∈ covered

def GlobalCausalResultCovered
    (covered : Set GlobalChainValueIndex)
    (result : (α × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace
        GlobalChainValueIndex) : Prop :=
  GlobalCausalRevealsCovered covered result.1.2 ∧
    GlobalCausalTraceRevealsCovered covered result.2

def GlobalChainValueIndicesForwardClosed
    (covered : Set GlobalChainValueIndex) : Prop :=
  ∀ chain leafIndex earlier later,
    (chain, leafIndex, earlier) ∈ covered → earlier ≤ later →
      (chain, leafIndex, later) ∈ covered

theorem GlobalCausalTraceRevealsCovered.append
    {covered : Set GlobalChainValueIndex}
    {left right : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex}
    (hleft : GlobalCausalTraceRevealsCovered covered left)
    (hright : GlobalCausalTraceRevealsCovered covered right) :
    GlobalCausalTraceRevealsCovered covered (left ++ right) := by
  intro index value hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft index value hmem
  · exact hright index value hmem

theorem GlobalCausalRevealsCovered.setCache
    {covered : Set GlobalChainValueIndex} {state : GlobalCausalHashState}
    (hcovered : GlobalCausalRevealsCovered covered state)
    (cache : QueryCache HashSpec) :
    GlobalCausalRevealsCovered covered { state with cache := cache } := by
  exact hcovered

theorem GlobalCausalRevealsCovered.recordedState
    {covered : Set GlobalChainValueIndex} {state : GlobalCausalHashState}
    (hcovered : GlobalCausalRevealsCovered covered state)
    (secretKey : SecretKey) (input : HashInput) :
    GlobalCausalRevealsCovered covered
      (globalCausalRecordedState secretKey input state) := by
  intro index value hrevealed
  apply hcovered index value
  simpa only [globalCausalRecordedState_revealed] using hrevealed

theorem GlobalCausalRevealsCovered.recordReveal
    {covered : Set GlobalChainValueIndex} {state : GlobalCausalHashState}
    (hcovered : GlobalCausalRevealsCovered covered state)
    (index : GlobalChainValueIndex) (value : Digest)
    (hindex : index ∈ covered) :
    GlobalCausalRevealsCovered covered (state.recordReveal index value) := by
  intro candidate candidateValue hrevealed
  by_cases heq : candidate = index
  · simpa [heq] using hindex
  · apply hcovered candidate candidateValue
    simpa [GlobalCausalHashState.recordReveal,
      Function.update_of_ne heq] using hrevealed

theorem GlobalCausalRevealsCovered.revealResultState
    {covered : Set GlobalChainValueIndex} {state : GlobalCausalHashState}
    (hcovered : GlobalCausalRevealsCovered covered state)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest)
    (hindex : index ∈ covered) :
    GlobalCausalRevealsCovered covered
      (globalFilteredCausalRevealResultState secretKey input state index
        value) := by
  intro candidate candidateValue hrevealed
  by_cases heq : candidate = index
  · subst candidate
    exact hindex
  · apply hcovered candidate candidateValue
    simpa [globalFilteredCausalRevealResultState,
      Function.update_of_ne heq] using hrevealed

noncomputable def GlobalReturnedChainValueCovered
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) : Set GlobalChainValueIndex :=
  fun index =>
    index.2 ∈ ReturnedChainValueCovered cache secretKey log index.1

theorem globalReturnedChainValueCovered_forwardClosed
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) :
    GlobalChainValueIndicesForwardClosed
      (GlobalReturnedChainValueCovered cache secretKey log) := by
  intro chain leafIndex earlier later hmem hle
  exact returnedChainValueCovered_forwardClosed cache secretKey log chain
    leafIndex earlier later hmem hle

theorem globalReturnedChainValueCovered_contains_returned
    (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) (request : SignRequest)
    (signature : Signature) (encoding : Encoding)
    (hreturned : SigningTranscript.Returned log request signature)
    (hdecode : Concrete.CacheView.decodedEncoding cache secretKey.parameter request.epoch
        (request.message, signature.randomness) = some encoding)
    (chain : ChainIndex) :
    (chain, request.epoch, encoding chain) ∈
      GlobalReturnedChainValueCovered cache secretKey log := by
  exact returnedChainValueCovered_contains_returned cache secretKey log chain
    request signature encoding hreturned hdecode

theorem globalReturnedChainValueCovered_of_comparableCaches
    (parameter : PublicParameter)
    (leftCache rightCache : QueryCache HashSpec)
    (leftSecret rightSecret : SecretKey)
    (leftLog rightLog : QueryLog SigningSpec)
    (hleftParameter : leftSecret.parameter = parameter)
    (hrightParameter : rightSecret.parameter = parameter)
    (hlogs : rightLog = leftLog)
    (hcaches : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) leftCache rightCache)
    (index : GlobalChainValueIndex)
    (hindex : index ∈
      GlobalReturnedChainValueCovered rightCache rightSecret rightLog) :
    index ∈ GlobalReturnedChainValueCovered leftCache leftSecret
      leftLog := by
  change index.2 ∈ ReturnedChainValueCovered rightCache rightSecret
    rightLog index.1 at hindex
  change index.2 ∈ ReturnedChainValueCovered leftCache leftSecret
    leftLog index.1
  rw [returnedChainValueCovered_iff] at hindex ⊢
  obtain ⟨request, signature, encoding, hreturned, hdecode, hleafIndex,
    hdigit⟩ := hindex
  have hhash :
      Concrete.CacheView.decodedEncoding leftCache leftSecret.parameter
          request.epoch (request.message, signature.randomness) =
        Concrete.CacheView.decodedEncoding rightCache rightSecret.parameter
          request.epoch (request.message, signature.randomness) := by
    rw [hleftParameter, hrightParameter]
    unfold Concrete.CacheView.decodedEncoding
    rw [hcaches _ ⟨request.epoch, request.message, signature.randomness,
      rfl⟩]
  refine ⟨request, signature, encoding, ?_, ?_, hleafIndex, hdigit⟩
  · simpa [hlogs] using hreturned
  · rw [hhash]
    exact hdecode

theorem globalFilteredCausalLeafHashPlan_ne_reveal
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex) :
    globalFilteredCausalLeafHashPlan secretKey input state ≠ .reveal index := by
  unfold globalFilteredCausalLeafHashPlan
  split <;> try { intro h; cases h }
  split <;> try { intro h; cases h }
  split <;> try { intro h; cases h }
  split <;> intro h <;> cases h

theorem globalFilteredCausalUncachedHashPlan_reveal_has_predecessor
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest))
    (index : GlobalChainValueIndex)
    (hplan : globalFilteredCausalUncachedAttackerHashPlan secretKey input state
      probe = .reveal index) :
    ∃ predecessor value,
      state.revealed predecessor = some value ∧
      predecessor.1 = index.1 ∧
      predecessor.2.1 = index.2.1 ∧
      predecessor.2.2.val + 1 = index.2.2.val := by
  cases probe with
  | none =>
      exact (globalFilteredCausalLeafHashPlan_ne_reveal secretKey input state
        index hplan).elim
  | some probe =>
      obtain ⟨predecessor, target⟩ := probe
      cases hrevealed : state.revealed predecessor with
      | none =>
          simp only [globalFilteredCausalUncachedAttackerHashPlan,
            hrevealed] at hplan
          split at hplan <;> cases hplan
      | some value =>
          by_cases htarget : value = target
          · subst target
            by_cases hnext : predecessor.2.2.val + 1 < chainLength
            · simp only [globalFilteredCausalUncachedAttackerHashPlan,
                hrevealed, dif_pos hnext] at hplan
              have hindex :
                  (predecessor.1, predecessor.2.1,
                    ⟨predecessor.2.2.val + 1, hnext⟩) = index :=
                GlobalFilteredCausalHashPlan.reveal.inj hplan
              subst index
              exact ⟨predecessor, value, hrevealed, rfl, rfl, rfl⟩
            · simp only [globalFilteredCausalUncachedAttackerHashPlan,
                hrevealed, dif_neg hnext] at hplan
              cases hplan
          · simp only [globalFilteredCausalUncachedAttackerHashPlan,
              hrevealed, if_neg htarget] at hplan
            cases hplan

theorem globalFilteredCausalAttackerHashPlan_reveal_has_predecessor
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .reveal index) :
    ∃ predecessor value,
      state.revealed predecessor = some value ∧
      predecessor.1 = index.1 ∧
      predecessor.2.1 = index.2.1 ∧
      predecessor.2.2.val + 1 = index.2.2.val := by
  unfold globalFilteredCausalAttackerHashPlan at hplan
  cases hcache : state.cache input with
  | some output => simp only [hcache] at hplan; cases hplan
  | none =>
      simp only [hcache] at hplan
      exact globalFilteredCausalUncachedHashPlan_reveal_has_predecessor
        secretKey input state
          (globalChainInputProbe? secretKey.parameter input) index hplan

theorem globalFilteredCausalAttackerHashPlan_reveal_mem_of_covered
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (covered : Set GlobalChainValueIndex)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .reveal index)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered) :
    index ∈ covered := by
  obtain ⟨predecessor, value, hrevealed, hchain, hleafIndex, hnext⟩ :=
    globalFilteredCausalAttackerHashPlan_reveal_has_predecessor secretKey input
      state index hplan
  apply hforward index.1 index.2.1 predecessor.2.2 index.2.2
  · rw [← hchain, ← hleafIndex]
    exact hcovered predecessor value hrevealed
  · change predecessor.2.2.val ≤ index.2.2.val
    omega

theorem simulate_eagerTrace_globalCausalAttackerHashQuery_support_covered
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : (Digest × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQuery secretKey input).run
          state)).run)) :
    GlobalCausalResultCovered covered result := by
  generalize hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
    plan
  cases plan with
  | cached output =>
      rw [globalCausalAttackerHashQuery_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered.recordedState secretKey input,
        by simp [GlobalCausalTraceRevealsCovered]⟩
  | redirect output =>
      rw [globalCausalAttackerHashQuery_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered.recordedState secretKey input |>.setCache _,
        by simp [GlobalCausalTraceRevealsCovered]⟩
  | fresh =>
      rw [globalCausalAttackerHashQuery_run, hplan,
        simulate_eagerTrace_globalCausalHashQuery, support_map] at hresult
      obtain ⟨sample, _hsample, rfl⟩ := hresult
      exact ⟨hcovered.recordedState secretKey input |>.setCache _,
        by simp [GlobalCausalTraceRevealsCovered]⟩
  | reveal index =>
      have hindex :=
        globalFilteredCausalAttackerHashPlan_reveal_mem_of_covered secretKey
          input state index covered hplan hcovered hforward
      rw [globalCausalAttackerHashQuery_run, hplan,
        simulate_eagerTrace_globalCausalRevealHashQuery] at hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      constructor
      · exact hcovered.revealResultState secretKey input index (table index)
          hindex
      · intro candidate value hmem
        simp only [List.mem_singleton,
          RevealProbeOracleSimulation.ObservedAction.reveal.injEq] at hmem
        obtain ⟨rfl, rfl⟩ := hmem
        exact hindex
  | probeThenFresh index target =>
      rw [simulate_eagerTrace_globalCausalAttackerHashQuery_probeThenFresh
        table secretKey input state index target hplan, support_map]
        at hresult
      obtain ⟨sample, _hsample, rfl⟩ := hresult
      exact ⟨hcovered.recordedState secretKey input |>.setCache _,
        by simp [GlobalCausalTraceRevealsCovered]⟩

theorem globalSignatureRevealResult_covered
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hindices : ∀ chain ∈ chains,
      (chain, request.epoch, encoding chain) ∈ covered) :
    GlobalCausalRevealsCovered covered
        (globalSignatureRevealResult table request encoding chains signature
          state).2 ∧
      GlobalCausalTraceRevealsCovered covered
        (globalSignatureRevealTrace table request encoding chains) := by
  induction chains generalizing signature state with
  | nil =>
      exact ⟨hcovered, by
        simp [globalSignatureRevealTrace,
          GlobalCausalTraceRevealsCovered]⟩
  | cons chain chains ih =>
      let index : GlobalChainValueIndex :=
        (chain, request.epoch, encoding chain)
      have hindex : index ∈ covered := hindices chain (by simp)
      have htailIndices : ∀ candidate ∈ chains,
          (candidate, request.epoch, encoding candidate) ∈ covered := by
        intro candidate hcandidate
        exact hindices candidate (List.mem_cons_of_mem chain hcandidate)
      rw [globalSignatureRevealResult, globalSignatureRevealTrace]
      have htail := ih
        (replaceSignatureChainValue signature chain (table index))
        (state.recordReveal index (table index))
        (hcovered.recordReveal index (table index) hindex) htailIndices
      constructor
      · exact htail.1
      · intro candidate value hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hhead | htailMem
        · cases hhead
          exact hindex
        · exact htail.2 candidate value htailMem

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_globalFilteredCausalSigningAttempt_support_covered_of_final
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ returnedSignature encoding chain,
      result.1.1 = some returnedSignature →
      Concrete.CacheView.decodedEncoding finalCache
          keyView.secretKey.parameter request.epoch
          (request.message, returnedSignature.randomness) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningAttempt keyView request state)).run)) :
    GlobalCausalResultCovered covered result := by
  unfold globalFilteredCausalSigningAttempt at hresult
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp,
    mem_support_bind_iff] at hresult
  obtain ⟨randomnessTrace, hrandomnessTrace, hresult⟩ := hresult
  rw [support_map] at hrandomnessTrace
  obtain ⟨randomness, _hrandomness, rfl⟩ := hrandomnessTrace
  simp only [List.nil_append] at hresult
  rw [show (Prod.map id
    (fun trace : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex => trace)) = id from rfl, id_map] at hresult
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp,
    mem_support_bind_iff] at hresult
  obtain ⟨encodedTrace, hencodedTrace, hresult⟩ := hresult
  rw [support_map] at hencodedTrace
  obtain ⟨encoded, hencoded, rfl⟩ := hencodedTrace
  simp only [List.nil_append] at hresult
  cases hdecode : Code.decodeDigest encoded.1 with
  | none =>
      simp only [hdecode, simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      exact ⟨hcovered.setCache encoded.2,
        by simp [GlobalCausalTraceRevealsCovered]⟩
  | some encoding =>
      rw [hdecode, simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_revealGlobalSignatureChains] at hresult
      simp only [pure_bind, simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      let initialSignature := Concrete.CacheReplay.signWithEncoding
        keyView.cache keyView.secretKey request.epoch randomness encoding
      let encodedState : GlobalCausalHashState := { state with cache := encoded.2 }
      let returned := globalSignatureRevealResult table request encoding
        allChains initialSignature encodedState
      have hstable : Concrete.CacheView.decodedEncoding finalCache
          keyView.secretKey.parameter request.epoch
          (request.message, randomness) = Code.decodeDigest encoded.1 := by
        apply Concrete.CacheReplay.decodedEncoding_eq_of_run_support_of_cache_le
          keyView.secretKey.parameter state.cache encoded.2 finalCache
            request.epoch request.message randomness encoded.1 hencoded
        simpa [Prod.map, returned, encodedState,
          globalSignatureRevealResult_cache]
          using hcacheLe
      have hindices : ∀ chain ∈ allChains,
          (chain, request.epoch, encoding chain) ∈ covered := by
        intro chain _hchain
        apply hdirect returned.1 encoding chain
        · rfl
        · simpa [returned, initialSignature,
            Concrete.CacheReplay.signWithEncoding,
            globalSignatureRevealResult_randomness, hstable] using hdecode
      simpa [GlobalCausalResultCovered, returned, initialSignature,
        encodedState] using
        (globalSignatureRevealResult_covered table request encoding allChains
          initialSignature encodedState covered (hcovered.setCache encoded.2)
            hindices)

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_support_covered_of_final
    (attempts : Nat) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ returnedSignature encoding chain,
      result.1.1 = some returnedSignature →
      Concrete.CacheView.decodedEncoding finalCache
          keyView.secretKey.parameter request.epoch
          (request.message, returnedSignature.randomness) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSignBoundedAttempts attempts keyView request
          state)).run)) :
    GlobalCausalResultCovered covered result := by
  induction attempts generalizing state result with
  | zero =>
      simp only [globalFilteredCausalSignBoundedAttempts, simulateQ_pure,
        WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hcovered, by simp [GlobalCausalTraceRevealsCovered]⟩
  | succ attempts ih =>
      rw [simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_succ,
        mem_support_bind_iff] at hresult
      obtain ⟨attemptResult, hattempt, hcontinuation⟩ := hresult
      cases hoption : attemptResult.1.1 with
      | some signature =>
          unfold globalFilteredCausalSignTraceContinuation at hcontinuation
          rw [hoption] at hcontinuation
          simp only [support_pure, Set.mem_singleton_iff] at hcontinuation
          subst result
          exact
            simulate_eagerTrace_globalFilteredCausalSigningAttempt_support_covered_of_final
              table keyView request state covered finalCache attemptResult
                hcovered hcacheLe hdirect hattempt
      | none =>
          unfold globalFilteredCausalSignTraceContinuation at hcontinuation
          rw [hoption, support_map] at hcontinuation
          obtain ⟨rest, hrest, rfl⟩ := hcontinuation
          have hrestCacheLe : rest.1.2.cache ≤ finalCache := hcacheLe
          have hattemptCacheLe : attemptResult.1.2.cache ≤ finalCache :=
            (simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_stateExtends
              attempts table keyView request attemptResult.1.2 rest hrest).1.trans
                hrestCacheLe
          have hattemptCovered :=
            simulate_eagerTrace_globalFilteredCausalSigningAttempt_support_covered_of_final
              table keyView request state covered finalCache attemptResult
                hcovered hattemptCacheLe (by
                  intro returnedSignature encoding chain hreturned _hdecode
                  rw [hoption] at hreturned
                  contradiction) hattempt
          have hrestCovered := ih attemptResult.1.2 rest hattemptCovered.1
            hrestCacheLe hdirect hrest
          exact ⟨hrestCovered.1,
            hattemptCovered.2.append hrestCovered.2⟩

set_option maxRecDepth 100000 in
theorem simulate_eagerTrace_globalFilteredCausalSigningQuery_support_covered_of_final
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hcovered : GlobalCausalRevealsCovered covered state)
    (hcacheLe : result.1.2.cache ≤ finalCache)
    (hdirect : ∀ returnedSignature encoding chain,
      result.1.1 = some returnedSignature →
      Concrete.CacheView.decodedEncoding finalCache
          keyView.secretKey.parameter request.epoch
          (request.message, returnedSignature.randomness) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningQuery keyView request state)).run)) :
    GlobalCausalResultCovered covered result := by
  exact
    simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_support_covered_of_final
      Code.signingAttemptLimit table keyView request state covered finalCache result
        hcovered hcacheLe hdirect hresult

theorem globalFilteredCausalAttackerHashPlan_cache_none_of_noncached
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (plan : GlobalFilteredCausalHashPlan)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state = plan)
    (hnoncached : ∀ output, plan ≠ .cached output) :
    state.cache input = none := by
  unfold globalFilteredCausalAttackerHashPlan at hplan
  cases hcache : state.cache input with
  | none => rfl
  | some output =>
      simp only [hcache] at hplan
      exact (hnoncached output hplan.symm).elim

theorem simulate_eagerTrace_globalCausalHashQuery_support_cache_le
    (table : GlobalChainValueIndex → Digest) (input : HashInput)
    (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalHashQuery input).run state)).run)) :
    state.cache ≤ result.1.2.cache := by
  rw [simulate_eagerTrace_globalCausalHashQuery, support_map] at hresult
  obtain ⟨sample, hsample, rfl⟩ := hresult
  have hsample' : sample ∈ support
      ((uniformSampleImpl.withCaching input).run state.cache) := by
    simpa [randomOracle] using hsample
  exact QueryImpl.withCaching_cache_le uniformSampleImpl input state.cache
    sample hsample'

theorem simulate_eagerTrace_globalCausalAttackerHashQuery_support_cache_le
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (result : (Digest × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQuery secretKey input).run
          state)).run)) :
    state.cache ≤ result.1.2.cache := by
  generalize hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
    plan
  cases plan with
  | cached output =>
      rw [globalCausalAttackerHashQuery_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simpa only [globalCausalRecordedState_cache] using
        (le_rfl : state.cache ≤ state.cache)
  | redirect output =>
      rw [globalCausalAttackerHashQuery_run, hplan] at hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      have habsent := globalFilteredCausalAttackerHashPlan_cache_none_of_noncached
        secretKey input state (.redirect output) hplan (by intro; simp)
      simpa [globalFilteredCausalRedirectResultState,
        globalCausalRecordedState_cache] using
          QueryCache.le_cacheQuery state.cache habsent
  | fresh =>
      rw [globalCausalAttackerHashQuery_run, hplan] at hresult
      simpa only [globalCausalRecordedState_cache] using
        (simulate_eagerTrace_globalCausalHashQuery_support_cache_le table
          input (globalCausalRecordedState secretKey input state) result hresult)
  | reveal index =>
      rw [globalCausalAttackerHashQuery_run, hplan,
        simulate_eagerTrace_globalCausalRevealHashQuery] at hresult
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      have habsent := globalFilteredCausalAttackerHashPlan_cache_none_of_noncached
        secretKey input state (.reveal index) hplan (by intro; simp)
      simpa [globalFilteredCausalRevealResultState] using
        QueryCache.le_cacheQuery state.cache habsent
  | probeThenFresh index target =>
      rw [simulate_eagerTrace_globalCausalAttackerHashQuery_probeThenFresh
        table secretKey input state index target hplan, support_map]
        at hresult
      obtain ⟨sample, hsample, rfl⟩ := hresult
      have hsample' : sample ∈ support
          ((uniformSampleImpl.withCaching input).run state.cache) := by
        simpa [randomOracle] using hsample
      simpa [globalCausalRecordedState_cache,
        GlobalCausalHashState.setCache] using
          (QueryImpl.withCaching_cache_le uniformSampleImpl input state.cache
            sample hsample')

def GlobalMonitoredCausalStateCovered
    (covered : Set GlobalChainValueIndex)
    (state : GlobalMonitoredCausalState) : Prop :=
  GlobalCausalRevealsCovered covered state.causal ∧
    GlobalCausalTraceRevealsCovered covered state.trace

theorem simulate_eagerTrace_globalCausalUniformImpl_support_state_trace
    (table : GlobalChainValueIndex → Digest) (n : Nat)
    (state : GlobalCausalHashState)
    (result : (Fin (n + 1) × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalUniformImpl n).run state)).run)) :
    result.1.2 = state ∧ result.2 = [] := by
  rw [simulate_eagerTrace_globalCausalUniformImpl, support_map] at hresult
  obtain ⟨output, _houtput, rfl⟩ := hresult
  exact ⟨rfl, rfl⟩

theorem monitorGlobalCausalTrace_support_covered
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (state : GlobalMonitoredCausalState)
    (covered : Set GlobalChainValueIndex)
    (hcovered : GlobalMonitoredCausalStateCovered covered state)
    (result : α × GlobalMonitoredCausalState)
    (hresult : result ∈ support
      ((monitorGlobalCausalTrace computation).run state))
    (hstep : ∀ raw ∈ support (computation state.causal),
      GlobalCausalResultCovered covered raw) :
    GlobalMonitoredCausalStateCovered covered result.2 := by
  rw [monitorGlobalCausalTrace_run, support_map] at hresult
  obtain ⟨raw, hraw, rfl⟩ := hresult
  have hrawCovered := hstep raw hraw
  exact ⟨hrawCovered.1, hcovered.2.append hrawCovered.2⟩

theorem globalMonitoredBaseMappedAdversaryImpl_support_cache_le
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredCausalState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredCausalState)
    (hresult : result ∈ support
      ((globalMonitoredBaseMappedAdversaryImpl right input).run state)) :
    state.causal.cache ≤ result.2.causal.cache := by
  rcases input with (n | hashInput) | request
  · unfold globalMonitoredBaseMappedAdversaryImpl at hresult
    rw [monitorGlobalCausalTrace_run, support_map] at hresult
    obtain ⟨raw, hraw, rfl⟩ := hresult
    have hstate :=
      simulate_eagerTrace_globalCausalUniformImpl_support_state_trace
        right.2 n state.causal raw hraw
    simp [globalMonitoredCausalResult, hstate.1]
  · unfold globalMonitoredBaseMappedAdversaryImpl at hresult
    rw [monitorGlobalCausalTrace_run, support_map] at hresult
    obtain ⟨raw, hraw, rfl⟩ := hresult
    exact
      simulate_eagerTrace_globalCausalAttackerHashQuery_support_cache_le
        right.2 right.1.secretKey hashInput state.causal raw hraw
  · unfold globalMonitoredBaseMappedAdversaryImpl at hresult
    rw [monitorGlobalCausalTrace_run, support_map] at hresult
    obtain ⟨raw, hraw, rfl⟩ := hresult
    exact
      (simulate_eagerTrace_globalFilteredCausalSigningQuery_stateExtends
        right.2 right.1 request state.causal raw hraw).1

set_option maxRecDepth 100000 in
theorem globalMonitoredBaseMappedAdversaryImpl_support_covered_of_final_if_hash
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredCausalState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (hcovered : GlobalMonitoredCausalStateCovered covered state)
    (hforward : (∃ hashInput, input = .inl (.inr hashInput)) →
      GlobalChainValueIndicesForwardClosed covered)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredCausalState)
    (hcacheLe : result.2.causal.cache ≤ finalCache)
    (hdirect : ∀ request signature encoding chain,
      AttackerAction.sign request (some signature) ∈
        attackerActionFragment input result.1 →
      Concrete.CacheView.decodedEncoding finalCache
          right.1.secretKey.parameter request.epoch
          (request.message, signature.randomness) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      ((globalMonitoredBaseMappedAdversaryImpl right input).run state)) :
    GlobalMonitoredCausalStateCovered covered result.2 := by
  rcases input with (n | hashInput) | request
  · unfold globalMonitoredBaseMappedAdversaryImpl at hresult
    apply monitorGlobalCausalTrace_support_covered _ state covered
      hcovered result hresult
    intro raw hraw
    have hstate :=
      simulate_eagerTrace_globalCausalUniformImpl_support_state_trace
        right.2 n state.causal raw hraw
    constructor
    · simpa [hstate.1] using hcovered.1
    · simp [hstate.2, GlobalCausalTraceRevealsCovered]
  · unfold globalMonitoredBaseMappedAdversaryImpl at hresult
    apply monitorGlobalCausalTrace_support_covered _ state covered
      hcovered result hresult
    intro raw hraw
    exact
      simulate_eagerTrace_globalCausalAttackerHashQuery_support_covered
        right.2 right.1.secretKey hashInput state.causal covered hcovered.1 (hforward ⟨hashInput, rfl⟩)
            raw hraw
  · unfold globalMonitoredBaseMappedAdversaryImpl at hresult
    rw [monitorGlobalCausalTrace_run, support_map] at hresult
    obtain ⟨raw, hraw, rfl⟩ := hresult
    have hrawCovered :=
      simulate_eagerTrace_globalFilteredCausalSigningQuery_support_covered_of_final
        right.2 right.1 request state.causal covered finalCache raw
          hcovered.1 (by
            simpa [globalMonitoredCausalResult] using hcacheLe)
          (by
            intro returnedSignature encoding chain hreturned hdecode
            apply hdirect request returnedSignature encoding chain
            · simp [globalMonitoredCausalResult, attackerActionFragment,
                hreturned]
            · exact hdecode)
          hraw
    exact ⟨hrawCovered.1, hcovered.2.append hrawCovered.2⟩

theorem globalMonitoredBaseMappedAdversaryImpl_support_covered_of_final
    (right : ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain) (state : GlobalMonitoredCausalState)
    (covered : Set GlobalChainValueIndex) (finalCache : QueryCache HashSpec)
    (hcovered : GlobalMonitoredCausalStateCovered covered state)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : (OracleWorld + SigningSpec).Range input × GlobalMonitoredCausalState)
    (hcacheLe : result.2.causal.cache ≤ finalCache)
    (hdirect : ∀ request signature encoding chain,
      AttackerAction.sign request (some signature) ∈ attackerActionFragment input result.1 →
      Concrete.CacheView.decodedEncoding finalCache right.1.secretKey.parameter request.epoch
        (request.message, signature.randomness) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support ((globalMonitoredBaseMappedAdversaryImpl right input).run state)) :
    GlobalMonitoredCausalStateCovered covered result.2 :=
  globalMonitoredBaseMappedAdversaryImpl_support_covered_of_final_if_hash right input state covered
    finalCache hcovered (fun _ => hforward) result hcacheLe hdirect hresult

theorem globalMonitoredMappedAdversaryImpl_support_cache_le
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalMonitoredMappedAdversaryImpl right input).run state)) :
    state.1.causal.cache ≤ result.2.1.causal.cache := by
  unfold globalMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (globalMonitoredBaseMappedAdversaryImpl right input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  exact globalMonitoredBaseMappedAdversaryImpl_support_cache_le right
    input state.1 baseResult hbaseResult

set_option maxRecDepth 100000 in
theorem globalMonitoredMappedAdversaryImpl_support_covered_of_final_if_hash
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (hcovered : GlobalMonitoredCausalStateCovered covered state.1)
    (hforward : (∃ hashInput, input = .inl (.inr hashInput)) →
      GlobalChainValueIndicesForwardClosed covered)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState)
    (hcacheLe : result.2.1.causal.cache ≤ finalCache)
    (hdirect : ∀ request signature encoding chain,
      AttackerAction.sign request (some signature) ∈ result.2.2 →
      Concrete.CacheView.decodedEncoding finalCache
          right.1.secretKey.parameter request.epoch
          (request.message, signature.randomness) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support
      ((globalMonitoredMappedAdversaryImpl right input).run state)) :
    GlobalMonitoredCausalStateCovered covered result.2.1 := by
  unfold globalMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (globalMonitoredBaseMappedAdversaryImpl right input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  apply globalMonitoredBaseMappedAdversaryImpl_support_covered_of_final_if_hash
    right input state.1 covered finalCache hcovered hforward baseResult hcacheLe
  · intro request signature encoding chain haction hdecode
    apply hdirect request signature encoding chain
    · exact List.mem_append_right state.2 haction
    · exact hdecode
  · exact hbaseResult

theorem globalMonitoredMappedAdversaryImpl_support_covered_of_final
    (right : ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain) (state : GlobalMonitoredTracedState)
    (covered : Set GlobalChainValueIndex) (finalCache : QueryCache HashSpec)
    (hcovered : GlobalMonitoredCausalStateCovered covered state.1)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (result : (OracleWorld + SigningSpec).Range input × GlobalMonitoredTracedState)
    (hcacheLe : result.2.1.causal.cache ≤ finalCache)
    (hdirect : ∀ request signature encoding chain,
      AttackerAction.sign request (some signature) ∈ result.2.2 →
      Concrete.CacheView.decodedEncoding finalCache right.1.secretKey.parameter request.epoch
        (request.message, signature.randomness) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (hresult : result ∈ support ((globalMonitoredMappedAdversaryImpl right input).run state)) :
    GlobalMonitoredCausalStateCovered covered result.2.1 :=
  globalMonitoredMappedAdversaryImpl_support_covered_of_final_if_hash right input state covered
    finalCache hcovered (fun _ => hforward) result hcacheLe hdirect hresult

theorem globalMonitoredMappedAdversaryImpl_preserves_cache_extension
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (initialCache : QueryCache HashSpec) :
    QueryImpl.PreservesInv (globalMonitoredMappedAdversaryImpl right)
      (fun state : GlobalMonitoredTracedState =>
        initialCache ≤ state.1.causal.cache) := by
  intro input state hstate result hresult
  exact hstate.trans
    (globalMonitoredMappedAdversaryImpl_support_cache_le right input state
      result hresult)

theorem globalMonitoredMappedAdversaryImpl_preserves_trace_extension
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (initialTrace : AttackerActionTrace) :
    QueryImpl.PreservesInv (globalMonitoredMappedAdversaryImpl right)
      (fun state : GlobalMonitoredTracedState =>
        ∀ action ∈ initialTrace, action ∈ state.2) := by
  intro input state hstate result hresult
  unfold globalMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (globalMonitoredBaseMappedAdversaryImpl right input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, _hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  intro action haction
  exact List.mem_append_left _ (hstate action haction)

theorem simulate_globalMonitoredMappedAdversary_support_cache_le
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredTracedState)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalMonitoredMappedAdversaryImpl right)
        computation).run state)) :
    state.1.causal.cache ≤ result.2.1.causal.cache := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalMonitoredMappedAdversaryImpl right)
    (fun current : GlobalMonitoredTracedState =>
      state.1.causal.cache ≤ current.1.causal.cache)
    (globalMonitoredMappedAdversaryImpl_preserves_cache_extension right
      state.1.causal.cache) computation state le_rfl result hresult

theorem simulate_globalMonitoredMappedAdversary_support_trace_le
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredTracedState)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalMonitoredMappedAdversaryImpl right)
        computation).run state)) :
    ∀ action ∈ state.2, action ∈ result.2.2 := by
  exact OracleComp.simulateQ_run_preservesInv
    (globalMonitoredMappedAdversaryImpl right)
    (fun current : GlobalMonitoredTracedState =>
      ∀ action ∈ state.2, action ∈ current.2)
    (globalMonitoredMappedAdversaryImpl_preserves_trace_extension right
      state.2) computation state (by simp) result hresult

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem simulate_globalMonitoredMappedAdversary_support_covered_of_final
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalMonitoredTracedState)
    (covered : Set GlobalChainValueIndex)
    (finalCache : QueryCache HashSpec)
    (finalTrace : AttackerActionTrace)
    (hcovered : GlobalMonitoredCausalStateCovered covered state.1)
    (hforward : GlobalChainValueIndicesForwardClosed covered)
    (hdirect : ∀ request signature encoding chain,
      AttackerAction.sign request (some signature) ∈ finalTrace →
      Concrete.CacheView.decodedEncoding finalCache
          right.1.secretKey.parameter request.epoch
          (request.message, signature.randomness) = some encoding →
      (chain, request.epoch, encoding chain) ∈ covered)
    (result : α × GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((simulateQ (globalMonitoredMappedAdversaryImpl right)
        computation).run state))
    (hcacheLe : result.2.1.causal.cache ≤ finalCache)
    (htraceLe : ∀ action, action ∈ result.2.2 → action ∈ finalTrace) :
    GlobalMonitoredCausalStateCovered covered result.2.1 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact hcovered
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind] at hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      have hheadCacheLe : head.2.1.causal.cache ≤ finalCache :=
        (simulate_globalMonitoredMappedAdversary_support_cache_le right
          (next head.1) head.2 result htail).trans hcacheLe
      have hheadTraceLe : ∀ action, action ∈ head.2.2 →
          action ∈ finalTrace := by
        intro action haction
        apply htraceLe action
        exact simulate_globalMonitoredMappedAdversary_support_trace_le right
          (next head.1) head.2 result htail action haction
      have hheadCovered :=
        globalMonitoredMappedAdversaryImpl_support_covered_of_final right
          input state covered finalCache hcovered hforward head hheadCacheLe
            (fun request signature encoding chain haction hdecode =>
              hdirect request signature encoding chain
                (hheadTraceLe _ haction) hdecode)
            hhead
      exact ih head.1 head.2 hheadCovered result htail hcacheLe htraceLe

theorem globalRunObserved_eq_true_of_probe_mem_of_no_reveal
    (table : GlobalChainValueIndex → Digest)
    (state : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (index : GlobalChainValueIndex) (target : Digest)
    (hhidden : state.revealed index = none)
    (hprobe : RevealProbeOracleSimulation.ObservedAction.probe index target ∈
      trace)
    (hhit : table index = target)
    (hnoreveal : ∀ value,
      RevealProbeOracleSimulation.ObservedAction.reveal index value ∉ trace) :
    RevealProbeOracleSimulation.runObserved table state trace = true := by
  induction trace generalizing state with
  | nil => simp at hprobe
  | cons action trace ih =>
      cases action with
      | probe candidate candidateTarget =>
          rw [List.mem_cons] at hprobe
          rcases hprobe with heq | htail
          · cases heq
            rw [RevealProbeOracleSimulation.runObserved, hhidden]
            apply RevealProbeOracleSimulation.runObserved_eq_true_of_initial_tableHit
            unfold RevealProbeOracleSimulation.tableHits
            simp only [decide_eq_true_eq]
            refine ⟨index, ?_⟩
            simp [AdaptiveRevealMonitor.State.addPending, hhit]
          · simp only [RevealProbeOracleSimulation.runObserved]
            cases hrevealed : state.revealed candidate with
            | some value =>
                apply ih state hhidden htail
                intro revealValue hmem
                exact hnoreveal revealValue (by simp [hmem])
            | none =>
                apply ih (state.addPending candidate candidateTarget)
                · exact hhidden
                · exact htail
                · intro revealValue hmem
                  exact hnoreveal revealValue (by simp [hmem])
      | reveal candidate value =>
          have hne : candidate ≠ index := by
            intro heq
            subst candidate
            exact hnoreveal value (by simp)
          have htail :
              RevealProbeOracleSimulation.ObservedAction.probe index target ∈
                trace := by
            simpa using hprobe
          simp only [RevealProbeOracleSimulation.runObserved]
          cases hrevealed : state.revealed candidate with
          | some previous =>
              apply ih state hhidden htail
              intro revealValue hmem
              exact hnoreveal revealValue (by simp [hmem])
          | none =>
              by_cases hearly : table candidate ∈ state.pending candidate
              · simp [hearly]
              · rw [if_neg hearly]
                apply ih (state.install candidate (table candidate))
                · simpa [AdaptiveRevealMonitor.State.install,
                    Function.update_of_ne (Ne.symm hne)] using hhidden
                · exact htail
                · intro revealValue hmem
                  exact hnoreveal revealValue (by simp [hmem])

end XmssSecurity.Generic.CappedChain
