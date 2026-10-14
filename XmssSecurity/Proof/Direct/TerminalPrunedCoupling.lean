import XmssSecurity.Proof.Direct.TerminalPrunedPrefix

/-! Couple the source to the terminal-pruned public prefix. Besides the usual
agreement-or-hit cases, an early cut certifies that the source cannot have an accepted encoding. -/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.CappedChain

open Seeded FirstLaneOracleSimulation

def TerminalFirstLaneOutcomeRelation {α : Type}
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest))
    (history : ActionTrace GlobalChainValueIndex) (source : α × CountedSourceState)
    (target : (Option (α × GlobalHighDirectTracedState) × EncodingBudgetCounters) ×
      ActionTrace GlobalChainValueIndex) : Prop :=
  LimitedFirstLaneOutcomeRelation left right history source target ∨
    (target.1.1 = none ∧ ¬HasAcceptedEncoding left.secretKey.parameter source.2.counts.cache)

theorem relTriple_countedSource_terminalPrefix_of_related {α : Type}
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (limit : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftState : CountedSourceState) (rightState : GlobalHighDirectTracedState)
    (history : ActionTrace GlobalChainValueIndex)
    (hstate : SourceFirstLaneExactGoodStateRelation left right.1 leftState.toSource rightState history)
    (hcacheCount : cachedEncodingInputCount rightState.causalState.cache right.1.1.secretKey.parameter =
      (history.encodingActions.length : ℝ≥0∞))
    (hencoding : CountedSourceEncodingBudget left.secretKey.parameter leftState)
    (hcount : hazardCount history ≤ leftState.counts.direct)
    (hsourceTrace : leftState.counts.direct = leftState.attackerTrace.hashInputs.length)
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit computation leftState) :
    RelTriple
      ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
        computation).run leftState)
      ((simulateQ (eagerTraceImpl right.1.2)
        (terminalPrunedFirstLanePrefix limit right.1.1 right.2 computation rightState
          (firstLaneCounters right.1.1.secretKey.parameter rightState history))).run)
      (TerminalFirstLaneOutcomeRelation left right.1 history) := by
  induction computation using OracleComp.inductionOn generalizing leftState rightState history with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, terminalPrunedFirstLanePrefix_pure, WriterT.run_pure]
      apply relTriple_pure_pure
      apply Or.inl
      apply Or.inl
      exact ⟨rightState, rfl, by simpa using hstate, by simp, by simpa using hcount⟩
  | query_bind input next ih =>
      rw [terminalPrunedFirstLanePrefix_query_bind]
      by_cases hcut : TerminalPrefixCut limit right.1.1 input rightState
          (firstLaneCounters right.1.1.secretKey.parameter rightState history)
      · rw [if_pos hcut, simulateQ_pure, WriterT.run_pure]
        apply relTriple_post_mono (relTriple_with_support
          (relTriple_prod (fun _ _ => True.intro) (fun _ _ => True.intro)))
        intro source target hresult
        obtain ⟨_, hsource, htarget⟩ := hresult
        simp only [support_pure, Set.mem_singleton_iff] at htarget
        subst target
        exact Or.inr ⟨rfl, terminalPrefixCut_source_noAccepted left right hrel hleftSupport
          hrightSupport limit input next leftState rightState history hstate hcacheCount hencoding
            hsourceTrace hbudget hcut source hsource⟩
      · rw [if_neg hcut, Direct.run_simulateQ_query_bind, simulateQ_bind,
          WriterT.run_bind', limitedFirstLaneAction_eq_of_related left right hrel hleftSupport
            hrightSupport input next limit leftState rightState history hstate hcacheCount hencoding
              hcount hsourceTrace hbudget, bind_map_left]
        change RelTriple
          ((countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey) input).run leftState >>=
            fun head => (simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
              (next head.1)).run head.2)
          ((simulateQ (eagerTraceImpl right.1.2)
            ((globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2 input).run rightState)).run >>=
            fun head => Prod.map id (fun tail => head.2 ++ tail) <$>
              (simulateQ (eagerTraceImpl right.1.2)
                (terminalPrunedFirstLanePrefix limit right.1.1 right.2 (next head.1.1) head.1.2
                  (firstLaneCounters right.1.1.secretKey.parameter head.1.2 (history ++ head.2)))).run)
          (TerminalFirstLaneOutcomeRelation left right.1 history)
        apply relTriple_bind (relTriple_with_support (relTriple_countedSource_firstLane_action left right
          hrel hleftSupport hrightSupport input next limit leftState rightState history hstate hcount hbudget))
        intro headLeft headRight hhead
        obtain ⟨⟨_hcharge, hnextBudget, hnextCount, hnext⟩, hleft, hright⟩ := hhead
        rcases hnext with ⟨hvalue, hnextState⟩ | hhit
        · have hnextCache := globalFirstLaneExactTraced_query_encodingCountGrowth right.1.2 right.1.1
            right.2 input rightState headRight hright
          change cachedEncodingInputCount headRight.1.2.causalState.cache right.1.1.secretKey.parameter = _
            at hnextCache
          rw [hcacheCount] at hnextCache
          have hnextCache' : cachedEncodingInputCount headRight.1.2.causalState.cache right.1.1.secretKey.parameter =
              ((history ++ headRight.2).encodingActions.length : ℝ≥0∞) := by
            simpa only [ActionTrace.encodingActions_append, List.length_append, Nat.cast_add] using hnextCache
          have hnextEncoding := countedSourceImpl_encodingBudget
            (Concrete.materializePrecomputation left.cache left.secretKey) input leftState hencoding headLeft hleft
          have hnextTrace : headLeft.2.counts.direct = headLeft.2.attackerTrace.hashInputs.length := by
            rw [countedSourceImpl_direct_eq _ input leftState headLeft hleft,
              countedSourceImpl_hashInputs_update _ input leftState headLeft hleft, hsourceTrace]
          rw [hvalue] at hnextBudget
          have hrec := ih headRight.1.1 headLeft.2 headRight.1.2 (history ++ headRight.2) hnextState
            hnextCache' hnextEncoding hnextCount hnextTrace hnextBudget
          have hmapped : RelTriple
              (id <$> ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
                (next headRight.1.1)).run headLeft.2))
              (Prod.map id (fun tail => headRight.2 ++ tail) <$>
                (simulateQ (eagerTraceImpl right.1.2)
                  (terminalPrunedFirstLanePrefix limit right.1.1 right.2 (next headRight.1.1) headRight.1.2
                    (firstLaneCounters right.1.1.secretKey.parameter headRight.1.2 (history ++ headRight.2)))).run)
              (TerminalFirstLaneOutcomeRelation left right.1 history) := by
            apply relTriple_map
            apply relTriple_post_mono hrec
            intro source target hresult
            simpa only [TerminalFirstLaneOutcomeRelation, LimitedFirstLaneOutcomeRelation,
              Prod.map, id_eq, List.append_assoc] using hresult
          rw [hvalue]
          simpa only [id_map] using hmapped
        · apply relTriple_post_mono (relTriple_firstLaneHit_append right.1.2 history headRight.2 hhit
            ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
              (next headLeft.1)).run headLeft.2)
            ((simulateQ (eagerTraceImpl right.1.2)
              (terminalPrunedFirstLanePrefix limit right.1.1 right.2 (next headRight.1.1) headRight.1.2
                (firstLaneCounters right.1.1.secretKey.parameter headRight.1.2 (history ++ headRight.2)))).run))
          intro _ _ hhit
          exact Or.inl (Or.inr hhit)

theorem relTriple_countedSource_terminalPrefix {α : Type}
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (limit : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit computation (CountedSourceState.initial left.cache)) :
    RelTriple
      ((simulateQ (countedSourceImpl (Concrete.materializePrecomputation left.cache left.secretKey))
        computation).run (CountedSourceState.initial left.cache))
      ((simulateQ (eagerTraceImpl right.1.2)
        (terminalPrunedFirstLanePrefix limit right.1.1 right.2 computation
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)) ⟨0, 0, 0⟩)).run)
      (TerminalFirstLaneOutcomeRelation left right.1 []) := by
  let sourceInitial := CountedSourceState.initial left.cache
  let targetInitial := GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState right.1.1)
  have hstate : SourceFirstLaneExactGoodStateRelation left right.1 sourceInitial.toSource targetInitial [] := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [sourceInitial, targetInitial, CountedSourceState.initial,
        CountedSourceState.toSource, globalStateOfFirstLane, sourceExactSigningProjection,
        ActionTrace.chainActions] using
        globalSigningMonitoredTracedStateRelation_initial left right hrel hleftSupport hrightSupport
    · simp [sourceInitial, CountedSourceState.initial, CountedSourceState.toSource,
        ActionTrace.encodingActions]
    · simp [targetInitial, CappedEncodingMonitor.validObservedSignLeafIndices,
        ActionTrace.encodingActions, CappedEncodingMonitor.validActions, EncodingMonitor.observedSignLeafIndices]
  have hcacheCount : cachedEncodingInputCount targetInitial.causalState.cache right.1.1.secretKey.parameter = 0 :=
    globalFilteredCausalKeygenState_encodingCount_zero right.1.1 hrightSupport
  have hencoding : CountedSourceEncodingBudget left.secretKey.parameter sourceInitial := by
    change cachedEncodingInputCount left.cache left.secretKey.parameter ≤ _
    rw [cachedEncodingInputCount_eq_zero_of_no_encodingInputs left.cache left.secretKey.parameter
      (Concrete.keygen_cache_none_encodingInput left.keyResult
        (trajectoryProgrammedGlobalChainKeygen_support_keyResult left hleftSupport))]
    exact zero_le
  exact relTriple_countedSource_terminalPrefix_of_related left right hrel hleftSupport hrightSupport
    limit computation sourceInitial targetInitial [] hstate
    (by simpa [ActionTrace.encodingActions] using hcacheCount) hencoding
    (by simp [hazardCount]) rfl hbudget

/-- info: 'XmssSecurity.CappedChain.relTriple_countedSource_terminalPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relTriple_countedSource_terminalPrefix

end XmssSecurity.CappedChain
