import XmssSecurity.Proof.Direct.FirstLaneStepBudget
import XmssSecurity.Proof.FirstLanePublicBudget

/-! The observable first-lane budget is enforced without inspecting the hidden table.
At a related source/ideal state, enforcement preserves the next action exactly, including
an action that first breaks the relation. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.CappedChain

open Seeded FirstLaneOracleSimulation

noncomputable def directEncodingActionCost (parameter : PublicParameter) :
    (OracleWorld + SigningSpec).Domain → Nat
  | .inl input => if CappedEncodingMonitor.IsEncodingHashQuery parameter input then 1 else 0
  | .inr _ => 0

noncomputable def firstLaneCounters (parameter : PublicParameter)
    (state : GlobalHighDirectTracedState) (history : ActionTrace GlobalChainValueIndex) :
    EncodingBudgetCounters :=
  ⟨state.attackerTrace.hashInputs.length, state.attackerTrace.encodingInputCount parameter,
    history.encodingActions.length⟩

theorem globalFirstLane_query_encodingInputCount_update
    (table : GlobalChainValueIndex → Digest) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × GlobalHighDirectTracedState) ×
      ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      ((globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state)).run)) :
    result.1.2.attackerTrace.encodingInputCount key.secretKey.parameter =
      state.attackerTrace.encodingInputCount key.secretKey.parameter +
        directEncodingActionCost key.secretKey.parameter input := by
  cases input with
  | inl input => exact globalFirstLane_world_encodingInputCount_update table key edgeHigh input state result hresult
  | inr request =>
      obtain ⟨base, _hbase, hresultEq⟩ := globalExactTracedLift_eager_support_decompose table key
        (.inr request) (globalFirstLaneSigningImpl key request) state result hresult
      rw [hresultEq, globalExactTracedNextState]
      change (state.attackerTrace ++ attackerActionFragment (.inr request) base.1.1).encodingInputCount
        key.secretKey.parameter = _
      rw [AttackerActionTrace.encodingInputCount_append, attackerActionFragment_encodingInputCount]
      rfl

theorem firstLaneCounters_query_update
    (table : GlobalChainValueIndex → Digest) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighDirectTracedState) (history : ActionTrace GlobalChainValueIndex)
    (result : ((OracleWorld + SigningSpec).Range input × GlobalHighDirectTracedState) ×
      ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      ((globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state)).run)) :
    ((firstLaneCounters key.secretKey.parameter state history).credit (directHashActionCost input)
      (directEncodingActionCost key.secretKey.parameter input)).addSamples result.2.encodingActions.length =
        firstLaneCounters key.secretKey.parameter result.1.2 (history ++ result.2) := by
  unfold firstLaneCounters EncodingBudgetCounters.credit EncodingBudgetCounters.addSamples
  rw [globalFirstLane_query_hashInputs_update table key edgeHigh input state result hresult,
    globalFirstLane_query_encodingInputCount_update table key edgeHigh input state result hresult,
    ActionTrace.encodingActions_append, List.length_append]

noncomputable def limitedFirstLaneAction (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighDirectTracedState) (counters : EncodingBudgetCounters) :
    OracleComp GlobalFirstLaneWorld
      (Option ((OracleWorld + SigningSpec).Range input × GlobalHighDirectTracedState) × EncodingBudgetCounters) :=
  limitEncodingAction limit (directHashActionCost input) (directEncodingActionCost key.secretKey.parameter input)
    counters ((globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state)

/-- The complete public prefix halts on an aborted action, keeping its counters and trace. -/
noncomputable def limitedFirstLanePrefix {α : Type} (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalHighDirectTracedState) (counters : EncodingBudgetCounters) :
    OracleComp GlobalFirstLaneWorld (Option (α × GlobalHighDirectTracedState) × EncodingBudgetCounters) :=
  OracleComp.recOn computation (fun value state counters => pure (some (value, state), counters))
    (fun input _ next state counters => do
      let result ← limitedFirstLaneAction limit key edgeHigh input state counters
      match result.1 with
      | none => pure (none, result.2)
      | some handled => next handled.1 handled.2 result.2) state counters

theorem limitedFirstLanePrefix_pure {α : Type} (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (value : α) (state : GlobalHighDirectTracedState)
    (counters : EncodingBudgetCounters) :
    limitedFirstLanePrefix limit key edgeHigh (pure value) state counters = pure (some (value, state), counters) := rfl

theorem limitedFirstLanePrefix_query_bind {α : Type} (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalHighDirectTracedState) (counters : EncodingBudgetCounters) :
    limitedFirstLanePrefix limit key edgeHigh (liftM ((OracleWorld + SigningSpec).query input) >>= next)
      state counters = (do
        let result ← limitedFirstLaneAction limit key edgeHigh input state counters
        match result.1 with
        | none => pure (none, result.2)
        | some handled => limitedFirstLanePrefix limit key edgeHigh (next handled.1) handled.2 result.2) := rfl

theorem limitedFirstLanePrefix_trace_budget {α : Type}
    (table : GlobalChainValueIndex → Digest) (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalHighDirectTracedState) (counters : EncodingBudgetCounters)
    (hbudget : counters.charge ≤ limit)
    (result : (Option (α × GlobalHighDirectTracedState) × EncodingBudgetCounters) ×
      ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl table)
      (limitedFirstLanePrefix limit key edgeHigh computation state counters)).run) :
    result.1.2.charge ≤ limit ∧
      result.1.2.samples = counters.samples + result.2.encodingActions.length := by
  induction computation using OracleComp.inductionOn generalizing state counters result with
  | pure value =>
      simp only [limitedFirstLanePrefix_pure, simulateQ_pure, WriterT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hbudget, by simp [ActionTrace.encodingActions]⟩
  | query_bind input next ih =>
      rw [limitedFirstLanePrefix_query_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rw [support_map] at htail
      obtain ⟨tail, htail, rfl⟩ := htail
      have hheadBudget := limitEncodingAction_trace_budget table limit (directHashActionCost input)
        (directEncodingActionCost key.secretKey.parameter input) counters
        ((globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state) hbudget head hhead
      change tail.1.2.charge ≤ limit ∧
        tail.1.2.samples = counters.samples + (head.2 ++ tail.2).encodingActions.length
      cases hhandled : head.1.1 with
      | none =>
          simp only [hhandled, simulateQ_pure, WriterT.run_pure, support_pure,
            Set.mem_singleton_iff] at htail
          subst tail
          simpa using hheadBudget
      | some handled =>
          simp only [hhandled] at htail
          have htailBudget := ih handled.1 handled.2 head.1.2 hheadBudget.1 tail htail
          refine ⟨htailBudget.1, ?_⟩
          rw [htailBudget.2, hheadBudget.2, ActionTrace.encodingActions_append, List.length_append, Nat.add_assoc]

theorem limitedFirstLanePrefix_trace_direct {α : Type}
    (table : GlobalChainValueIndex → Digest) (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalHighDirectTracedState) (counters : EncodingBudgetCounters)
    (result : (Option (α × GlobalHighDirectTracedState) × EncodingBudgetCounters) ×
      ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl table)
      (limitedFirstLanePrefix limit key edgeHigh computation state counters)).run) :
    counters.direct + hazardCount result.2 ≤ result.1.2.direct := by
  induction computation using OracleComp.inductionOn generalizing state counters result with
  | pure value =>
      simp only [limitedFirstLanePrefix_pure, simulateQ_pure, WriterT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp [hazardCount]
  | query_bind input next ih =>
      rw [limitedFirstLanePrefix_query_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rw [support_map] at htail
      obtain ⟨tail, htail, rfl⟩ := htail
      have hheadBound := limitEncodingAction_trace_direct table limit (directHashActionCost input)
        (directEncodingActionCost key.secretKey.parameter input) counters
        ((globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state)
        (globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound key edgeHigh input state) head hhead
      change counters.direct + hazardCount (head.2 ++ tail.2) ≤ tail.1.2.direct
      cases hhandled : head.1.1 with
      | none =>
          simp only [hhandled, simulateQ_pure, WriterT.run_pure, support_pure,
            Set.mem_singleton_iff] at htail
          subst tail
          simpa using hheadBound
      | some handled =>
          simp only [hhandled] at htail
          have htailBound := ih handled.1 handled.2 head.1.2 tail htail
          rw [hazardCount_append]
          omega

theorem limitedFirstLaneAction_eq_of_related {α : Type}
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView × (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (limit : Nat) (leftState : CountedSourceState) (rightState : GlobalHighDirectTracedState)
    (history : ActionTrace GlobalChainValueIndex)
    (hstate : SourceFirstLaneExactGoodStateRelation left right.1 leftState.toSource rightState history)
    (hcacheCount : cachedEncodingInputCount rightState.causalState.cache right.1.1.secretKey.parameter =
      (history.encodingActions.length : ℝ≥0∞))
    (hencoding : CountedSourceEncodingBudget left.secretKey.parameter leftState)
    (hcount : hazardCount history ≤ leftState.counts.direct)
    (hsourceTrace : leftState.counts.direct = leftState.attackerTrace.hashInputs.length)
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit (liftM ((OracleWorld + SigningSpec).query input) >>= next) leftState) :
    (simulateQ (eagerTraceImpl right.1.2) (limitedFirstLaneAction limit right.1.1 right.2 input rightState
      (firstLaneCounters right.1.1.secretKey.parameter rightState history))).run =
        (fun result => ((some result.1,
          firstLaneCounters right.1.1.secretKey.parameter result.1.2 (history ++ result.2)), result.2)) <$>
            (simulateQ (eagerTraceImpl right.1.2)
              ((globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2 input).run rightState)).run := by
  have hstep := firstLane_step_observableDirectCharge_le left right hrel hleftSupport hrightSupport input next
    limit leftState rightState history hstate hcacheCount hencoding hcount hsourceTrace hbudget
  unfold limitedFirstLaneAction
  rw [simulate_limitEncodingAction_eq right.1.2 limit _ _ _ _ (fun result hresult => by
    rw [firstLaneCounters_query_update right.1.2 right.1.1 right.2 input rightState history result hresult]
    exact hstep result hresult)]
  simp only [map_eq_bind_pure_comp]
  refine bind_congr_of_forall_mem_support _ fun result hresult => ?_
  simp only [Function.comp_apply,
    firstLaneCounters_query_update right.1.2 right.1.1 right.2 input rightState history result hresult]

/-- info: 'XmssSecurity.CappedChain.limitedFirstLaneAction_eq_of_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitedFirstLaneAction_eq_of_related

/-- info: 'XmssSecurity.CappedChain.limitedFirstLanePrefix_trace_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitedFirstLanePrefix_trace_budget

/-- info: 'XmssSecurity.CappedChain.limitedFirstLanePrefix_trace_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitedFirstLanePrefix_trace_direct

end XmssSecurity.CappedChain
