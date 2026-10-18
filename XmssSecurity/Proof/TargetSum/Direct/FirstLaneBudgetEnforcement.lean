import XmssSecurity.Proof.TargetSum.Direct.FirstLaneStepBudget
import XmssSecurity.Proof.TargetSum.FirstLanePublicBudget
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The observable first-lane budget is enforced without inspecting the hidden table.
At a related source/ideal state, enforcement preserves the next action exactly, including
an action that first breaks the relation. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.CappedChain

open Seeded FirstLaneOracleSimulation

noncomputable def directEncodingActionCost (parameter : PublicParameter) :
    (OracleWorld + SigningSpec).Domain → Nat
  | .inl input => if CappedEncodingMonitor.IsEncodingHashQuery parameter input then 1 else 0
  | .inr _ => 0

noncomputable def firstLaneCounters (parameter : PublicParameter)
    (state : CappedChain.GlobalDirectTracedState) (history : FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex) :
    EncodingBudgetCounters :=
  ⟨state.attackerTrace.hashInputs.length, state.attackerTrace.encodingInputCount parameter,
    history.encodingActions.length⟩

theorem globalFirstLane_query_encodingInputCount_update
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CappedChain.GlobalDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedChain.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key input).run state)).run)) :
    result.1.2.attackerTrace.encodingInputCount key.secretKey.parameter =
      state.attackerTrace.encodingInputCount key.secretKey.parameter +
        directEncodingActionCost key.secretKey.parameter input := by
  cases input with
  | inl input => exact globalFirstLane_world_encodingInputCount_update table key input state result hresult
  | inr request =>
      obtain ⟨base, _hbase, hresultEq⟩ := CappedChain.globalExactTracedLift_eager_support_decompose table key
        (.inr request) (CappedChain.globalFirstLaneSigningImpl key request) state result hresult
      rw [hresultEq, CappedChain.globalExactTracedNextState]
      change (state.attackerTrace ++ CappedChain.attackerActionFragment (.inr request) base.1.1).encodingInputCount
        key.secretKey.parameter = _
      rw [CappedChain.AttackerActionTrace.encodingInputCount_append, attackerActionFragment_encodingInputCount]
      rfl

theorem firstLaneCounters_query_update
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CappedChain.GlobalDirectTracedState) (history : FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (result : ((OracleWorld + SigningSpec).Range input × CappedChain.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key input).run state)).run)) :
    ((firstLaneCounters key.secretKey.parameter state history).credit (CappedChain.directHashActionCost input)
      (directEncodingActionCost key.secretKey.parameter input)).addSamples result.2.encodingActions.length =
        firstLaneCounters key.secretKey.parameter result.1.2 (history ++ result.2) := by
  unfold firstLaneCounters EncodingBudgetCounters.credit EncodingBudgetCounters.addSamples
  rw [globalFirstLane_query_hashInputs_update table key input state result hresult,
    globalFirstLane_query_encodingInputCount_update table key input state result hresult,
    FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append]

noncomputable def limitedFirstLaneAction (limit : Nat) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CappedChain.GlobalDirectTracedState) (counters : EncodingBudgetCounters) :
    OracleComp CappedChain.GlobalFirstLaneWorld
      (Option ((OracleWorld + SigningSpec).Range input × CappedChain.GlobalDirectTracedState) × EncodingBudgetCounters) :=
  limitEncodingAction limit (CappedChain.directHashActionCost input) (directEncodingActionCost key.secretKey.parameter input)
    counters ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key input).run state)

/-- The complete public prefix halts on an aborted action, keeping its counters and trace. -/
noncomputable def limitedFirstLanePrefix {α : Type} (limit : Nat) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CappedChain.GlobalDirectTracedState) (counters : EncodingBudgetCounters) :
    OracleComp CappedChain.GlobalFirstLaneWorld (Option (α × CappedChain.GlobalDirectTracedState) × EncodingBudgetCounters) :=
  OracleComp.recOn computation (fun value state counters => pure (some (value, state), counters))
    (fun input _ next state counters => do
      let result ← limitedFirstLaneAction limit key input state counters
      match result.1 with
      | none => pure (none, result.2)
      | some handled => next handled.1 handled.2 result.2) state counters

theorem limitedFirstLanePrefix_pure {α : Type} (limit : Nat) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (value : α) (state : CappedChain.GlobalDirectTracedState)
    (counters : EncodingBudgetCounters) :
    limitedFirstLanePrefix limit key (pure value) state counters = pure (some (value, state), counters) := rfl

theorem limitedFirstLanePrefix_query_bind {α : Type} (limit : Nat) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (state : CappedChain.GlobalDirectTracedState) (counters : EncodingBudgetCounters) :
    limitedFirstLanePrefix limit key (liftM ((OracleWorld + SigningSpec).query input) >>= next)
      state counters = (do
        let result ← limitedFirstLaneAction limit key input state counters
        match result.1 with
        | none => pure (none, result.2)
        | some handled => limitedFirstLanePrefix limit key (next handled.1) handled.2 result.2) := rfl

theorem limitedFirstLanePrefix_trace_budget {α : Type}
    (table : CappedChain.GlobalChainValueIndex → Digest) (limit : Nat) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CappedChain.GlobalDirectTracedState) (counters : EncodingBudgetCounters)
    (hbudget : counters.charge ≤ limit)
    (result : (Option (α × CappedChain.GlobalDirectTracedState) × EncodingBudgetCounters) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (limitedFirstLanePrefix limit key computation state counters)).run) :
    result.1.2.charge ≤ limit ∧
      result.1.2.samples = counters.samples + result.2.encodingActions.length := by
  induction computation using OracleComp.inductionOn generalizing state counters result with
  | pure value =>
      simp only [limitedFirstLanePrefix_pure, simulateQ_pure, WriterT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hbudget, by simp [FirstLaneOracleSimulation.ActionTrace.encodingActions]⟩
  | query_bind input next ih =>
      rw [limitedFirstLanePrefix_query_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rw [support_map] at htail
      obtain ⟨tail, htail, rfl⟩ := htail
      have hheadBudget := limitEncodingAction_trace_budget table limit (CappedChain.directHashActionCost input)
        (directEncodingActionCost key.secretKey.parameter input) counters
        ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key input).run state) hbudget head hhead
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
          rw [htailBudget.2, hheadBudget.2, FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append, Nat.add_assoc]

theorem limitedFirstLanePrefix_trace_direct {α : Type}
    (table : CappedChain.GlobalChainValueIndex → Digest) (limit : Nat) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CappedChain.GlobalDirectTracedState) (counters : EncodingBudgetCounters)
    (result : (Option (α × CappedChain.GlobalDirectTracedState) × EncodingBudgetCounters) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (limitedFirstLanePrefix limit key computation state counters)).run) :
    counters.direct + FirstLaneOracleSimulation.hazardCount result.2 ≤ result.1.2.direct := by
  induction computation using OracleComp.inductionOn generalizing state counters result with
  | pure value =>
      simp only [limitedFirstLanePrefix_pure, simulateQ_pure, WriterT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp [FirstLaneOracleSimulation.hazardCount]
  | query_bind input next ih =>
      rw [limitedFirstLanePrefix_query_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rw [support_map] at htail
      obtain ⟨tail, htail, rfl⟩ := htail
      have hheadBound := limitEncodingAction_trace_direct table limit (CappedChain.directHashActionCost input)
        (directEncodingActionCost key.secretKey.parameter input) counters
        ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key input).run state)
        (CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound key input state) head hhead
      change counters.direct + FirstLaneOracleSimulation.hazardCount (head.2 ++ tail.2) ≤ tail.1.2.direct
      cases hhandled : head.1.1 with
      | none =>
          simp only [hhandled, simulateQ_pure, WriterT.run_pure, support_pure,
            Set.mem_singleton_iff] at htail
          subst tail
          simpa using hheadBound
      | some handled =>
          simp only [hhandled] at htail
          have htailBound := ih handled.1 handled.2 head.1.2 tail htail
          rw [FirstLaneOracleSimulation.hazardCount_append]
          omega

theorem limitedFirstLaneAction_eq_of_related {α : Type}
    (left : CappedChain.ProgrammedGlobalChainKeygenView)
    (right : CappedChain.ProgrammedGlobalChainKeygenView × (CappedChain.GlobalChainValueIndex → Digest))
    (hrel : CappedChain.ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (limit : Nat) (leftState : CountedSourceState) (rightState : CappedChain.GlobalDirectTracedState)
    (history : FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hstate : CappedChain.SourceFirstLaneExactGoodStateRelation left right leftState.toSource rightState history)
    (hcacheCount : cachedEncodingInputCount rightState.causalState.cache right.1.secretKey.parameter =
      (history.encodingActions.length : ℝ≥0∞))
    (hencoding : CountedSourceEncodingBudget left.secretKey.parameter leftState)
    (hcount : FirstLaneOracleSimulation.hazardCount history ≤ leftState.counts.direct)
    (hsourceTrace : leftState.counts.direct = leftState.attackerTrace.hashInputs.length)
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit (liftM ((OracleWorld + SigningSpec).query input) >>= next) leftState) :
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2) (limitedFirstLaneAction limit right.1 input rightState
      (firstLaneCounters right.1.secretKey.parameter rightState history))).run =
        (fun result => ((some result.1,
          firstLaneCounters right.1.secretKey.parameter result.1.2 (history ++ result.2)), result.2)) <$>
            (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
              ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1 input).run rightState)).run := by
  have hstep := firstLane_step_observableDirectCharge_le left right hrel hleftSupport hrightSupport input next
    limit leftState rightState history hstate hcacheCount hencoding hcount hsourceTrace hbudget
  unfold limitedFirstLaneAction
  rw [simulate_limitEncodingAction_eq right.2 limit _ _ _ _ (fun result hresult => by
    rw [firstLaneCounters_query_update right.2 right.1 input rightState history result hresult]
    exact hstep result hresult)]
  simp only [map_eq_bind_pure_comp]
  refine bind_congr_of_forall_mem_support _ fun result hresult => ?_
  simp only [Function.comp_apply,
    firstLaneCounters_query_update right.2 right.1 input rightState history result hresult]

/-- info: 'XmssSecurity.TargetSum.CappedChain.limitedFirstLaneAction_eq_of_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitedFirstLaneAction_eq_of_related

/-- info: 'XmssSecurity.TargetSum.CappedChain.limitedFirstLanePrefix_trace_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitedFirstLanePrefix_trace_budget

/-- info: 'XmssSecurity.TargetSum.CappedChain.limitedFirstLanePrefix_trace_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitedFirstLanePrefix_trace_direct

end XmssSecurity.TargetSum.CappedChain
