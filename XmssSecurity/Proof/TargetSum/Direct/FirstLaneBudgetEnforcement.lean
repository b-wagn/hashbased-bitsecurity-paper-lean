import XmssSecurity.Proof.TargetSum.Direct.FirstLaneStepBudget
import XmssSecurity.Proof.TargetSum.FirstLanePublicBudget
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The observable first-lane budget is enforced without inspecting the hidden table.
At a related source/ideal state, enforcement preserves the next action exactly, including
an action that first breaks the relation. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.CappedChain

open Seeded FirstLaneOracleSimulation

noncomputable def directEncodingActionCost (parameter : PublicParameter) :
    (OracleWorld + Generic.SigningSpec).Domain → Nat
  | .inl input => if Generic.CappedEncodingMonitor.IsEncodingHashQuery parameter input then 1 else 0
  | .inr _ => 0

noncomputable def firstLaneCounters (parameter : PublicParameter)
    (state : Generic.CappedChain.GlobalHighDirectTracedState) (history : Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex) :
    EncodingBudgetCounters :=
  ⟨state.attackerTrace.hashInputs.length, state.attackerTrace.encodingInputCount parameter,
    history.encodingActions.length⟩

theorem globalFirstLane_query_encodingInputCount_update
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (input : (OracleWorld + Generic.SigningSpec).Domain)
    (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : ((OracleWorld + Generic.SigningSpec).Range input × Generic.CappedChain.GlobalHighDirectTracedState) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state)).run)) :
    result.1.2.attackerTrace.encodingInputCount key.secretKey.parameter =
      state.attackerTrace.encodingInputCount key.secretKey.parameter +
        directEncodingActionCost key.secretKey.parameter input := by
  cases input with
  | inl input => exact globalFirstLane_world_encodingInputCount_update table key edgeHigh input state result hresult
  | inr request =>
      obtain ⟨base, _hbase, hresultEq⟩ := Generic.CappedChain.globalExactTracedLift_eager_support_decompose table key
        (.inr request) (Generic.CappedChain.globalFirstLaneSigningImpl key request) state result hresult
      rw [hresultEq, Generic.CappedChain.globalExactTracedNextState]
      change (state.attackerTrace ++ Generic.CappedChain.attackerActionFragment (.inr request) base.1.1).encodingInputCount
        key.secretKey.parameter = _
      rw [Generic.CappedChain.AttackerActionTrace.encodingInputCount_append, attackerActionFragment_encodingInputCount]
      rfl

theorem firstLaneCounters_query_update
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (input : (OracleWorld + Generic.SigningSpec).Domain)
    (state : Generic.CappedChain.GlobalHighDirectTracedState) (history : Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (result : ((OracleWorld + Generic.SigningSpec).Range input × Generic.CappedChain.GlobalHighDirectTracedState) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state)).run)) :
    ((firstLaneCounters key.secretKey.parameter state history).credit (Generic.CappedChain.directHashActionCost input)
      (directEncodingActionCost key.secretKey.parameter input)).addSamples result.2.encodingActions.length =
        firstLaneCounters key.secretKey.parameter result.1.2 (history ++ result.2) := by
  unfold firstLaneCounters EncodingBudgetCounters.credit EncodingBudgetCounters.addSamples
  rw [globalFirstLane_query_hashInputs_update table key edgeHigh input state result hresult,
    globalFirstLane_query_encodingInputCount_update table key edgeHigh input state result hresult,
    Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append]

noncomputable def limitedFirstLaneAction (limit : Nat) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (input : (OracleWorld + Generic.SigningSpec).Domain)
    (state : Generic.CappedChain.GlobalHighDirectTracedState) (counters : EncodingBudgetCounters) :
    OracleComp Generic.CappedChain.GlobalFirstLaneWorld
      (Option ((OracleWorld + Generic.SigningSpec).Range input × Generic.CappedChain.GlobalHighDirectTracedState) × EncodingBudgetCounters) :=
  limitEncodingAction limit (Generic.CappedChain.directHashActionCost input) (directEncodingActionCost key.secretKey.parameter input)
    counters ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state)

/-- The complete public prefix halts on an aborted action, keeping its counters and trace. -/
noncomputable def limitedFirstLanePrefix {α : Type} (limit : Nat) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (state : Generic.CappedChain.GlobalHighDirectTracedState) (counters : EncodingBudgetCounters) :
    OracleComp Generic.CappedChain.GlobalFirstLaneWorld (Option (α × Generic.CappedChain.GlobalHighDirectTracedState) × EncodingBudgetCounters) :=
  OracleComp.recOn computation (fun value state counters => pure (some (value, state), counters))
    (fun input _ next state counters => do
      let result ← limitedFirstLaneAction limit key edgeHigh input state counters
      match result.1 with
      | none => pure (none, result.2)
      | some handled => next handled.1 handled.2 result.2) state counters

theorem limitedFirstLanePrefix_pure {α : Type} (limit : Nat) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (value : α) (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (counters : EncodingBudgetCounters) :
    limitedFirstLanePrefix limit key edgeHigh (pure value) state counters = pure (some (value, state), counters) := rfl

theorem limitedFirstLanePrefix_query_bind {α : Type} (limit : Nat) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (input : (OracleWorld + Generic.SigningSpec).Domain)
    (next : (OracleWorld + Generic.SigningSpec).Range input → OracleComp (OracleWorld + Generic.SigningSpec) α)
    (state : Generic.CappedChain.GlobalHighDirectTracedState) (counters : EncodingBudgetCounters) :
    limitedFirstLanePrefix limit key edgeHigh (liftM ((OracleWorld + Generic.SigningSpec).query input) >>= next)
      state counters = (do
        let result ← limitedFirstLaneAction limit key edgeHigh input state counters
        match result.1 with
        | none => pure (none, result.2)
        | some handled => limitedFirstLanePrefix limit key edgeHigh (next handled.1) handled.2 result.2) := rfl

theorem limitedFirstLanePrefix_trace_budget {α : Type}
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (limit : Nat) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (state : Generic.CappedChain.GlobalHighDirectTracedState) (counters : EncodingBudgetCounters)
    (hbudget : counters.charge ≤ limit)
    (result : (Option (α × Generic.CappedChain.GlobalHighDirectTracedState) × EncodingBudgetCounters) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      (limitedFirstLanePrefix limit key edgeHigh computation state counters)).run) :
    result.1.2.charge ≤ limit ∧
      result.1.2.samples = counters.samples + result.2.encodingActions.length := by
  induction computation using OracleComp.inductionOn generalizing state counters result with
  | pure value =>
      simp only [limitedFirstLanePrefix_pure, simulateQ_pure, WriterT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hbudget, by simp [Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions]⟩
  | query_bind input next ih =>
      rw [limitedFirstLanePrefix_query_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rw [support_map] at htail
      obtain ⟨tail, htail, rfl⟩ := htail
      have hheadBudget := limitEncodingAction_trace_budget table limit (Generic.CappedChain.directHashActionCost input)
        (directEncodingActionCost key.secretKey.parameter input) counters
        ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state) hbudget head hhead
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
          rw [htailBudget.2, hheadBudget.2, Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append, Nat.add_assoc]

theorem limitedFirstLanePrefix_trace_direct {α : Type}
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (limit : Nat) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (state : Generic.CappedChain.GlobalHighDirectTracedState) (counters : EncodingBudgetCounters)
    (result : (Option (α × Generic.CappedChain.GlobalHighDirectTracedState) × EncodingBudgetCounters) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      (limitedFirstLanePrefix limit key edgeHigh computation state counters)).run) :
    counters.direct + Generic.FirstLaneOracleSimulation.hazardCount result.2 ≤ result.1.2.direct := by
  induction computation using OracleComp.inductionOn generalizing state counters result with
  | pure value =>
      simp only [limitedFirstLanePrefix_pure, simulateQ_pure, WriterT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp [Generic.FirstLaneOracleSimulation.hazardCount]
  | query_bind input next ih =>
      rw [limitedFirstLanePrefix_query_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rw [support_map] at htail
      obtain ⟨tail, htail, rfl⟩ := htail
      have hheadBound := limitEncodingAction_trace_direct table limit (Generic.CappedChain.directHashActionCost input)
        (directEncodingActionCost key.secretKey.parameter input) counters
        ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state)
        (Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound key edgeHigh input state) head hhead
      change counters.direct + Generic.FirstLaneOracleSimulation.hazardCount (head.2 ++ tail.2) ≤ tail.1.2.direct
      cases hhandled : head.1.1 with
      | none =>
          simp only [hhandled, simulateQ_pure, WriterT.run_pure, support_pure,
            Set.mem_singleton_iff] at htail
          subst tail
          simpa using hheadBound
      | some handled =>
          simp only [hhandled] at htail
          have htailBound := ih handled.1 handled.2 head.1.2 tail htail
          rw [Generic.FirstLaneOracleSimulation.hazardCount_append]
          omega

theorem limitedFirstLaneAction_eq_of_related {α : Type}
    (left : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (right : (Generic.CappedChain.ProgrammedGlobalChainKeygenView × (Generic.CappedChain.GlobalChainValueIndex → Digest)) ×
      (Generic.CappedChain.GlobalChainEdgeIndex → Digest))
    (hrel : Generic.CappedChain.ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (input : (OracleWorld + Generic.SigningSpec).Domain)
    (next : (OracleWorld + Generic.SigningSpec).Range input → OracleComp (OracleWorld + Generic.SigningSpec) α)
    (limit : Nat) (leftState : CountedSourceState) (rightState : Generic.CappedChain.GlobalHighDirectTracedState)
    (history : Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hstate : Generic.CappedChain.SourceFirstLaneExactGoodStateRelation left right.1 leftState.toSource rightState history)
    (hcacheCount : Generic.cachedEncodingInputCount rightState.causalState.cache right.1.1.secretKey.parameter =
      (history.encodingActions.length : ℝ≥0∞))
    (hencoding : CountedSourceEncodingBudget left.secretKey.parameter leftState)
    (hcount : Generic.FirstLaneOracleSimulation.hazardCount history ≤ leftState.counts.direct)
    (hsourceTrace : leftState.counts.direct = leftState.attackerTrace.hashInputs.length)
    (hbudget : CountedSourceBudget (Generic.Concrete.materializePrecomputation left.cache left.secretKey)
      limit (liftM ((OracleWorld + Generic.SigningSpec).query input) >>= next) leftState) :
    (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl right.1.2) (limitedFirstLaneAction limit right.1.1 right.2 input rightState
      (firstLaneCounters right.1.1.secretKey.parameter rightState history))).run =
        (fun result => ((some result.1,
          firstLaneCounters right.1.1.secretKey.parameter result.1.2 (history ++ result.2)), result.2)) <$>
            (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
              ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2 input).run rightState)).run := by
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
