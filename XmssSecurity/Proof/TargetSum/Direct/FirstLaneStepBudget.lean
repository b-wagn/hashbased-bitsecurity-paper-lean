import XmssSecurity.Proof.TargetSum.Direct.FirstLaneWorldBudget

/-! Every ideal query starting from related states stays within an observable budget,
including the first query that breaks the relation. Direct calls can be charged through
the attacker log, so the bound can be enforced without access to the hidden table. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.CappedChain

open Seeded FirstLaneOracleSimulation

theorem firstLane_step_charge_bounds {α : Type}
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
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit (liftM ((OracleWorld + SigningSpec).query input) >>= next) leftState)
    (result : ((OracleWorld + SigningSpec).Range input × GlobalHighDirectTracedState) ×
      ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl right.1.2)
      ((globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2 input).run rightState)).run)) :
    (leftState.counts.direct + directHashActionCost input +
      2 * ((history ++ result.2).encodingActions.length -
        result.1.2.attackerTrace.encodingInputCount right.1.1.secretKey.parameter) ≤ limit) ∧
    observableFirstLaneCharge right.1.1.secretKey.parameter result.1.2 (history ++ result.2) ≤ limit := by
  cases input with
  | inl input =>
      exact firstLane_world_charge_bounds left right hrel hleftSupport hrightSupport input next
        limit leftState rightState history hstate hcacheCount hencoding hcount hbudget result hresult
  | inr request =>
      simpa only [directHashActionCost, Nat.add_zero] using firstLane_signing_charge_bounds left right hrel
        hleftSupport hrightSupport request next limit leftState rightState history hstate hcacheCount
        hencoding hcount hbudget result hresult

theorem countedSourceImpl_hashInputs_update (secretKey : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CountedSourceState)
    (result : (OracleWorld + SigningSpec).Range input × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey input).run state)) :
    result.2.attackerTrace.hashInputs.length = state.attackerTrace.hashInputs.length + directHashActionCost input := by
  simp only [countedSourceImpl, StateT.run, support_map] at hresult
  obtain ⟨handled, _, rfl⟩ := hresult
  simp only [countedSourceUpdate, AttackerActionTrace.hashInputs_append, List.length_append,
    attackerActionFragment_hashInputs_length]

theorem countedSource_direct_eq_hashInputs {α : Type} (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CountedSourceState)
    (hstate : state.counts.direct = state.attackerTrace.hashInputs.length)
    (result : α × CountedSourceState)
    (hresult : result ∈ support ((simulateQ (countedSourceImpl secretKey) computation).run state)) :
    result.2.counts.direct = result.2.attackerTrace.hashInputs.length := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hstate
  | query_bind input next ih =>
      rw [Direct.run_simulateQ_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      apply ih head.1 head.2 _ result htail
      rw [countedSourceImpl_direct_eq secretKey input state head hhead,
        countedSourceImpl_hashInputs_update secretKey input state head hhead, hstate]

theorem globalExactTracedLift_hashInputs_update
    (table : GlobalChainValueIndex → Digest) (key : ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT GlobalCausalHashState (OracleComp GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : GlobalHighDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × GlobalHighDirectTracedState) ×
      ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      ((globalExactTracedLift key input base).run state)).run)) :
    result.1.2.attackerTrace.hashInputs.length = state.attackerTrace.hashInputs.length + directHashActionCost input := by
  obtain ⟨handled, _hhandled, hresultEq⟩ := globalExactTracedLift_eager_support_decompose table key
    input base state result hresult
  rw [hresultEq, globalExactTracedNextState]
  change (state.attackerTrace ++ attackerActionFragment input handled.1.1).hashInputs.length = _
  rw [AttackerActionTrace.hashInputs_append, List.length_append, attackerActionFragment_hashInputs_length]

theorem globalFirstLane_query_hashInputs_update
    (table : GlobalChainValueIndex → Digest) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalHighDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × GlobalHighDirectTracedState) ×
      ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl table)
      ((globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state)).run)) :
    result.1.2.attackerTrace.hashInputs.length = state.attackerTrace.hashInputs.length + directHashActionCost input := by
  cases input with
  | inl input =>
      exact globalExactTracedLift_hashInputs_update table key (.inl input)
        (StateT.mk (globalFirstLaneOracleExecution key edgeHigh input)) state result hresult
  | inr request =>
      exact globalExactTracedLift_hashInputs_update table key (.inr request)
        (globalFirstLaneSigningImpl key request) state result hresult

noncomputable def observableFirstLaneDirectCharge (parameter : PublicParameter)
    (state : GlobalHighDirectTracedState) (trace : ActionTrace GlobalChainValueIndex) : Nat :=
  state.attackerTrace.hashInputs.length +
    2 * (trace.encodingActions.length - state.attackerTrace.encodingInputCount parameter)

theorem firstLane_step_observableDirectCharge_le {α : Type}
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
      limit (liftM ((OracleWorld + SigningSpec).query input) >>= next) leftState)
    (result : ((OracleWorld + SigningSpec).Range input × GlobalHighDirectTracedState) ×
      ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (eagerTraceImpl right.1.2)
      ((globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2 input).run rightState)).run)) :
    observableFirstLaneDirectCharge right.1.1.secretKey.parameter result.1.2 (history ++ result.2) ≤ limit := by
  have hstep := (firstLane_step_charge_bounds left right hrel hleftSupport hrightSupport input next limit
    leftState rightState history hstate hcacheCount hencoding hcount hbudget result hresult).1
  have htraceEq : leftState.attackerTrace = rightState.attackerTrace := hstate.1.2
  unfold observableFirstLaneDirectCharge
  rw [globalFirstLane_query_hashInputs_update right.1.2 right.1.1 right.2 input rightState result hresult,
    ← htraceEq, ← hsourceTrace]
  exact hstep

/-- info: 'XmssSecurity.TargetSum.CappedChain.firstLane_step_observableDirectCharge_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms firstLane_step_observableDirectCharge_le

end XmssSecurity.TargetSum.CappedChain
