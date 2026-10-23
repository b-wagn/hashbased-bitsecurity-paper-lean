import Xmss.Proof.TargetSum.Direct.FirstLaneWorldBudget
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Every ideal query starting from related states stays within an observable budget,
including the first query that breaks the relation. Direct calls can be charged through
the attacker log, so the bound can be enforced without access to the hidden table. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.CappedExecution

open Seeded FirstLaneOracleSimulation

theorem firstLane_step_charge_bounds {α : Type}
    (left : CappedExecution.ProgrammedGlobalChainKeygenView)
    (right : CappedExecution.ProgrammedGlobalChainKeygenView × (CappedExecution.GlobalChainValueIndex → Digest))
    (hrel : CappedExecution.ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (limit : Nat) (leftState : CountedSourceState) (rightState : CappedExecution.GlobalDirectTracedState)
    (history : FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hstate : CappedExecution.SourceFirstLaneExactGoodStateRelation left right leftState.toSource rightState history)
    (hcacheCount : cachedEncodingInputCount rightState.causalState.cache right.1.secretKey.parameter =
      (history.encodingActions.length : ℝ≥0∞))
    (hencoding : CountedSourceEncodingBudget left.secretKey.parameter leftState)
    (hcount : FirstLaneOracleSimulation.hazardCount history ≤ leftState.counts.direct)
    (hbudget : CountedSourceBudget (Keygen.materializePrecomputation left.cache left.secretKey)
      limit (liftM ((OracleWorld + SigningSpec).query input) >>= next) leftState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedExecution.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
      ((CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl right.1 input).run rightState)).run)) :
    (leftState.counts.direct + CappedExecution.directHashActionCost input +
      2 * ((history ++ result.2).encodingActions.length -
        result.1.2.attackerTrace.encodingInputCount right.1.secretKey.parameter) ≤ limit) ∧
    observableFirstLaneCharge right.1.secretKey.parameter result.1.2 (history ++ result.2) ≤ limit := by
  cases input with
  | inl input =>
      exact firstLane_world_charge_bounds left right hrel hleftSupport hrightSupport input next
        limit leftState rightState history hstate hcacheCount hencoding hcount hbudget result hresult
  | inr request =>
      simpa only [CappedExecution.directHashActionCost, Nat.add_zero] using firstLane_signing_charge_bounds left right hrel
        hleftSupport hrightSupport request next limit leftState rightState history hstate hcacheCount
        hencoding hcount hbudget result hresult

theorem countedSourceImpl_hashInputs_update (secretKey : Generic.SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CountedSourceState)
    (result : (OracleWorld + SigningSpec).Range input × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey input).run state)) :
    result.2.attackerTrace.hashInputs.length = state.attackerTrace.hashInputs.length + CappedExecution.directHashActionCost input := by
  simp only [countedSourceImpl, StateT.run, support_map] at hresult
  obtain ⟨handled, _, rfl⟩ := hresult
  simp only [countedSourceUpdate, CappedExecution.AttackerActionTrace.hashInputs_append, List.length_append,
    CappedExecution.attackerActionFragment_hashInputs_length]

theorem globalExactTracedLift_hashInputs_update
    (table : CappedExecution.GlobalChainValueIndex → Digest) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT CappedExecution.GlobalCausalHashState (OracleComp CappedExecution.GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : CappedExecution.GlobalDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedExecution.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedExecution.globalExactTracedLift key input base).run state)).run)) :
    result.1.2.attackerTrace.hashInputs.length = state.attackerTrace.hashInputs.length + CappedExecution.directHashActionCost input := by
  obtain ⟨handled, _hhandled, hresultEq⟩ := CappedExecution.globalExactTracedLift_eager_support_decompose table key
    input base state result hresult
  rw [hresultEq, CappedExecution.globalExactTracedNextState]
  change (state.attackerTrace ++ CappedExecution.attackerActionFragment input handled.1.1).hashInputs.length = _
  rw [CappedExecution.AttackerActionTrace.hashInputs_append, List.length_append, CappedExecution.attackerActionFragment_hashInputs_length]

theorem globalFirstLane_query_hashInputs_update
    (table : CappedExecution.GlobalChainValueIndex → Digest) (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CappedExecution.GlobalDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedExecution.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl key input).run state)).run)) :
    result.1.2.attackerTrace.hashInputs.length = state.attackerTrace.hashInputs.length + CappedExecution.directHashActionCost input := by
  cases input with
  | inl input =>
      exact globalExactTracedLift_hashInputs_update table key (.inl input)
        (StateT.mk (CappedExecution.globalFirstLaneOracleExecution key input)) state result hresult
  | inr request =>
      exact globalExactTracedLift_hashInputs_update table key (.inr request)
        (CappedExecution.globalFirstLaneSigningImpl key request) state result hresult

noncomputable def observableFirstLaneDirectCharge (parameter : PublicParameter)
    (state : CappedExecution.GlobalDirectTracedState) (trace : FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex) : Nat :=
  state.attackerTrace.hashInputs.length +
    2 * (trace.encodingActions.length - state.attackerTrace.encodingInputCount parameter)

theorem firstLane_step_observableDirectCharge_le {α : Type}
    (left : CappedExecution.ProgrammedGlobalChainKeygenView)
    (right : CappedExecution.ProgrammedGlobalChainKeygenView × (CappedExecution.GlobalChainValueIndex → Digest))
    (hrel : CappedExecution.ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (limit : Nat) (leftState : CountedSourceState) (rightState : CappedExecution.GlobalDirectTracedState)
    (history : FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hstate : CappedExecution.SourceFirstLaneExactGoodStateRelation left right leftState.toSource rightState history)
    (hcacheCount : cachedEncodingInputCount rightState.causalState.cache right.1.secretKey.parameter =
      (history.encodingActions.length : ℝ≥0∞))
    (hencoding : CountedSourceEncodingBudget left.secretKey.parameter leftState)
    (hcount : FirstLaneOracleSimulation.hazardCount history ≤ leftState.counts.direct)
    (hsourceTrace : leftState.counts.direct = leftState.attackerTrace.hashInputs.length)
    (hbudget : CountedSourceBudget (Keygen.materializePrecomputation left.cache left.secretKey)
      limit (liftM ((OracleWorld + SigningSpec).query input) >>= next) leftState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedExecution.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
      ((CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl right.1 input).run rightState)).run)) :
    observableFirstLaneDirectCharge right.1.secretKey.parameter result.1.2 (history ++ result.2) ≤ limit := by
  have hstep := (firstLane_step_charge_bounds left right hrel hleftSupport hrightSupport input next limit
    leftState rightState history hstate hcacheCount hencoding hcount hbudget result hresult).1
  have htraceEq : leftState.attackerTrace = rightState.attackerTrace := hstate.1.2
  unfold observableFirstLaneDirectCharge
  rw [globalFirstLane_query_hashInputs_update right.2 right.1 input rightState result hresult,
    ← htraceEq, ← hsourceTrace]
  exact hstep

/-- info: 'Xmss.TargetSum.CappedExecution.firstLane_step_observableDirectCharge_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms firstLane_step_observableDirectCharge_le

end Xmss.TargetSum.CappedExecution
