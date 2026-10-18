import XmssSecurity.Proof.TargetSum.Direct.FirstLaneWorldBudget
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Every ideal query starting from related states stays within an observable budget,
including the first query that breaks the relation. Direct calls can be charged through
the attacker log, so the bound can be enforced without access to the hidden table. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.CappedChain

open Seeded FirstLaneOracleSimulation

theorem firstLane_step_charge_bounds {α : Type}
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
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit (liftM ((OracleWorld + SigningSpec).query input) >>= next) leftState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedChain.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
      ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1 input).run rightState)).run)) :
    (leftState.counts.direct + CappedChain.directHashActionCost input +
      2 * ((history ++ result.2).encodingActions.length -
        result.1.2.attackerTrace.encodingInputCount right.1.secretKey.parameter) ≤ limit) ∧
    observableFirstLaneCharge right.1.secretKey.parameter result.1.2 (history ++ result.2) ≤ limit := by
  cases input with
  | inl input =>
      exact firstLane_world_charge_bounds left right hrel hleftSupport hrightSupport input next
        limit leftState rightState history hstate hcacheCount hencoding hcount hbudget result hresult
  | inr request =>
      simpa only [CappedChain.directHashActionCost, Nat.add_zero] using firstLane_signing_charge_bounds left right hrel
        hleftSupport hrightSupport request next limit leftState rightState history hstate hcacheCount
        hencoding hcount hbudget result hresult

theorem countedSourceImpl_hashInputs_update (secretKey : Generic.SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CountedSourceState)
    (result : (OracleWorld + SigningSpec).Range input × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey input).run state)) :
    result.2.attackerTrace.hashInputs.length = state.attackerTrace.hashInputs.length + CappedChain.directHashActionCost input := by
  simp only [countedSourceImpl, StateT.run, support_map] at hresult
  obtain ⟨handled, _, rfl⟩ := hresult
  simp only [countedSourceUpdate, CappedChain.AttackerActionTrace.hashInputs_append, List.length_append,
    CappedChain.attackerActionFragment_hashInputs_length]

theorem globalExactTracedLift_hashInputs_update
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT CappedChain.GlobalCausalHashState (OracleComp CappedChain.GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input))
    (state : CappedChain.GlobalDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedChain.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedChain.globalExactTracedLift key input base).run state)).run)) :
    result.1.2.attackerTrace.hashInputs.length = state.attackerTrace.hashInputs.length + CappedChain.directHashActionCost input := by
  obtain ⟨handled, _hhandled, hresultEq⟩ := CappedChain.globalExactTracedLift_eager_support_decompose table key
    input base state result hresult
  rw [hresultEq, CappedChain.globalExactTracedNextState]
  change (state.attackerTrace ++ CappedChain.attackerActionFragment input handled.1.1).hashInputs.length = _
  rw [CappedChain.AttackerActionTrace.hashInputs_append, List.length_append, CappedChain.attackerActionFragment_hashInputs_length]

theorem globalFirstLane_query_hashInputs_update
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CappedChain.GlobalDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedChain.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key input).run state)).run)) :
    result.1.2.attackerTrace.hashInputs.length = state.attackerTrace.hashInputs.length + CappedChain.directHashActionCost input := by
  cases input with
  | inl input =>
      exact globalExactTracedLift_hashInputs_update table key (.inl input)
        (StateT.mk (CappedChain.globalFirstLaneOracleExecution key input)) state result hresult
  | inr request =>
      exact globalExactTracedLift_hashInputs_update table key (.inr request)
        (CappedChain.globalFirstLaneSigningImpl key request) state result hresult

noncomputable def observableFirstLaneDirectCharge (parameter : PublicParameter)
    (state : CappedChain.GlobalDirectTracedState) (trace : FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex) : Nat :=
  state.attackerTrace.hashInputs.length +
    2 * (trace.encodingActions.length - state.attackerTrace.encodingInputCount parameter)

theorem firstLane_step_observableDirectCharge_le {α : Type}
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
      limit (liftM ((OracleWorld + SigningSpec).query input) >>= next) leftState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedChain.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
      ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1 input).run rightState)).run)) :
    observableFirstLaneDirectCharge right.1.secretKey.parameter result.1.2 (history ++ result.2) ≤ limit := by
  have hstep := (firstLane_step_charge_bounds left right hrel hleftSupport hrightSupport input next limit
    leftState rightState history hstate hcacheCount hencoding hcount hbudget result hresult).1
  have htraceEq : leftState.attackerTrace = rightState.attackerTrace := hstate.1.2
  unfold observableFirstLaneDirectCharge
  rw [globalFirstLane_query_hashInputs_update right.2 right.1 input rightState result hresult,
    ← htraceEq, ← hsourceTrace]
  exact hstep

/-- info: 'XmssSecurity.TargetSum.CappedChain.firstLane_step_observableDirectCharge_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms firstLane_step_observableDirectCharge_le

end XmssSecurity.TargetSum.CappedChain
