import XmssSecurity.Proof.TargetSum.Direct.FirstLaneWorldBudget
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Every ideal query starting from related states stays within an observable budget,
including the first query that breaks the relation. Direct calls can be charged through
the attacker log, so the bound can be enforced without access to the hidden table. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.CappedChain

open Seeded FirstLaneOracleSimulation

theorem firstLane_step_charge_bounds {α : Type}
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
    (hbudget : CountedSourceBudget (Generic.Concrete.materializePrecomputation left.cache left.secretKey)
      limit (liftM ((OracleWorld + Generic.SigningSpec).query input) >>= next) leftState)
    (result : ((OracleWorld + Generic.SigningSpec).Range input × Generic.CappedChain.GlobalHighDirectTracedState) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2 input).run rightState)).run)) :
    (leftState.counts.direct + Generic.CappedChain.directHashActionCost input +
      2 * ((history ++ result.2).encodingActions.length -
        result.1.2.attackerTrace.encodingInputCount right.1.1.secretKey.parameter) ≤ limit) ∧
    observableFirstLaneCharge right.1.1.secretKey.parameter result.1.2 (history ++ result.2) ≤ limit := by
  cases input with
  | inl input =>
      exact firstLane_world_charge_bounds left right hrel hleftSupport hrightSupport input next
        limit leftState rightState history hstate hcacheCount hencoding hcount hbudget result hresult
  | inr request =>
      simpa only [Generic.CappedChain.directHashActionCost, Nat.add_zero] using firstLane_signing_charge_bounds left right hrel
        hleftSupport hrightSupport request next limit leftState rightState history hstate hcacheCount
        hencoding hcount hbudget result hresult

theorem countedSourceImpl_hashInputs_update (secretKey : Generic.SecretKey)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (state : CountedSourceState)
    (result : (OracleWorld + Generic.SigningSpec).Range input × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey input).run state)) :
    result.2.attackerTrace.hashInputs.length = state.attackerTrace.hashInputs.length + Generic.CappedChain.directHashActionCost input := by
  simp only [countedSourceImpl, StateT.run, support_map] at hresult
  obtain ⟨handled, _, rfl⟩ := hresult
  simp only [countedSourceUpdate, Generic.CappedChain.AttackerActionTrace.hashInputs_append, List.length_append,
    Generic.CappedChain.attackerActionFragment_hashInputs_length]

theorem globalExactTracedLift_hashInputs_update
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + Generic.SigningSpec).Domain)
    (base : StateT Generic.CappedChain.GlobalCausalHashState (OracleComp Generic.CappedChain.GlobalFirstLaneWorld)
      ((OracleWorld + Generic.SigningSpec).Range input))
    (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : ((OracleWorld + Generic.SigningSpec).Range input × Generic.CappedChain.GlobalHighDirectTracedState) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalExactTracedLift key input base).run state)).run)) :
    result.1.2.attackerTrace.hashInputs.length = state.attackerTrace.hashInputs.length + Generic.CappedChain.directHashActionCost input := by
  obtain ⟨handled, _hhandled, hresultEq⟩ := Generic.CappedChain.globalExactTracedLift_eager_support_decompose table key
    input base state result hresult
  rw [hresultEq, Generic.CappedChain.globalExactTracedNextState]
  change (state.attackerTrace ++ Generic.CappedChain.attackerActionFragment input handled.1.1).hashInputs.length = _
  rw [Generic.CappedChain.AttackerActionTrace.hashInputs_append, List.length_append, Generic.CappedChain.attackerActionFragment_hashInputs_length]

theorem globalFirstLane_query_hashInputs_update
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (input : (OracleWorld + Generic.SigningSpec).Domain)
    (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : ((OracleWorld + Generic.SigningSpec).Range input × Generic.CappedChain.GlobalHighDirectTracedState) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state)).run)) :
    result.1.2.attackerTrace.hashInputs.length = state.attackerTrace.hashInputs.length + Generic.CappedChain.directHashActionCost input := by
  cases input with
  | inl input =>
      exact globalExactTracedLift_hashInputs_update table key (.inl input)
        (StateT.mk (Generic.CappedChain.globalFirstLaneOracleExecution key edgeHigh input)) state result hresult
  | inr request =>
      exact globalExactTracedLift_hashInputs_update table key (.inr request)
        (Generic.CappedChain.globalFirstLaneSigningImpl key request) state result hresult

noncomputable def observableFirstLaneDirectCharge (parameter : PublicParameter)
    (state : Generic.CappedChain.GlobalHighDirectTracedState) (trace : Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex) : Nat :=
  state.attackerTrace.hashInputs.length +
    2 * (trace.encodingActions.length - state.attackerTrace.encodingInputCount parameter)

theorem firstLane_step_observableDirectCharge_le {α : Type}
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
      limit (liftM ((OracleWorld + Generic.SigningSpec).query input) >>= next) leftState)
    (result : ((OracleWorld + Generic.SigningSpec).Range input × Generic.CappedChain.GlobalHighDirectTracedState) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2 input).run rightState)).run)) :
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
