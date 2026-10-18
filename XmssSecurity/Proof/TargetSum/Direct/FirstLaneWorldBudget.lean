import XmssSecurity.Proof.TargetSum.Direct.FirstLaneSigningBudget
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Direct hash queries and private sampling preserve the observable budget through
their complete ideal step, including a step where the collision monitor fires. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.CappedChain

open Seeded FirstLaneOracleSimulation

theorem globalFirstLane_hash_encodingSamples_le
    (table : CappedChain.GlobalChainValueIndex → Digest) (secretKey : Generic.SecretKey) (input : HashInput)
    (state : CappedChain.GlobalCausalHashState)
    (result : (Digest × CappedChain.GlobalCausalHashState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (CappedChain.globalFirstLaneAttackerHashQueryFromHighRun secretKey input state)).run)) :
    result.2.encodingActions.length ≤
      if CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter (.inr input) then 1 else 0 := by
  cases hencoding : encodingInputLeafIndex? secretKey.parameter input with
  | some leafIndex =>
      have hquery : CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter (.inr input) := by
        change (encodingInputLeafIndex? secretKey.parameter input).isSome = true
        rw [hencoding]
        rfl
      rw [if_pos hquery]
      rw [CappedChain.globalFirstLaneAttackerHashQueryFromHighRun_eq_some _ _ _ _ hencoding] at hresult
      cases hcached : state.cache input with
      | some output =>
          rw [CappedChain.globalFirstLaneAttackerHashQueryAtLeafIndex_eq_cached _ _ _ _ _ hcached] at hresult
          simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hresult
          subst result
          simp [FirstLaneOracleSimulation.ActionTrace.encodingActions]
      | none =>
          rw [CappedChain.globalFirstLaneAttackerHashQueryAtLeafIndex_eq_fresh _ _ _ _ hcached] at hresult
          unfold CappedChain.globalFirstLaneFreshEncodingQuery at hresult
          simp [FirstLaneOracleSimulation.encodingQuery, FirstLaneOracleSimulation.eagerTraceImpl, FirstLaneOracleSimulation.eagerImpl, FirstLaneOracleSimulation.traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
          obtain ⟨output, _, rfl⟩ := hresult
          simp [FirstLaneOracleSimulation.ActionTrace.encodingActions]
  | none =>
      rw [CappedChain.globalFirstLaneAttackerHashQueryFromHighRun_eq_none _ _ _ hencoding] at hresult
      rw [CappedChain.globalFirstLaneLiftRevealProbe_encodingActions_eq_nil table _ result hresult]
      exact Nat.zero_le _

theorem globalFirstLane_uniform_encodingActions_nil
    (table : CappedChain.GlobalChainValueIndex → Digest) (n : Nat) (state : CappedChain.GlobalCausalHashState)
    (result : (Fin (n + 1) × CappedChain.GlobalCausalHashState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedChain.globalFirstLaneUniformImpl n).run state)).run)) : result.2.encodingActions = [] := by
  rw [CappedChain.globalFirstLaneUniformImpl_run, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨head, hhead, htail⟩ := hresult
  simp [FirstLaneOracleSimulation.uniformQuery, FirstLaneOracleSimulation.eagerTraceImpl, FirstLaneOracleSimulation.eagerImpl, FirstLaneOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
  obtain ⟨output, _, rfl⟩ := hhead
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at htail
  subst result
  rfl

theorem globalFirstLane_traced_uniform_encodingActions_nil
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (n : Nat) (state : CappedChain.GlobalHighDirectTracedState)
    (result : (Fin (n + 1) × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key (.inl (.inl n))).run state)).run)) :
    result.2.encodingActions = [] := by
  obtain ⟨base, hbase, hresultEq⟩ := CappedChain.globalExactTracedLift_eager_support_decompose table key
    (.inl (.inl n)) (CappedChain.globalFirstLaneUniformImpl n) state result hresult
  rw [hresultEq]
  exact globalFirstLane_uniform_encodingActions_nil table n state.causalState base hbase

theorem globalFirstLane_traced_hash_encodingSamples_le
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (input : HashInput) (state : CappedChain.GlobalHighDirectTracedState)
    (result : (Digest × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key (.inl (.inr input))).run state)).run)) :
    result.2.encodingActions.length ≤
      if CappedEncodingMonitor.IsEncodingHashQuery key.secretKey.parameter (.inr input) then 1 else 0 := by
  rw [CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl_hash_eq_run] at hresult
  obtain ⟨base, hbase, hresultEq⟩ := CappedChain.globalExactTracedLift_eager_support_decompose table key
    (.inl (.inr input)) (StateT.mk (CappedChain.globalFirstLaneAttackerHashQueryFromHighRun
      key.secretKey input)) state result hresult
  rw [StateT.run_mk] at hbase
  have htrace := congrArg (fun candidate => candidate.2.encodingActions.length) hresultEq
  exact htrace.trans_le (globalFirstLane_hash_encodingSamples_le table
    key.secretKey input state.causalState base hbase)

theorem globalFirstLane_world_encodingSamples_le
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (input : OracleWorld.Domain)
    (state : CappedChain.GlobalHighDirectTracedState)
    (result : (OracleWorld.Range input × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key (.inl input)).run state)).run)) :
    result.2.encodingActions.length ≤
      if CappedEncodingMonitor.IsEncodingHashQuery key.secretKey.parameter input then 1 else 0 := by
  cases input with
  | inl n =>
      rw [globalFirstLane_traced_uniform_encodingActions_nil table key n state result hresult]
      exact Nat.zero_le _
  | inr input =>
      exact globalFirstLane_traced_hash_encodingSamples_le table key input state result hresult

theorem globalFirstLane_world_encodingInputCount_update
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (input : OracleWorld.Domain)
    (state : CappedChain.GlobalHighDirectTracedState)
    (result : (OracleWorld.Range input × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key (.inl input)).run state)).run)) :
    result.1.2.attackerTrace.encodingInputCount key.secretKey.parameter =
      state.attackerTrace.encodingInputCount key.secretKey.parameter +
        if CappedEncodingMonitor.IsEncodingHashQuery key.secretKey.parameter input then 1 else 0 := by
  obtain ⟨base, _hbase, rfl⟩ := CappedChain.globalExactTracedLift_eager_support_decompose table key
    (.inl input) (StateT.mk (CappedChain.globalFirstLaneOracleExecution key input)) state result hresult
  rw [CappedChain.globalExactTracedNextState]
  change (state.attackerTrace ++ CappedChain.attackerActionFragment (.inl input) base.1.1).encodingInputCount
    key.secretKey.parameter = _
  rw [CappedChain.AttackerActionTrace.encodingInputCount_append, attackerActionFragment_encodingInputCount]

theorem countedSourceImpl_world_signing_eq (secretKey : Generic.SecretKey) (input : OracleWorld.Domain)
    (state : CountedSourceState) (result : OracleWorld.Range input × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey (.inl input)).run state)) :
    result.2.counts.signing = state.counts.signing := by
  simp only [countedSourceImpl, StateT.run, support_map] at hresult
  obtain ⟨handled, hhandled, rfl⟩ := hresult
  simp only [referencePhaseCountsImpl, phaseCountsImpl, StateT.run, support_map] at hhandled
  obtain ⟨sample, _hsample, rfl⟩ := hhandled
  rfl

theorem firstLane_world_charge_bounds {α : Type}
    (left : CappedChain.ProgrammedGlobalChainKeygenView)
    (right : CappedChain.ProgrammedGlobalChainKeygenView × (CappedChain.GlobalChainValueIndex → Digest))
    (hrel : CappedChain.ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp (OracleWorld + SigningSpec) α)
    (limit : Nat) (leftState : CountedSourceState) (rightState : CappedChain.GlobalHighDirectTracedState)
    (history : FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hstate : CappedChain.SourceFirstLaneExactGoodStateRelation left right leftState.toSource rightState history)
    (hcacheCount : cachedEncodingInputCount rightState.causalState.cache right.1.secretKey.parameter =
      (history.encodingActions.length : ℝ≥0∞))
    (hencoding : CountedSourceEncodingBudget left.secretKey.parameter leftState)
    (hcount : FirstLaneOracleSimulation.hazardCount history ≤ leftState.counts.direct)
    (hbudget : CountedSourceBudget (Concrete.materializePrecomputation left.cache left.secretKey)
      limit (liftM ((OracleWorld + SigningSpec).query (.inl input)) >>= next) leftState)
    (result : (OracleWorld.Range input × CappedChain.GlobalHighDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
      ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1 (.inl input)).run rightState)).run)) :
    (leftState.counts.direct + CappedChain.directHashActionCost (.inl input) +
      2 * ((history ++ result.2).encodingActions.length -
        result.1.2.attackerTrace.encodingInputCount right.1.secretKey.parameter) ≤ limit) ∧
    observableFirstLaneCharge right.1.secretKey.parameter result.1.2 (history ++ result.2) ≤ limit := by
  let secretKey := Concrete.materializePrecomputation left.cache left.secretKey
  obtain ⟨source, hsource⟩ := probComp_support_nonempty ((countedSourceImpl secretKey (.inl input)).run leftState)
  have hcharge := (hbudget.query_step source hsource).1
  have hdirect := countedSourceImpl_direct_eq secretKey (.inl input) leftState source hsource
  have hsigning := countedSourceImpl_world_signing_eq secretKey input leftState source hsource
  have hparameter := CappedChain.programmedGlobal_secretKey_parameter_eq left right hrel hleftSupport hrightSupport
  have hcacheEq := SourceFirstLaneExactGoodStateRelation.encodingCount_eq hstate
  change cachedEncodingInputCount leftState.counts.cache left.secretKey.parameter =
    cachedEncodingInputCount rightState.causalState.cache left.secretKey.parameter at hcacheEq
  have htraceEq : leftState.attackerTrace = rightState.attackerTrace := hstate.1.2
  have hinitialSamples : history.encodingActions.length ≤
      rightState.attackerTrace.encodingInputCount right.1.secretKey.parameter + leftState.counts.signing := by
    change cachedEncodingInputCount leftState.counts.cache left.secretKey.parameter ≤
      ((leftState.attackerTrace.encodingInputCount left.secretKey.parameter +
        leftState.counts.signing : Nat) : ℝ≥0∞) at hencoding
    rw [hcacheEq, ← hparameter, hcacheCount, htraceEq] at hencoding
    exact_mod_cast hencoding
  have hfragmentSamples := globalFirstLane_world_encodingSamples_le right.2 right.1 input
    rightState result hresult
  have htargetTrace := globalFirstLane_world_encodingInputCount_update right.2 right.1 input
    rightState result hresult
  have hfragment := FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le right.2
    ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1 (.inl input)).run rightState)
    (CappedChain.directHashActionCost (.inl input))
    (CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound right.1 (.inl input) rightState)
    result hresult
  unfold observableFirstLaneCharge CountedSourceState.charge at *
  simp only [FirstLaneOracleSimulation.hazardCount_append, FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append]
  constructor <;> omega

/-- info: 'XmssSecurity.TargetSum.CappedChain.firstLane_world_charge_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms firstLane_world_charge_bounds

end XmssSecurity.TargetSum.CappedChain
