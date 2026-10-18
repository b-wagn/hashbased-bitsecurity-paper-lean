import XmssSecurity.Proof.TargetSum.Direct.FirstLaneSigningBudget
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Direct hash queries and private sampling preserve the observable budget through
their complete ideal step, including a step where the collision monitor fires. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.CappedChain

open Seeded FirstLaneOracleSimulation

theorem globalFirstLane_hash_encodingSamples_le
    (table high : Generic.CappedChain.GlobalChainValueIndex → Digest) (secretKey : Generic.SecretKey) (input : HashInput)
    (state : Generic.CappedChain.GlobalCausalHashState)
    (result : (HashOutput × Generic.CappedChain.GlobalCausalHashState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      (Generic.CappedChain.globalFirstLaneAttackerHashQueryFromHighRun high secretKey input state)).run)) :
    result.2.encodingActions.length ≤
      if Generic.CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter (.inr input) then 1 else 0 := by
  cases hencoding : Generic.encodingInputLeafIndex? secretKey.parameter input with
  | some leafIndex =>
      have hquery : Generic.CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter (.inr input) := by
        change (Generic.encodingInputLeafIndex? secretKey.parameter input).isSome = true
        rw [hencoding]
        rfl
      rw [if_pos hquery]
      rw [Generic.CappedChain.globalFirstLaneAttackerHashQueryFromHighRun_eq_some _ _ _ _ _ hencoding] at hresult
      cases hcached : state.cache input with
      | some output =>
          rw [Generic.CappedChain.globalFirstLaneAttackerHashQueryAtLeafIndex_eq_cached _ _ _ _ _ hcached] at hresult
          simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hresult
          subst result
          simp [Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions]
      | none =>
          rw [Generic.CappedChain.globalFirstLaneAttackerHashQueryAtLeafIndex_eq_fresh _ _ _ _ hcached] at hresult
          unfold Generic.CappedChain.globalFirstLaneFreshEncodingQuery at hresult
          simp [Generic.FirstLaneOracleSimulation.encodingQuery, Generic.FirstLaneOracleSimulation.eagerTraceImpl, Generic.FirstLaneOracleSimulation.eagerImpl, Generic.FirstLaneOracleSimulation.traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hresult
          obtain ⟨output, _, rfl⟩ := hresult
          simp [Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions]
  | none =>
      rw [Generic.CappedChain.globalFirstLaneAttackerHashQueryFromHighRun_eq_none _ _ _ _ hencoding] at hresult
      rw [Generic.CappedChain.globalFirstLaneLiftRevealProbe_encodingActions_eq_nil table _ result hresult]
      exact Nat.zero_le _

theorem globalFirstLane_uniform_encodingActions_nil
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (n : Nat) (state : Generic.CappedChain.GlobalCausalHashState)
    (result : (Fin (n + 1) × Generic.CappedChain.GlobalCausalHashState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalFirstLaneUniformImpl n).run state)).run)) : result.2.encodingActions = [] := by
  rw [Generic.CappedChain.globalFirstLaneUniformImpl_run, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
  obtain ⟨head, hhead, htail⟩ := hresult
  simp [Generic.FirstLaneOracleSimulation.uniformQuery, Generic.FirstLaneOracleSimulation.eagerTraceImpl, Generic.FirstLaneOracleSimulation.eagerImpl, Generic.FirstLaneOracleSimulation.traceFragment,
    QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
  obtain ⟨output, _, rfl⟩ := hhead
  simp only [simulateQ_pure, WriterT.run_pure', map_pure, support_pure,
    Set.mem_singleton_iff, Prod.map_apply, id_eq] at htail
  subst result
  rfl

theorem globalFirstLane_traced_uniform_encodingActions_nil
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (n : Nat) (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : (Fin (n + 1) × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh (.inl (.inl n))).run state)).run)) :
    result.2.encodingActions = [] := by
  obtain ⟨base, hbase, hresultEq⟩ := Generic.CappedChain.globalExactTracedLift_eager_support_decompose table key
    (.inl (.inl n)) (Generic.CappedChain.globalFirstLaneUniformImpl n) state result hresult
  rw [hresultEq]
  exact globalFirstLane_uniform_encodingActions_nil table n state.causalState base hbase

theorem globalFirstLane_traced_hash_encodingSamples_le
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (input : HashInput) (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : (HashOutput × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh (.inl (.inr input))).run state)).run)) :
    result.2.encodingActions.length ≤
      if Generic.CappedEncodingMonitor.IsEncodingHashQuery key.secretKey.parameter (.inr input) then 1 else 0 := by
  rw [Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl_hash_eq_run] at hresult
  obtain ⟨base, hbase, hresultEq⟩ := Generic.CappedChain.globalExactTracedLift_eager_support_decompose table key
    (.inl (.inr input)) (StateT.mk (Generic.CappedChain.globalFirstLaneAttackerHashQueryFromHighRun
      (Generic.CappedChain.globalChainValueHighTableOfEdges edgeHigh) key.secretKey input)) state result hresult
  rw [StateT.run_mk] at hbase
  have htrace := congrArg (fun candidate => candidate.2.encodingActions.length) hresultEq
  exact htrace.trans_le (globalFirstLane_hash_encodingSamples_le table
    (Generic.CappedChain.globalChainValueHighTableOfEdges edgeHigh) key.secretKey input state.causalState base hbase)

theorem globalFirstLane_world_encodingSamples_le
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (input : OracleWorld.Domain)
    (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : (OracleWorld.Range input × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh (.inl input)).run state)).run)) :
    result.2.encodingActions.length ≤
      if Generic.CappedEncodingMonitor.IsEncodingHashQuery key.secretKey.parameter input then 1 else 0 := by
  cases input with
  | inl n =>
      rw [globalFirstLane_traced_uniform_encodingActions_nil table key edgeHigh n state result hresult]
      exact Nat.zero_le _
  | inr input =>
      exact globalFirstLane_traced_hash_encodingSamples_le table key edgeHigh input state result hresult

theorem globalFirstLane_world_encodingInputCount_update
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (input : OracleWorld.Domain)
    (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : (OracleWorld.Range input × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh (.inl input)).run state)).run)) :
    result.1.2.attackerTrace.encodingInputCount key.secretKey.parameter =
      state.attackerTrace.encodingInputCount key.secretKey.parameter +
        if Generic.CappedEncodingMonitor.IsEncodingHashQuery key.secretKey.parameter input then 1 else 0 := by
  obtain ⟨base, _hbase, rfl⟩ := Generic.CappedChain.globalExactTracedLift_eager_support_decompose table key
    (.inl input) (StateT.mk (Generic.CappedChain.globalFirstLaneOracleExecution key edgeHigh input)) state result hresult
  rw [Generic.CappedChain.globalExactTracedNextState]
  change (state.attackerTrace ++ Generic.CappedChain.attackerActionFragment (.inl input) base.1.1).encodingInputCount
    key.secretKey.parameter = _
  rw [AttackerActionTrace.encodingInputCount_append, attackerActionFragment_encodingInputCount]

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
    (left : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (right : (Generic.CappedChain.ProgrammedGlobalChainKeygenView × (Generic.CappedChain.GlobalChainValueIndex → Digest)) ×
      (Generic.CappedChain.GlobalChainEdgeIndex → Digest))
    (hrel : Generic.CappedChain.ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp (OracleWorld + Generic.SigningSpec) α)
    (limit : Nat) (leftState : CountedSourceState) (rightState : Generic.CappedChain.GlobalHighDirectTracedState)
    (history : Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hstate : Generic.CappedChain.SourceFirstLaneExactGoodStateRelation left right.1 leftState.toSource rightState history)
    (hcacheCount : Generic.cachedEncodingInputCount rightState.causalState.cache right.1.1.secretKey.parameter =
      (history.encodingActions.length : ℝ≥0∞))
    (hencoding : CountedSourceEncodingBudget left.secretKey.parameter leftState)
    (hcount : Generic.FirstLaneOracleSimulation.hazardCount history ≤ leftState.counts.direct)
    (hbudget : CountedSourceBudget (Generic.Concrete.materializePrecomputation left.cache left.secretKey)
      limit (liftM ((OracleWorld + Generic.SigningSpec).query (.inl input)) >>= next) leftState)
    (result : (OracleWorld.Range input × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl right.1.2)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2 (.inl input)).run rightState)).run)) :
    (leftState.counts.direct + Generic.CappedChain.directHashActionCost (.inl input) +
      2 * ((history ++ result.2).encodingActions.length -
        result.1.2.attackerTrace.encodingInputCount right.1.1.secretKey.parameter) ≤ limit) ∧
    observableFirstLaneCharge right.1.1.secretKey.parameter result.1.2 (history ++ result.2) ≤ limit := by
  let secretKey := Generic.Concrete.materializePrecomputation left.cache left.secretKey
  obtain ⟨source, hsource⟩ := Generic.probComp_support_nonempty ((countedSourceImpl secretKey (.inl input)).run leftState)
  have hcharge := (hbudget.query_step source hsource).1
  have hdirect := countedSourceImpl_direct_eq secretKey (.inl input) leftState source hsource
  have hsigning := countedSourceImpl_world_signing_eq secretKey input leftState source hsource
  have hparameter := Generic.CappedChain.programmedGlobal_secretKey_parameter_eq left right hrel hleftSupport hrightSupport
  have hcacheEq := SourceFirstLaneExactGoodStateRelation.encodingCount_eq hstate
  change Generic.cachedEncodingInputCount leftState.counts.cache left.secretKey.parameter =
    Generic.cachedEncodingInputCount rightState.causalState.cache left.secretKey.parameter at hcacheEq
  have htraceEq : leftState.attackerTrace = rightState.attackerTrace := hstate.1.2
  have hinitialSamples : history.encodingActions.length ≤
      rightState.attackerTrace.encodingInputCount right.1.1.secretKey.parameter + leftState.counts.signing := by
    change Generic.cachedEncodingInputCount leftState.counts.cache left.secretKey.parameter ≤
      ((leftState.attackerTrace.encodingInputCount left.secretKey.parameter +
        leftState.counts.signing : Nat) : ℝ≥0∞) at hencoding
    rw [hcacheEq, ← hparameter, hcacheCount, htraceEq] at hencoding
    exact_mod_cast hencoding
  have hfragmentSamples := globalFirstLane_world_encodingSamples_le right.1.2 right.1.1 right.2 input
    rightState result hresult
  have htargetTrace := globalFirstLane_world_encodingInputCount_update right.1.2 right.1.1 right.2 input
    rightState result hresult
  have hfragment := Generic.FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le right.1.2
    ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl right.1.1 right.2 (.inl input)).run rightState)
    (Generic.CappedChain.directHashActionCost (.inl input))
    (Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound right.1.1 right.2 (.inl input) rightState)
    result hresult
  unfold observableFirstLaneCharge CountedSourceState.charge at *
  simp only [Generic.FirstLaneOracleSimulation.hazardCount_append, Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append]
  constructor <;> omega

/-- info: 'XmssSecurity.TargetSum.CappedChain.firstLane_world_charge_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms firstLane_world_charge_bounds

end XmssSecurity.TargetSum.CappedChain
