import XmssSecurity.Proof.Generic.CappedGlobalChainHighCoverage
import XmssSecurity.Proof.Common.StateLens

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.Generic.CappedChain

variable [Code]

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

noncomputable def globalHighDirectUniformImpl :
    QueryImpl unifSpec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalCausalUniformImpl

noncomputable def globalHighDirectOracleExecution
    (keyView : ProgrammedGlobalChainKeygenView)
    (input : OracleWorld.Domain) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (OracleWorld.Range input × GlobalCausalHashState) :=
  match input with
  | .inl n => (globalHighDirectUniformImpl n).run state
  | .inr hashInput =>
      (globalCausalAttackerHashQueryFromHigh keyView.secretKey hashInput).run
        state

noncomputable def globalHighDirectOracleImpl
    (keyView : ProgrammedGlobalChainKeygenView) :
    QueryImpl OracleWorld
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input state => globalHighDirectOracleExecution keyView input state

noncomputable def globalHighDirectSigningImpl
    (keyView : ProgrammedGlobalChainKeygenView) :
    QueryImpl SigningSpec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun request state => globalFilteredCausalSigningQuery keyView request state

noncomputable def globalHighDirectBaseMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  globalHighDirectOracleImpl keyView + globalHighDirectSigningImpl keyView

noncomputable def globalHighDirectKeygenAfterMaterial
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial) :
    ProbComp ProgrammedGlobalChainKeygenView := do
  let tree ← treeValues parameter material.1 allTreeValueIndices material.2.2
  pure (({
      secret := material.1
      table := globalChainTrajectoryMaterialTable material
      values := tree.1
      cache := tree.2
    } : CoupledGlobalChainKeygenView).toProgrammedView parameter)

noncomputable def globalHighDirectKeygenAfterParameter
    (parameter : PublicParameter) : ProbComp ProgrammedGlobalChainKeygenView := do
  let material ← programmedGlobalChainTrajectoryMaterial parameter
  globalHighDirectKeygenAfterMaterial parameter material

noncomputable def globalHighDirectKeygen :
    ProbComp ProgrammedGlobalChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  globalHighDirectKeygenAfterParameter parameter

attribute [local irreducible]
  treeValues
  programmedGlobalChainTrajectoryMaterial
  globalChainTrajectoryMaterialTable
  CoupledGlobalChainKeygenView.toProgrammedView

theorem globalHighDirectKeygenAfterMaterial_with_base
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (base : GlobalChainValueIndex → Digest) :
    (do
      let tree ← treeValues parameter material.1 allTreeValueIndices
        material.2.2
      let view : ProgrammedGlobalChainKeygenView :=
        (({
          secret := material.1
          table := globalChainTrajectoryMaterialTable material
          values := tree.1
          cache := tree.2
        } : CoupledGlobalChainKeygenView).toProgrammedView parameter)
      pure (view, base)) = (do
      let keyView ← globalHighDirectKeygenAfterMaterial parameter material
      pure (keyView, base)) := by
  unfold globalHighDirectKeygenAfterMaterial
  simp

theorem coupledGlobalChainKeygenWithBaseHighFull_eq_direct :
    coupledGlobalChainKeygenWithBaseHighFull = (do
      let parameter ← Concrete.samplePublicParameter
      let base ← independentGlobalChainValueTable
      let keyView ← globalHighDirectKeygenAfterParameter parameter
      pure (keyView, base)) := by
  unfold coupledGlobalChainKeygenWithBaseHighFull
    coupledGlobalChainKeygenWithBaseHigh
    programmedGlobalChainTrajectoryMaterialWithBase
    globalHighDirectKeygenAfterParameter independentGlobalChainValueTable
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro base
  apply bind_congr
  intro material
  exact globalHighDirectKeygenAfterMaterial_with_base parameter material base

theorem map_monitorGlobalCausalTrace_projection
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (state : GlobalMonitoredCausalState) :
    (fun result : α × GlobalMonitoredCausalState =>
      ((result.1, result.2.causal), result.2.trace)) <$>
        (monitorGlobalCausalTrace computation).run state =
      (fun result : (α × GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex =>
        (result.1, state.trace ++ result.2)) <$>
          computation state.causal := by
  rw [monitorGlobalCausalTrace_run, Functor.map_map]
  apply map_congr
  intro result
  simp [globalMonitoredCausalResult]

theorem map_actionTracedStateImpl_globalMonitor_erased_step
    {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT GlobalMonitoredCausalState ProbComp))
    (fragment : (input : spec.Domain) → spec.Range input →
      AttackerActionTrace)
    (input : spec.Domain) (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : spec.Range input × GlobalMonitoredTracedState =>
      (result.1, result.2.1)) <$>
        (actionTracedStateImpl impl fragment input).run
          (state, attackerTrace) =
      (impl input).run state := by
  unfold actionTracedStateImpl
  simp [StateT.run_mk, map_eq_bind_pure_comp, bind_assoc]

theorem map_globalHighMonitored_uniform_erased_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest) (n : Nat)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : (OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
        GlobalMonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          (keyView, base) (.inl (.inl n))).run
            (state, attackerTrace) =
      (fun result : (((OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
          GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalCausalUniformImpl n).run state.causal)).run := by
  calc
    _ = (fun result : (OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
          GlobalMonitoredCausalState =>
          ((result.1, result.2.causal), result.2.trace)) <$>
        (globalHighMonitoredBaseMappedAdversaryImpl
          (keyView, base) (.inl (.inl n))).run state := by
      have herase := map_actionTracedStateImpl_globalMonitor_erased_step
        (globalHighMonitoredBaseMappedAdversaryImpl
          (keyView, base)) attackerActionFragment
        (.inl (.inl n)) state attackerTrace
      simpa [globalHighMonitoredMappedAdversaryImpl, Functor.map_map,
        Function.comp_def] using congrArg
          (fun candidate =>
            (fun result : (OracleWorld + SigningSpec).Range (.inl (.inl n)) ×
                GlobalMonitoredCausalState =>
              ((result.1, result.2.causal), result.2.trace)) <$> candidate)
          herase
    _ = _ := by
      unfold globalHighMonitoredBaseMappedAdversaryImpl
      exact map_monitorGlobalCausalTrace_projection _ state

theorem map_globalHighMonitored_hash_erased_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest) (input : HashInput)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : (OracleWorld + SigningSpec).Range (.inl (.inr input)) ×
        GlobalMonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          (keyView, base) (.inl (.inr input))).run
            (state, attackerTrace) =
      (fun result : (((OracleWorld + SigningSpec).Range (.inl (.inr input)) ×
          GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalCausalAttackerHashQueryFromHigh keyView.secretKey input
              ).run state.causal)).run := by
  calc
    _ = (fun result : (OracleWorld + SigningSpec).Range (.inl (.inr input)) ×
          GlobalMonitoredCausalState =>
          ((result.1, result.2.causal), result.2.trace)) <$>
        (globalHighMonitoredBaseMappedAdversaryImpl
          (keyView, base) (.inl (.inr input))).run state := by
      have herase := map_actionTracedStateImpl_globalMonitor_erased_step
        (globalHighMonitoredBaseMappedAdversaryImpl
          (keyView, base)) attackerActionFragment
        (.inl (.inr input)) state attackerTrace
      simpa [globalHighMonitoredMappedAdversaryImpl, Functor.map_map,
        Function.comp_def] using congrArg
          (fun candidate =>
            (fun result : (OracleWorld + SigningSpec).Range
                (.inl (.inr input)) × GlobalMonitoredCausalState =>
              ((result.1, result.2.causal), result.2.trace)) <$> candidate)
          herase
    _ = _ := by
      unfold globalHighMonitoredBaseMappedAdversaryImpl
      exact map_monitorGlobalCausalTrace_projection _ state

theorem map_globalHighMonitored_sign_erased_projection
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest) (request : SignRequest)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : (OracleWorld + SigningSpec).Range (.inr request) ×
        GlobalMonitoredTracedState =>
      ((result.1, result.2.1.causal), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          (keyView, base) (.inr request)).run
            (state, attackerTrace) =
      (fun result : (((OracleWorld + SigningSpec).Range (.inr request) ×
          GlobalCausalHashState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          (globalFilteredCausalSigningQuery keyView request state.causal)).run := by
  calc
    _ = (fun result : (OracleWorld + SigningSpec).Range (.inr request) ×
          GlobalMonitoredCausalState =>
          ((result.1, result.2.causal), result.2.trace)) <$>
        (globalHighMonitoredBaseMappedAdversaryImpl
          (keyView, base) (.inr request)).run state := by
      have herase := map_actionTracedStateImpl_globalMonitor_erased_step
        (globalHighMonitoredBaseMappedAdversaryImpl
          (keyView, base)) attackerActionFragment
        (.inr request) state attackerTrace
      simpa [globalHighMonitoredMappedAdversaryImpl, Functor.map_map,
        Function.comp_def] using congrArg
          (fun candidate =>
            (fun result : (OracleWorld + SigningSpec).Range (.inr request) ×
                GlobalMonitoredCausalState =>
              ((result.1, result.2.causal), result.2.trace)) <$> candidate)
          herase
    _ = _ := by
      unfold globalHighMonitoredBaseMappedAdversaryImpl
      exact map_monitorGlobalCausalTrace_projection _ state

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem evalDist_map_congr_of_evalDist_eq
    (project : α → β) (left right : ProbComp α)
    (hdist : evalDist left = evalDist right) :
    evalDist (project <$> left) = evalDist (project <$> right) := by
  rw [evalDist_map, evalDist_map, hdist]

abbrev GlobalHighDirectTracedState :=
  GlobalCausalHashState × AttackerActionTrace

noncomputable def globalHighDirectTracedMappedAdversaryImpl
    (keyView : ProgrammedGlobalChainKeygenView) :
    QueryImpl (OracleWorld + SigningSpec)
      (StateT GlobalHighDirectTracedState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun input => StateT.mk fun state => do
    let result ←
      (globalHighDirectBaseMappedAdversaryImpl keyView input).run state.1
    pure (result.1,
      (result.2, state.2 ++ attackerActionFragment input result.1))

theorem globalHighMonitoredMappedAdversaryImpl_support_actionTrace_eq
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredTracedState)
    (result : (OracleWorld + SigningSpec).Range input ×
      GlobalMonitoredTracedState)
    (hresult : result ∈ support
      ((globalHighMonitoredMappedAdversaryImpl right input).run state)) :
    result.2.2 = state.2 ++ attackerActionFragment input result.1 := by
  unfold globalHighMonitoredMappedAdversaryImpl actionTracedStateImpl at hresult
  change result ∈ support (do
    let baseResult ←
      (globalHighMonitoredBaseMappedAdversaryImpl right input).run state.1
    pure (baseResult.1,
      (baseResult.2, state.2 ++ attackerActionFragment input baseResult.1)))
      at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨baseResult, _hbaseResult, hfinal⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hfinal
  subst result
  rfl

theorem map_globalHighMonitored_adversary_full_query
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : GlobalMonitoredCausalState)
    (attackerTrace : AttackerActionTrace) :
    (fun result : (OracleWorld + SigningSpec).Range input ×
        GlobalMonitoredTracedState =>
      ((result.1, (result.2.1.causal, result.2.2)), result.2.1.trace)) <$>
        (globalHighMonitoredMappedAdversaryImpl
          (keyView, base) input).run (state, attackerTrace) =
      (fun result : (((OracleWorld + SigningSpec).Range input ×
          GlobalHighDirectTracedState) ×
          RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
        (result.1, state.trace ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          ((globalHighDirectTracedMappedAdversaryImpl keyView input
            ).run (state.causal, attackerTrace))).run := by
  let addAttackerTrace := fun result :
      (((OracleWorld + SigningSpec).Range input × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
    ((result.1.1,
      (result.1.2, attackerTrace ++ attackerActionFragment input result.1.1)),
      result.2)
  have herased :
      (fun result : (OracleWorld + SigningSpec).Range input ×
          GlobalMonitoredTracedState =>
        ((result.1, result.2.1.causal), result.2.1.trace)) <$>
          (globalHighMonitoredMappedAdversaryImpl
            (keyView, base) input).run (state, attackerTrace) =
        (fun result : (((OracleWorld + SigningSpec).Range input ×
            GlobalCausalHashState) ×
            RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) =>
          (result.1, state.trace ++ result.2)) <$>
          (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
            ((globalHighDirectBaseMappedAdversaryImpl keyView input
              ).run state.causal)).run := by
    rcases input with (uniformOrHash | request)
    · rcases uniformOrHash with n | hashInput
      · unfold globalHighDirectBaseMappedAdversaryImpl
          globalHighDirectOracleImpl globalHighDirectOracleExecution
          globalHighDirectUniformImpl
        exact map_globalHighMonitored_uniform_erased_projection keyView base
          n state attackerTrace
      · unfold globalHighDirectBaseMappedAdversaryImpl
          globalHighDirectOracleImpl globalHighDirectOracleExecution
        exact map_globalHighMonitored_hash_erased_projection keyView base
          hashInput state attackerTrace
    · unfold globalHighDirectBaseMappedAdversaryImpl
        globalHighDirectSigningImpl
      exact map_globalHighMonitored_sign_erased_projection keyView base
        request state attackerTrace
  have hlifted := congrArg (fun candidate => addAttackerTrace <$> candidate)
    herased
  simpa [addAttackerTrace, globalHighMonitoredMappedAdversaryImpl,
    actionTracedStateImpl, globalHighDirectTracedMappedAdversaryImpl,
    StateT.run_mk, Functor.map_map, Function.comp_def, simulateQ_bind,
    bind_map_left, List.append_assoc] using hlifted

end XmssSecurity.Generic.CappedChain
