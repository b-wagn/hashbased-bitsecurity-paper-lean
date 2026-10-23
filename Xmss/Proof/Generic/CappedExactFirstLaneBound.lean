import Xmss.Proof.Generic.CappedExactFirstLaneTransportReduction
import Xmss.Proof.Generic.BoundedFirstLaneCoupling
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

open OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
open OracleComp.ProgramLogic.Relational

namespace Xmss.Generic.CappedExecution

variable [Code]

set_option maxRecDepth 1000000

def globalFirstLaneExactFullProjection {α : Type}
    (chainPrefix : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex)
    (result : (α × GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) :
    (α × GlobalDirectTracedState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  (result.1, chainPrefix ++ result.2.chainActions)

theorem map_eagerTrace_erasure_eq {α : Type}
    (base : GlobalChainValueIndex → Digest)
    (chainPrefix : RevealProbeOracleSimulation.ActionTrace
      GlobalChainValueIndex)
    (firstLane : OracleComp GlobalFirstLaneWorld
      (α × GlobalDirectTracedState))
    (direct : OracleComp
      (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (α × GlobalDirectTracedState))
    (herase : GlobalFirstLaneErases firstLane direct) :
    (fun result => (result.1, chainPrefix ++ result.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl base)
          direct).run =
      globalFirstLaneExactFullProjection chainPrefix <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
          firstLane).run := by
  have htarget :=
    simulate_globalFirstLaneEagerTrace_chainProjection base firstLane
  rw [herase] at htarget
  have htarget' := congrArg
    (fun computation =>
      (fun result => (result.1, chainPrefix ++ result.2)) <$> computation)
    htarget
  unfold globalFirstLaneExactFullProjection
  simpa [Functor.map_map, Function.comp_def] using htarget'.symm

theorem map_globalMonitored_action_eq_firstLane
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (monitoredState : GlobalMonitoredTracedState) :
    (fun result => ((result.1, GlobalDirectTracedState.mk
      result.2.1.causal result.2.2), result.2.1.trace)) <$>
        (globalMonitoredMappedAdversaryImpl
          (keyView, base) input).run monitoredState =
      globalFirstLaneExactFullProjection monitoredState.1.trace <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
          ((globalFirstLaneExactTracedMappedAdversaryImpl keyView
            input).run (GlobalDirectTracedState.mk monitoredState.1.causal
              monitoredState.2))).run := by
  have hmonitored := map_globalMonitored_adversary_exact_query keyView base
    input monitoredState
  have herase := globalFirstLaneErase_exactTracedMappedAdversaryImpl keyView
    input (GlobalDirectTracedState.mk monitoredState.1.causal monitoredState.2)
  rw [hmonitored]
  exact map_eagerTrace_erasure_eq base monitoredState.1.trace _ _ herase

theorem relTriple_globalMonitored_firstLane_action
    (keyView : ProgrammedGlobalChainKeygenView)
    (base : GlobalChainValueIndex → Digest)
    (input : (OracleWorld + SigningSpec).Domain)
    (monitoredState : GlobalMonitoredTracedState) :
    RelTriple
      ((globalMonitoredMappedAdversaryImpl
        (keyView, base) input).run monitoredState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
        ((globalFirstLaneExactTracedMappedAdversaryImpl keyView
          input).run (GlobalDirectTracedState.mk monitoredState.1.causal
            monitoredState.2))).run)
      (fun monitoredResult firstLaneResult =>
        ((monitoredResult.1, GlobalDirectTracedState.mk
            monitoredResult.2.1.causal monitoredResult.2.2),
            monitoredResult.2.1.trace) =
          globalFirstLaneExactFullProjection monitoredState.1.trace
            firstLaneResult ∧
        monitoredResult ∈ support
          ((globalMonitoredMappedAdversaryImpl
            (keyView, base) input).run monitoredState) ∧
        firstLaneResult ∈ support
          ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
            ((globalFirstLaneExactTracedMappedAdversaryImpl keyView
              input).run (GlobalDirectTracedState.mk monitoredState.1.causal
                monitoredState.2))).run)) := by
  classical
  letI : DecidableEq
      (((OracleWorld + SigningSpec).Range input ×
        GlobalDirectTracedState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
    Classical.decEq _
  apply relTriple_of_evalDist_map_eq_with_support_general
  exact congrArg evalDist
    (map_globalMonitored_action_eq_firstLane keyView base input
      monitoredState)

def globalStateOfFirstLane
    (firstLaneState : GlobalDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace
      GlobalChainValueIndex) : GlobalMonitoredTracedState :=
  (⟨firstLaneState.causalState, trace.chainActions⟩,
    firstLaneState.attackerTrace)

theorem globalStateOfFirstLane_eq
    (monitoredState : GlobalMonitoredTracedState)
    (firstLaneState : GlobalDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hstate : firstLaneState = GlobalDirectTracedState.mk
      monitoredState.1.causal monitoredState.2)
    (htrace : trace.chainActions = monitoredState.1.trace) :
    globalStateOfFirstLane firstLaneState trace = monitoredState := by
  subst firstLaneState
  rcases monitoredState with ⟨⟨causal, chainTrace⟩, attackerTrace⟩
  change trace.chainActions = chainTrace at htrace
  subst chainTrace
  rfl

structure GlobalFirstLaneProjectionFacts {Result : Type}
    (history : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (monitoredResult : Result × GlobalMonitoredTracedState)
    (firstLaneResult : (Result × GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop where
  output : monitoredResult.1 = firstLaneResult.1.1
  causal : monitoredResult.2.1.causal = firstLaneResult.1.2.causalState
  attacker : monitoredResult.2.2 = firstLaneResult.1.2.attackerTrace
  chain : monitoredResult.2.1.trace =
    history.chainActions ++ firstLaneResult.2.chainActions
  state : globalStateOfFirstLane firstLaneResult.1.2
    (history ++ firstLaneResult.2) = monitoredResult.2

theorem GlobalFirstLaneProjectionFacts.of_projection {Result : Type}
    (history : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (monitoredResult : Result × GlobalMonitoredTracedState)
    (firstLaneResult : (Result × GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hprojection :
      ((monitoredResult.1, GlobalDirectTracedState.mk
        monitoredResult.2.1.causal monitoredResult.2.2), monitoredResult.2.1.trace) =
        globalFirstLaneExactFullProjection history.chainActions
          firstLaneResult) :
    GlobalFirstLaneProjectionFacts history monitoredResult firstLaneResult := by
  have hchain : monitoredResult.2.1.trace =
      history.chainActions ++ firstLaneResult.2.chainActions := by
    simpa [globalFirstLaneExactFullProjection] using
      congrArg Prod.snd hprojection
  refine ⟨congrArg (fun result => result.1.1) hprojection,
    congrArg (fun result => result.1.2.causalState) hprojection,
    congrArg (fun result => result.1.2.attackerTrace) hprojection,
    hchain, ?_⟩
  apply globalStateOfFirstLane_eq
  · exact congrArg (fun result => result.1.2) hprojection |>.symm
  · rw [FirstLaneOracleSimulation.ActionTrace.chainActions_append]
    exact hchain.symm

theorem GlobalFirstLaneProjectionFacts.combinedHit_of_bad {Result : Type}
    {history : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex}
    {monitoredResult : Result × GlobalMonitoredTracedState}
    {firstLaneResult : (Result × GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex}
    (hfacts : GlobalFirstLaneProjectionFacts history monitoredResult firstLaneResult)
    (base : GlobalChainValueIndex → Digest)
    (hbad : monitoredResult.2.1.bad base) :
    FirstLaneOracleSimulation.CombinedHit base
      (history ++ firstLaneResult.2) := by
  right
  rw [FirstLaneOracleSimulation.ActionTrace.chainActions_append,
    ← hfacts.chain]
  exact monitoredResult.2.1.bad_implies_runObserved base hbad

def SourceFirstLaneExactGoodStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftState : SourceExactTracedState)
    (firstLaneState : GlobalDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace
      GlobalChainValueIndex) : Prop :=
  GlobalSigningMonitoredTracedStateRelation left right
      (sourceExactSigningProjection leftState)
      (globalStateOfFirstLane firstLaneState trace) ∧
    List.Sublist leftState.1.2 trace.encodingActions ∧
    List.Sublist
      (CappedEncodingMonitor.validObservedSignLeafIndices trace.encodingActions)
      (firstLaneState.attackerTrace.toSigningLog.map fun entry => entry.1.epoch)

theorem relTriple_sourceExact_firstLane_action
    (used : Nat)
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (input : (OracleWorld + SigningSpec).Domain)
    (leftState : SourceExactTracedState)
    (firstLaneState : GlobalDirectTracedState)
    (trace : FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hstate : SourceFirstLaneExactGoodStateRelation left right leftState
      firstLaneState trace)
    (hcount : FirstLaneOracleSimulation.hazardCount trace ≤ used) :
    RelTriple
      ((cappedBothTracedMappedAdversaryImpl left.publicKey
        (Keygen.materializePrecomputation left.cache left.secretKey)
          input).run leftState)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl right.2)
        ((globalFirstLaneExactTracedMappedAdversaryImpl right.1
          input).run firstLaneState)).run)
      (fun leftResult firstLaneResult =>
        (leftResult.1 = firstLaneResult.1.1 ∧
          SourceFirstLaneExactGoodStateRelation left right leftResult.2
            firstLaneResult.1.2 (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤
            used + directHashActionCost input ∧
          leftResult.2.2.hashInputs.length =
            leftState.2.hashInputs.length + directHashActionCost input) ∨
        (FirstLaneOracleSimulation.CombinedHit right.2
            (trace ++ firstLaneResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ firstLaneResult.2) ≤
            used + directHashActionCost input)) := by
  let monitoredState := globalStateOfFirstLane firstLaneState trace
  have hsourceMonitored : GlobalSigningMonitoredTracedStateRelation left right
      (sourceExactSigningProjection leftState) monitoredState := hstate.1
  have hencodingTrace := hstate.2.1
  have hvalidLeafIndices := hstate.2.2
  have hsource :=
    relTriple_programmed_globalMonitored_sourceExact_action left right hrel
      hleftSupport hrightSupport leftState monitoredState hsourceMonitored input
  have hmonitored := relTriple_globalMonitored_firstLane_action
    right.1 right.2 input monitoredState
  apply relTriple_post_mono (relTriple_trans_exists hsource hmonitored)
  intro leftResult firstLaneResult hglued
  obtain ⟨monitoredResult, hsourceResult, hmonitoredResult⟩ := hglued
  obtain ⟨hprojection, hmonitoredSupport, hfirstLaneSupport⟩ := hmonitoredResult
  have hfragmentCount : FirstLaneOracleSimulation.hazardCount
      firstLaneResult.2 ≤ directHashActionCost input :=
    FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le
      right.2
      ((globalFirstLaneExactTracedMappedAdversaryImpl right.1
        input).run (GlobalDirectTracedState.mk monitoredState.1.causal
          monitoredState.2))
      (directHashActionCost input)
      (globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound right.1
        input (GlobalDirectTracedState.mk monitoredState.1.causal
          monitoredState.2))
      firstLaneResult hfirstLaneSupport
  have htotalCount : FirstLaneOracleSimulation.hazardCount
      (trace ++ firstLaneResult.2) ≤
        used + directHashActionCost input := by
    rw [FirstLaneOracleSimulation.hazardCount_append]
    omega
  have hmonitoredActionTrace :=
    globalMonitoredMappedAdversaryImpl_support_actionTrace_eq right
      input monitoredState monitoredResult hmonitoredSupport
  have hfirstLaneEncodingSub :=
    globalFirstLaneExactTracedMappedAdversaryImpl_query_trace_sublist
      right.2 right.1 input
        (GlobalDirectTracedState.mk monitoredState.1.causal monitoredState.2)
          leftState.1.2 firstLaneResult hfirstLaneSupport
  have hprojectionFacts :=
    GlobalFirstLaneProjectionFacts.of_projection trace monitoredResult
      firstLaneResult (by
        simpa [monitoredState, globalStateOfFirstLane] using hprojection)
  have hfragmentValid :=
    globalFirstLaneExactTracedMappedAdversary_validSignLeafIndices_sublist
      right.2 right.1 (liftM (OracleSpec.query input))
        (GlobalDirectTracedState.mk monitoredState.1.causal monitoredState.2)
          firstLaneResult
          (by simpa only [simulateQ_spec_query] using hfirstLaneSupport)
  have hnextValidLeafIndices : List.Sublist
      (CappedEncodingMonitor.validObservedSignLeafIndices
        (trace ++ firstLaneResult.2).encodingActions)
      (monitoredResult.2.2.toSigningLog.map fun entry => entry.1.epoch) := by
    rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append,
      CappedEncodingMonitor.validObservedSignLeafIndices_append,
      hprojectionFacts.attacker]
    exact (hvalidLeafIndices.append (List.Sublist.refl _)).trans hfragmentValid
  rcases hsourceResult with hgood | hbad
  · apply Or.inl
    refine ⟨hgood.1.trans ?_, ?_, htotalCount, ?_⟩
    · exact congrArg (fun result => result.1.1) hprojection
    · have hnextEncodingTrace : List.Sublist leftResult.2.1.2
          (trace ++ firstLaneResult.2).encodingActions := by
        rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append]
        rw [hgood.2.2, hprojectionFacts.output, hprojectionFacts.causal]
        exact hfirstLaneEncodingSub.trans
          (hencodingTrace.append (List.Sublist.refl _))
      refine ⟨?_, hnextEncodingTrace, ?_⟩
      · rw [hprojectionFacts.state]
        exact hgood.2.1
      · simpa [← hprojectionFacts.attacker] using hnextValidLeafIndices
    · have hinitialTrace : leftState.2 = monitoredState.2 := hsourceMonitored.2
      have hfinalTrace : leftResult.2.2 = monitoredResult.2.2 := hgood.2.1.2
      rw [hfinalTrace, hmonitoredActionTrace, ← hinitialTrace,
        AttackerActionTrace.hashInputs_append, List.length_append,
        attackerActionFragment_hashInputs_length]
  · apply Or.inr
    exact ⟨hprojectionFacts.combinedHit_of_bad right.2 hbad, htotalCount⟩

set_option maxRecDepth 1000000

theorem firstLane_eagerTrace_liftProbComp_then_bind
    (base : GlobalChainValueIndex → Digest)
    (keygen : ProbComp κ)
    (body : κ → OracleComp GlobalFirstLaneWorld α) :
    (do
      let keyResult ← keygen
      let execution ← (simulateQ
        (FirstLaneOracleSimulation.eagerTraceImpl base)
        (body keyResult)).run
      pure (base, ((keyResult, execution.1), execution.2))) = (do
      let result ← (simulateQ
        (FirstLaneOracleSimulation.eagerTraceImpl base) (do
          let keyResult ← FirstLaneOracleSimulation.liftProbComp keygen
          let execution ← body keyResult
          pure (keyResult, execution))).run
      pure (base, result)) := by
  simp only [simulateQ_bind, WriterT.run_bind', bind_assoc]
  rw [FirstLaneOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp [simulateQ_pure, WriterT.run_pure]

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

def liftGlobalChainTrace
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    FirstLaneOracleSimulation.ActionTrace GlobalChainValueIndex :=
  trace.map FirstLaneOracleSimulation.ObservedAction.chain

@[simp]
theorem liftGlobalChainTrace_chainActions
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    (liftGlobalChainTrace trace).chainActions = trace := by
  simp [liftGlobalChainTrace,
    FirstLaneOracleSimulation.ActionTrace.chainActions]

@[simp]
theorem liftGlobalChainTrace_hazardCount
    (trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    FirstLaneOracleSimulation.hazardCount (liftGlobalChainTrace trace) =
      RevealProbeOracleSimulation.observedProbeCount trace := by
  induction trace with
  | nil => simp [liftGlobalChainTrace,
      FirstLaneOracleSimulation.hazardCount,
      RevealProbeOracleSimulation.observedProbeCount]
  | cons action trace ih =>
      cases action with
      | probe index target =>
          simp only [liftGlobalChainTrace, List.map_cons,
            FirstLaneOracleSimulation.hazardCount,
            RevealProbeOracleSimulation.observedProbeCount,
            Nat.succ.injEq]
          change FirstLaneOracleSimulation.hazardCount
              (liftGlobalChainTrace trace) =
            RevealProbeOracleSimulation.observedProbeCount trace
          exact ih
      | reveal index value =>
          simp only [liftGlobalChainTrace, List.map_cons,
            FirstLaneOracleSimulation.hazardCount,
            RevealProbeOracleSimulation.observedProbeCount]
          change FirstLaneOracleSimulation.hazardCount
              (liftGlobalChainTrace trace) =
            RevealProbeOracleSimulation.observedProbeCount trace
          exact ih

end Xmss.Generic.CappedExecution

namespace Xmss.Generic

variable [Code]

end Xmss.Generic
