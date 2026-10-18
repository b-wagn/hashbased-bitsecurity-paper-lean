import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsEncodingActivity
import XmssSecurity.Proof.TargetSum.Direct.FirstLaneStepBudget
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Accumulate the public first-lane trace in a state counter. This exposes the
terminal query saving to the existing collision-probability bound. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.EUFCMA.Requests
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding FirstLaneOracleSimulation

theorem globalExactTracedLift_activity (table : Generic.CappedChain.GlobalChainValueIndex → Digest)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (input : (OracleWorld + Generic.SigningSpec).Domain)
    (base : StateT Generic.CappedChain.GlobalCausalHashState (OracleComp Generic.CappedChain.GlobalFirstLaneWorld)
      ((OracleWorld + Generic.SigningSpec).Range input)) (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : ((OracleWorld + Generic.SigningSpec).Range input × Generic.CappedChain.GlobalHighDirectTracedState) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalExactTracedLift key input base).run state)).run)) :
    traceActive key.secretKey.parameter result.1.2.attackerTrace =
      (traceActive key.secretKey.parameter state.attackerTrace || activity key.secretKey.parameter input) := by
  obtain ⟨handled, _, hresultEq⟩ := Generic.CappedChain.globalExactTracedLift_eager_support_decompose table key input base state result hresult
  rw [hresultEq, Generic.CappedChain.globalExactTracedNextState]
  exact traceActive_append_fragment _ _ _ _

theorem public_query_activity (table : Generic.CappedChain.GlobalChainValueIndex → Digest)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : ((OracleWorld + Generic.SigningSpec).Range input × Generic.CappedChain.GlobalHighDirectTracedState) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state)).run)) :
    traceActive key.secretKey.parameter result.1.2.attackerTrace =
      (traceActive key.secretKey.parameter state.attackerTrace || activity key.secretKey.parameter input) := by
  cases input with
  | inl input =>
      exact globalExactTracedLift_activity table key (.inl input)
        (StateT.mk (Generic.CappedChain.globalFirstLaneOracleExecution key edgeHigh input)) state result hresult
  | inr request =>
      exact globalExactTracedLift_activity table key (.inr request)
        (Generic.CappedChain.globalFirstLaneSigningImpl key request) state result hresult

theorem globalExactTracedLift_attackerTrace (table : Generic.CappedChain.GlobalChainValueIndex → Digest)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (input : (OracleWorld + Generic.SigningSpec).Domain)
    (base : StateT Generic.CappedChain.GlobalCausalHashState (OracleComp Generic.CappedChain.GlobalFirstLaneWorld)
      ((OracleWorld + Generic.SigningSpec).Range input)) (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : ((OracleWorld + Generic.SigningSpec).Range input × Generic.CappedChain.GlobalHighDirectTracedState) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalExactTracedLift key input base).run state)).run)) :
    result.1.2.attackerTrace = state.attackerTrace ++ Generic.CappedChain.attackerActionFragment input result.1.1 := by
  obtain ⟨handled, _, hresultEq⟩ := Generic.CappedChain.globalExactTracedLift_eager_support_decompose table key input base state result hresult
  rw [hresultEq, Generic.CappedChain.globalExactTracedNextState]

theorem public_query_attackerTrace (table : Generic.CappedChain.GlobalChainValueIndex → Digest)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (result : ((OracleWorld + Generic.SigningSpec).Range input × Generic.CappedChain.GlobalHighDirectTracedState) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state)).run)) :
    result.1.2.attackerTrace = state.attackerTrace ++ Generic.CappedChain.attackerActionFragment input result.1.1 := by
  cases input with
  | inl input =>
      exact globalExactTracedLift_attackerTrace table key (.inl input)
        (StateT.mk (Generic.CappedChain.globalFirstLaneOracleExecution key edgeHigh input)) state result hresult
  | inr request =>
      exact globalExactTracedLift_attackerTrace table key (.inr request)
        (Generic.CappedChain.globalFirstLaneSigningImpl key request) state result hresult

abbrev PublicTraceState := Generic.CappedChain.GlobalHighDirectTracedState × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex

noncomputable def publicTraceImpl (table : Generic.CappedChain.GlobalChainValueIndex → Digest)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) :
    QueryImpl (OracleWorld + Generic.SigningSpec) (StateT PublicTraceState ProbComp) := fun input =>
  StateT.mk fun state => (fun result => (result.1.1, (result.1.2, state.2 ++ result.2))) <$>
    (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state.1)).run

theorem publicTrace_run {α : Type} (table : Generic.CappedChain.GlobalChainValueIndex → Digest)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (state : Generic.CappedChain.GlobalHighDirectTracedState)
    (history : Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex) :
    (simulateQ (publicTraceImpl table key edgeHigh) computation).run (state, history) =
      (fun result => (result.1.1, (result.1.2, history ++ result.2))) <$>
        (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
          ((simulateQ (Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh) computation).run state)).run := by
  induction computation using OracleComp.inductionOn generalizing state history with
  | pure value => simp
  | query_bind input next ih =>
      rw [Generic.Direct.run_simulateQ_query_bind]
      simp only [publicTraceImpl, StateT.run_mk, bind_map_left, simulateQ_bind,
        simulateQ_spec_query, StateT.run_bind, WriterT.run_bind', map_bind]
      apply bind_congr
      rintro ⟨⟨answer, state'⟩, trace⟩
      rw [ih]
      simp only [Functor.map_map, List.append_assoc]
      congr 1

theorem publicTrace_activity_step (table : Generic.CappedChain.GlobalChainValueIndex → Digest)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (state : PublicTraceState)
    (result : (OracleWorld + Generic.SigningSpec).Range input × PublicTraceState)
    (hresult : result ∈ support ((publicTraceImpl table key edgeHigh input).run state)) :
    traceActive key.secretKey.parameter result.2.1.attackerTrace =
      (traceActive key.secretKey.parameter state.1.attackerTrace || activity key.secretKey.parameter input) := by
  simp only [publicTraceImpl, StateT.run_mk, support_map] at hresult
  obtain ⟨handled, hhandled, rfl⟩ := hresult
  exact public_query_activity table key edgeHigh input state.1 handled hhandled

theorem publicTrace_hazard_step (table : Generic.CappedChain.GlobalChainValueIndex → Digest)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (state : PublicTraceState)
    (result : (OracleWorld + Generic.SigningSpec).Range input × PublicTraceState)
    (hresult : result ∈ support ((publicTraceImpl table key edgeHigh input).run state)) :
    Generic.FirstLaneOracleSimulation.hazardCount result.2.2 ≤ Generic.FirstLaneOracleSimulation.hazardCount state.2 + if IsCharged input then 1 else 0 := by
  simp only [publicTraceImpl, StateT.run_mk, support_map] at hresult
  obtain ⟨handled, hhandled, rfl⟩ := hresult
  have h := Generic.FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le table _ (Generic.CappedChain.directHashActionCost input)
    (Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound key edgeHigh input state.1) handled hhandled
  simp only [Generic.FirstLaneOracleSimulation.hazardCount_append]
  apply Nat.add_le_add_left (h.trans ?_)
  rcases input with (sample | hashInput) | request <;> simp [Generic.CappedChain.directHashActionCost]

theorem public_stopped_hazards_le (adversary : Generic.Adversary) (q : ℕ) (hpositive : 0 < q)
    (hbound : IsQueryBound adversary q) (table : Generic.CappedChain.GlobalChainValueIndex → Digest)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (hparameter : key.publicKey.parameter = key.secretKey.parameter)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest)
    (result : (Generic.Forgery × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      (Generic.Deciding.publicPrefixExecution (stoppedAdversary q adversary) key edgeHigh)).run)) :
    Generic.FirstLaneOracleSimulation.hazardCount result.2 ≤ (q - 1) + if traceActive key.secretKey.parameter result.1.2.attackerTrace then 1 else 0 := by
  have hsupport : (result.1.1, (result.1.2, result.2)) ∈ support
      ((simulateQ (publicTraceImpl table key edgeHigh)
        ((stoppedAdversary q adversary).main key.publicKey)).run
        (Generic.CappedChain.GlobalHighDirectTracedState.initial (Generic.CappedChain.globalFilteredCausalKeygenState key), [])) := by
    rw [publicTrace_run, support_map]
    exact ⟨result, hresult, by simp⟩
  have h := stopInactive_counter_le_terminal (publicTraceImpl table key edgeHigh)
    (activity key.secretKey.parameter)
    (fun state : PublicTraceState => traceActive key.secretKey.parameter state.1.attackerTrace)
    (fun state : PublicTraceState => Generic.FirstLaneOracleSimulation.hazardCount state.2)
    (publicTrace_activity_step table key edgeHigh) (publicTrace_hazard_step table key edgeHigh)
    stoppedFallback (adversary.main key.publicKey) q
    (Generic.CappedChain.GlobalHighDirectTracedState.initial (Generic.CappedChain.globalFilteredCausalKeygenState key), []) hpositive (hbound key.publicKey)
    (result.1.1, (result.1.2, result.2))
    (by simpa only [stoppedAdversary, hparameter, Generic.CappedChain.GlobalHighDirectTracedState.initial,
      show traceActive key.secretKey.parameter [] = false from rfl] using hsupport)
  simpa only [Generic.FirstLaneOracleSimulation.hazardCount, Nat.zero_add] using h

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.public_stopped_hazards_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_stopped_hazards_le

theorem publicTrace_hazards_requests_step (table : Generic.CappedChain.GlobalChainValueIndex → Digest)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (state : PublicTraceState)
    (result : (OracleWorld + Generic.SigningSpec).Range input × PublicTraceState)
    (hresult : result ∈ support ((publicTraceImpl table key edgeHigh input).run state)) :
    Generic.FirstLaneOracleSimulation.hazardCount result.2.2 + result.2.1.attackerTrace.toSigningLog.length ≤
      (Generic.FirstLaneOracleSimulation.hazardCount state.2 + state.1.attackerTrace.toSigningLog.length) + if IsCharged input then 1 else 0 := by
  simp only [publicTraceImpl, StateT.run_mk, support_map] at hresult
  obtain ⟨handled, hhandled, rfl⟩ := hresult
  have h := Generic.FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le table _ (Generic.CappedChain.directHashActionCost input)
    (Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound key edgeHigh input state.1) handled hhandled
  simp only [Generic.FirstLaneOracleSimulation.hazardCount_append, public_query_attackerTrace table key edgeHigh input state.1 handled hhandled,
    Generic.CappedChain.AttackerActionTrace.toSigningLog_append, List.length_append, Generic.CappedChain.attackerActionFragment_toSigningLog]
  rcases input with (sample | hashInput) | request <;>
    simp only [Generic.CappedChain.directHashActionCost, Generic.signingLogFragment, List.length_nil, List.length_cons,
      charged_hash, charged_sign, not_charged_uniform, if_true, if_false, Nat.add_zero] at h ⊢ <;> omega

theorem public_stopped_hazards_le_encoding (adversary : Generic.Adversary) (q : ℕ) (hpositive : 0 < q)
    (hbound : IsQueryBound adversary q) (table : Generic.CappedChain.GlobalChainValueIndex → Digest)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (hparameter : key.publicKey.parameter = key.secretKey.parameter)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest)
    (result : (Generic.Forgery × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      (Generic.Deciding.publicPrefixExecution (stoppedAdversary q adversary) key edgeHigh)).run)) :
    Generic.FirstLaneOracleSimulation.hazardCount result.2 ≤ (q - 1) + if encodingActive key.secretKey.parameter result.1.2.attackerTrace then 1 else 0 := by
  by_cases hrequests : result.1.2.attackerTrace.toSigningLog.length = 0
  · have h := public_stopped_hazards_le adversary q hpositive hbound table key hparameter edgeHigh result hresult
    simpa only [traceActive, activityCount, hrequests, Nat.add_zero, encodingActive] using h
  · have hsupport : (result.1.1, (result.1.2, result.2)) ∈ support
        ((simulateQ (publicTraceImpl table key edgeHigh)
          ((stoppedAdversary q adversary).main key.publicKey)).run
          (Generic.CappedChain.GlobalHighDirectTracedState.initial (Generic.CappedChain.globalFilteredCausalKeygenState key), [])) := by
      rw [publicTrace_run, support_map]
      exact ⟨result, hresult, by simp⟩
    have h := stopInactive_support_budget (publicTraceImpl table key edgeHigh)
      (activity key.secretKey.parameter)
      (fun state : PublicTraceState => traceActive key.secretKey.parameter state.1.attackerTrace)
      (fun state : PublicTraceState => Generic.FirstLaneOracleSimulation.hazardCount state.2 + state.1.attackerTrace.toSigningLog.length)
      (publicTrace_activity_step table key edgeHigh) (publicTrace_hazards_requests_step table key edgeHigh)
      stoppedFallback (adversary.main key.publicKey) q
      (Generic.CappedChain.GlobalHighDirectTracedState.initial (Generic.CappedChain.globalFilteredCausalKeygenState key), []) (hbound key.publicKey)
      (result.1.1, (result.1.2, result.2))
      (by simpa only [stoppedAdversary, hparameter, Generic.CappedChain.GlobalHighDirectTracedState.initial,
        show traceActive key.secretKey.parameter [] = false from rfl] using hsupport)
    have htotal : Generic.FirstLaneOracleSimulation.hazardCount result.2 + result.1.2.attackerTrace.toSigningLog.length ≤ q := by
      simpa only [Generic.FirstLaneOracleSimulation.hazardCount, Generic.CappedChain.GlobalHighDirectTracedState.initial, Generic.CappedChain.GlobalHighDirectTracedState.attackerTrace,
        Generic.CappedChain.AttackerActionTrace.toSigningLog,
        List.filterMap_nil, List.length_nil, Nat.zero_add] using h.1
    split_ifs <;> omega

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.public_stopped_hazards_le_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_stopped_hazards_le_encoding

end XmssSecurity.TargetSum.EUFCMA.Requests
