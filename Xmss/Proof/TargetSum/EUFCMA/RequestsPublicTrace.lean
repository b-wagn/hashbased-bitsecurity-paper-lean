import Xmss.Proof.TargetSum.EUFCMA.RequestsEncodingActivity
import Xmss.Proof.TargetSum.Direct.FirstLaneStepBudget
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Accumulate the public first-lane trace in a state counter. This exposes the
terminal query saving to the existing collision-probability bound. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.EUFCMA.Requests
open Xmss.EUFCMA

open Hashing Wots Merkle Verify Keygen Signing CappedExecution Deciding FirstLaneOracleSimulation

theorem globalExactTracedLift_activity (table : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT CappedExecution.GlobalCausalHashState (OracleComp CappedExecution.GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input)) (state : CappedExecution.GlobalDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedExecution.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedExecution.globalExactTracedLift key input base).run state)).run)) :
    traceActive key.secretKey.parameter result.1.2.attackerTrace =
      (traceActive key.secretKey.parameter state.attackerTrace || activity key.secretKey.parameter input) := by
  obtain ⟨handled, _, hresultEq⟩ := CappedExecution.globalExactTracedLift_eager_support_decompose table key input base state result hresult
  rw [hresultEq, CappedExecution.globalExactTracedNextState]
  exact traceActive_append_fragment _ _ _ _

theorem public_query_activity (table : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain) (state : CappedExecution.GlobalDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedExecution.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl key input).run state)).run)) :
    traceActive key.secretKey.parameter result.1.2.attackerTrace =
      (traceActive key.secretKey.parameter state.attackerTrace || activity key.secretKey.parameter input) := by
  cases input with
  | inl input =>
      exact globalExactTracedLift_activity table key (.inl input)
        (StateT.mk (CappedExecution.globalFirstLaneOracleExecution key input)) state result hresult
  | inr request =>
      exact globalExactTracedLift_activity table key (.inr request)
        (CappedExecution.globalFirstLaneSigningImpl key request) state result hresult

theorem globalExactTracedLift_attackerTrace (table : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (input : (OracleWorld + SigningSpec).Domain)
    (base : StateT CappedExecution.GlobalCausalHashState (OracleComp CappedExecution.GlobalFirstLaneWorld)
      ((OracleWorld + SigningSpec).Range input)) (state : CappedExecution.GlobalDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedExecution.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedExecution.globalExactTracedLift key input base).run state)).run)) :
    result.1.2.attackerTrace = state.attackerTrace ++ CappedExecution.attackerActionFragment input result.1.1 := by
  obtain ⟨handled, _, hresultEq⟩ := CappedExecution.globalExactTracedLift_eager_support_decompose table key input base state result hresult
  rw [hresultEq, CappedExecution.globalExactTracedNextState]

theorem public_query_attackerTrace (table : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain) (state : CappedExecution.GlobalDirectTracedState)
    (result : ((OracleWorld + SigningSpec).Range input × CappedExecution.GlobalDirectTracedState) ×
      FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl key input).run state)).run)) :
    result.1.2.attackerTrace = state.attackerTrace ++ CappedExecution.attackerActionFragment input result.1.1 := by
  cases input with
  | inl input =>
      exact globalExactTracedLift_attackerTrace table key (.inl input)
        (StateT.mk (CappedExecution.globalFirstLaneOracleExecution key input)) state result hresult
  | inr request =>
      exact globalExactTracedLift_attackerTrace table key (.inr request)
        (CappedExecution.globalFirstLaneSigningImpl key request) state result hresult

abbrev PublicTraceState := CappedExecution.GlobalDirectTracedState × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex

noncomputable def publicTraceImpl (table : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) :
    QueryImpl (OracleWorld + SigningSpec) (StateT PublicTraceState ProbComp) := fun input =>
  StateT.mk fun state => (fun result => (result.1.1, (result.1.2, state.2 ++ result.2))) <$>
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl key input).run state.1)).run

theorem publicTrace_run {α : Type} (table : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CappedExecution.GlobalDirectTracedState)
    (history : FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex) :
    (simulateQ (publicTraceImpl table key) computation).run (state, history) =
      (fun result => (result.1.1, (result.1.2, history ++ result.2))) <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((simulateQ (CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl key) computation).run state)).run := by
  induction computation using OracleComp.inductionOn generalizing state history with
  | pure value => simp
  | query_bind input next ih =>
      rw [Direct.run_simulateQ_query_bind]
      simp only [publicTraceImpl, StateT.run_mk, bind_map_left, simulateQ_bind,
        simulateQ_spec_query, StateT.run_bind, WriterT.run_bind', map_bind]
      apply bind_congr
      rintro ⟨⟨answer, state'⟩, trace⟩
      rw [ih]
      simp only [Functor.map_map, List.append_assoc]
      congr 1

theorem publicTrace_activity_step (table : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain) (state : PublicTraceState)
    (result : (OracleWorld + SigningSpec).Range input × PublicTraceState)
    (hresult : result ∈ support ((publicTraceImpl table key input).run state)) :
    traceActive key.secretKey.parameter result.2.1.attackerTrace =
      (traceActive key.secretKey.parameter state.1.attackerTrace || activity key.secretKey.parameter input) := by
  simp only [publicTraceImpl, StateT.run_mk, support_map] at hresult
  obtain ⟨handled, hhandled, rfl⟩ := hresult
  exact public_query_activity table key input state.1 handled hhandled

theorem publicTrace_hazard_step (table : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain) (state : PublicTraceState)
    (result : (OracleWorld + SigningSpec).Range input × PublicTraceState)
    (hresult : result ∈ support ((publicTraceImpl table key input).run state)) :
    FirstLaneOracleSimulation.hazardCount result.2.2 ≤ FirstLaneOracleSimulation.hazardCount state.2 + if IsCharged input then 1 else 0 := by
  simp only [publicTraceImpl, StateT.run_mk, support_map] at hresult
  obtain ⟨handled, hhandled, rfl⟩ := hresult
  have h := FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le table _ (CappedExecution.directHashActionCost input)
    (CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound key input state.1) handled hhandled
  simp only [FirstLaneOracleSimulation.hazardCount_append]
  apply Nat.add_le_add_left (h.trans ?_)
  rcases input with (sample | hashInput) | request <;> simp [CappedExecution.directHashActionCost]

theorem public_stopped_hazards_le (adversary : Adversary) (q : ℕ) (hpositive : 0 < q)
    (hbound : IsQueryBound adversary q) (table : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (hparameter : key.publicKey.parameter = key.secretKey.parameter)
    (result : (Forgery × CappedExecution.GlobalDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (Deciding.publicPrefixExecution (stoppedAdversary q adversary) key)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ (q - 1) + if traceActive key.secretKey.parameter result.1.2.attackerTrace then 1 else 0 := by
  have hsupport : (result.1.1, (result.1.2, result.2)) ∈ support
      ((simulateQ (publicTraceImpl table key)
        ((stoppedAdversary q adversary).main key.publicKey)).run
        (CappedExecution.GlobalDirectTracedState.initial (CappedExecution.globalFilteredCausalKeygenState key), [])) := by
    rw [publicTrace_run, support_map]
    exact ⟨result, hresult, by simp⟩
  have h := stopInactive_counter_le_terminal (publicTraceImpl table key)
    (activity key.secretKey.parameter)
    (fun state : PublicTraceState => traceActive key.secretKey.parameter state.1.attackerTrace)
    (fun state : PublicTraceState => FirstLaneOracleSimulation.hazardCount state.2)
    (publicTrace_activity_step table key) (publicTrace_hazard_step table key)
    stoppedFallback (adversary.main key.publicKey) q
    (CappedExecution.GlobalDirectTracedState.initial (CappedExecution.globalFilteredCausalKeygenState key), []) hpositive (hbound key.publicKey)
    (result.1.1, (result.1.2, result.2))
    (by simpa only [stoppedAdversary, hparameter, CappedExecution.GlobalDirectTracedState.initial,
      show traceActive key.secretKey.parameter [] = false from rfl] using hsupport)
  simpa only [FirstLaneOracleSimulation.hazardCount, Nat.zero_add] using h

/-- info: 'Xmss.TargetSum.EUFCMA.Requests.public_stopped_hazards_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_stopped_hazards_le

theorem publicTrace_hazards_requests_step (table : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain) (state : PublicTraceState)
    (result : (OracleWorld + SigningSpec).Range input × PublicTraceState)
    (hresult : result ∈ support ((publicTraceImpl table key input).run state)) :
    FirstLaneOracleSimulation.hazardCount result.2.2 + result.2.1.attackerTrace.toSigningLog.length ≤
      (FirstLaneOracleSimulation.hazardCount state.2 + state.1.attackerTrace.toSigningLog.length) + if IsCharged input then 1 else 0 := by
  simp only [publicTraceImpl, StateT.run_mk, support_map] at hresult
  obtain ⟨handled, hhandled, rfl⟩ := hresult
  have h := FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le table _ (CappedExecution.directHashActionCost input)
    (CappedExecution.globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound key input state.1) handled hhandled
  simp only [FirstLaneOracleSimulation.hazardCount_append, public_query_attackerTrace table key input state.1 handled hhandled,
    CappedExecution.AttackerActionTrace.toSigningLog_append, List.length_append, CappedExecution.attackerActionFragment_toSigningLog]
  rcases input with (sample | hashInput) | request <;>
    simp only [CappedExecution.directHashActionCost, signingLogFragment, List.length_nil, List.length_cons,
      charged_hash, charged_sign, not_charged_uniform, if_true, if_false, Nat.add_zero] at h ⊢ <;> omega

theorem public_stopped_hazards_le_encoding (adversary : Adversary) (q : ℕ) (hpositive : 0 < q)
    (hbound : IsQueryBound adversary q) (table : CappedExecution.GlobalChainValueIndex → Digest)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (hparameter : key.publicKey.parameter = key.secretKey.parameter)
    (result : (Forgery × CappedExecution.GlobalDirectTracedState) × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (Deciding.publicPrefixExecution (stoppedAdversary q adversary) key)).run)) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ (q - 1) + if encodingActive key.secretKey.parameter result.1.2.attackerTrace then 1 else 0 := by
  by_cases hrequests : result.1.2.attackerTrace.toSigningLog.length = 0
  · have h := public_stopped_hazards_le adversary q hpositive hbound table key hparameter result hresult
    simpa only [traceActive, activityCount, hrequests, Nat.add_zero, encodingActive] using h
  · have hsupport : (result.1.1, (result.1.2, result.2)) ∈ support
        ((simulateQ (publicTraceImpl table key)
          ((stoppedAdversary q adversary).main key.publicKey)).run
          (CappedExecution.GlobalDirectTracedState.initial (CappedExecution.globalFilteredCausalKeygenState key), [])) := by
      rw [publicTrace_run, support_map]
      exact ⟨result, hresult, by simp⟩
    have h := stopInactive_support_budget (publicTraceImpl table key)
      (activity key.secretKey.parameter)
      (fun state : PublicTraceState => traceActive key.secretKey.parameter state.1.attackerTrace)
      (fun state : PublicTraceState => FirstLaneOracleSimulation.hazardCount state.2 + state.1.attackerTrace.toSigningLog.length)
      (publicTrace_activity_step table key) (publicTrace_hazards_requests_step table key)
      stoppedFallback (adversary.main key.publicKey) q
      (CappedExecution.GlobalDirectTracedState.initial (CappedExecution.globalFilteredCausalKeygenState key), []) (hbound key.publicKey)
      (result.1.1, (result.1.2, result.2))
      (by simpa only [stoppedAdversary, hparameter, CappedExecution.GlobalDirectTracedState.initial,
        show traceActive key.secretKey.parameter [] = false from rfl] using hsupport)
    have htotal : FirstLaneOracleSimulation.hazardCount result.2 + result.1.2.attackerTrace.toSigningLog.length ≤ q := by
      simpa only [FirstLaneOracleSimulation.hazardCount, CappedExecution.GlobalDirectTracedState.initial, CappedExecution.GlobalDirectTracedState.attackerTrace,
        CappedExecution.AttackerActionTrace.toSigningLog,
        List.filterMap_nil, List.length_nil, Nat.zero_add] using h.1
    split_ifs <;> omega

/-- info: 'Xmss.TargetSum.EUFCMA.Requests.public_stopped_hazards_le_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_stopped_hazards_le_encoding

end Xmss.TargetSum.EUFCMA.Requests
