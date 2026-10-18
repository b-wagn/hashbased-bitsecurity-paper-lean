import XmssSecurity.Proof.TargetSum.EncodingMonitorExpectedRisk
import XmssSecurity.Proof.Generic.FirstLaneEagerBound
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Bound the encoding component of the first lane by its actual expected query count. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.CappedEncodingMonitor

inductive RiskState where
  | active (state : Generic.EncodingMonitor.State)
  | disabled
  | hit

noncomputable def RiskState.resource : RiskState → ℝ≥0∞
  | .active state => Generic.CappedEncodingMonitor.State.pendingRisk state
  | .disabled => 0
  | .hit => 1

noncomputable def RiskState.step : RiskState → Generic.EncodingMonitor.ObservedAction → RiskState
  | .active state, action => match Generic.CappedEncodingMonitor.State.applyObserved state action with
      | none => .disabled
      | some (next, wasHit) => if wasHit then .hit else .active next
  | .disabled, _ => .disabled
  | .hit, _ => .hit

noncomputable def RiskState.run (state : RiskState) (actions : Generic.EncodingActionTrace) : RiskState :=
  actions.foldl RiskState.step state

theorem RiskState.resource_step_active (state : Generic.EncodingMonitor.State)
    (action : Generic.EncodingMonitor.ObservedAction) :
    ((RiskState.active state).step action).resource = observedRisk (Generic.CappedEncodingMonitor.State.applyObserved state action) := by
  cases hstep : Generic.CappedEncodingMonitor.State.applyObserved state action with
  | none => simp [RiskState.step, hstep, RiskState.resource, observedRisk]
  | some pair =>
      rcases pair with ⟨next, wasHit⟩
      cases wasHit <;> simp [RiskState.step, hstep, RiskState.resource, observedRisk]

theorem RiskState.expected_step_query_le (state : RiskState) (leafIndex : LeafIndex) :
    (∑' output, Pr[= output | $ᵗ HashOutput] * (state.step (.query leafIndex output)).resource) ≤
      state.resource + ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ := by
  cases state with
  | active state =>
      simp_rw [RiskState.resource_step_active]
      exact expected_observedRisk_query_le state leafIndex
  | disabled => simp [RiskState.step, RiskState.resource]
  | hit =>
      simp only [RiskState.step, RiskState.resource, mul_one]
      exact le_add_right tsum_probOutput_le_one

theorem RiskState.expected_step_sign_le (state : RiskState) (leafIndex : LeafIndex) :
    (∑' output, Pr[= output | $ᵗ HashOutput] * (state.step (.sign leafIndex output)).resource) ≤
      state.resource := by
  cases state with
  | active state =>
      simp_rw [RiskState.resource_step_active]
      exact expected_observedRisk_sign_le state leafIndex
  | disabled => simp [RiskState.step, RiskState.resource]
  | hit => simpa only [RiskState.step, RiskState.resource, mul_one] using
      (tsum_probOutput_le_one (mx := ($ᵗ HashOutput)))

@[simp] theorem RiskState.run_disabled (actions : Generic.EncodingActionTrace) :
    RiskState.run .disabled actions = .disabled := by
  induction actions with
  | nil => rfl
  | cons action actions ih => exact ih

@[simp] theorem RiskState.run_hit (actions : Generic.EncodingActionTrace) :
    RiskState.run .hit actions = .hit := by
  induction actions with
  | nil => rfl
  | cons action actions ih => exact ih

theorem RiskState.run_active_hit_iff (state : Generic.EncodingMonitor.State) (actions : Generic.EncodingActionTrace) :
    RiskState.run (.active state) actions = .hit ↔ Generic.CappedEncodingMonitor.runObserved state actions = true := by
  induction actions generalizing state with
  | nil => simp [RiskState.run, Generic.CappedEncodingMonitor.runObserved]
  | cons action actions ih =>
      change RiskState.run ((RiskState.active state).step action) actions = .hit ↔ _
      rw [Generic.CappedEncodingMonitor.runObserved]
      cases hstep : Generic.CappedEncodingMonitor.State.applyObserved state action with
      | none => simp [RiskState.step, hstep]
      | some pair =>
          cases hhit : pair.2 <;> simp [RiskState.step, hstep, hhit, ih]

end XmssSecurity.TargetSum.CappedEncodingMonitor

namespace XmssSecurity.TargetSum.FirstLaneOracleSimulation

open CappedEncodingMonitor

variable {Index : Type} [Fintype Index] [DecidableEq Index]

def IsEncodingQuery : (Generic.FirstLaneOracleSimulation.World Index).Domain → Prop
  | .encodingQuery _ => True
  | _ => False

noncomputable instance : DecidablePred (IsEncodingQuery (Index := Index)) := Classical.decPred _

noncomputable def encodingRiskStep (state : RiskState) (input : (Generic.FirstLaneOracleSimulation.World Index).Domain)
    (output : (Generic.FirstLaneOracleSimulation.World Index).Range input) : RiskState :=
  match input with
  | .encodingQuery leafIndex => state.step (.query leafIndex output)
  | .encodingSignAttempt leafIndex => state.step (.sign leafIndex output)
  | _ => state

noncomputable def encodingRiskImpl (table : Index → Digest) :
    QueryImpl (Generic.FirstLaneOracleSimulation.World Index) (StateT RiskState ProbComp) := fun input state =>
  (fun output => (output, encodingRiskStep state input output)) <$> Generic.FirstLaneOracleSimulation.eagerImpl table input

noncomputable def eagerUnitImpl (table : Index → Digest) :
    QueryImpl (Generic.FirstLaneOracleSimulation.World Index) (StateT Unit ProbComp) := fun input _ =>
  (fun output => (output, ())) <$> Generic.FirstLaneOracleSimulation.eagerImpl table input

omit [Fintype Index] [DecidableEq Index] in
theorem encodingRiskImpl_expected_step (table : Index → Digest)
    (input : (Generic.FirstLaneOracleSimulation.World Index).Domain) (state : RiskState) :
    (∑' result, Pr[= result | (encodingRiskImpl table input).run state] * result.2.resource) ≤
      state.resource + if IsEncodingQuery input then ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  change (∑' result, Pr[= result |
    (fun output => (output, encodingRiskStep state input output)) <$> Generic.FirstLaneOracleSimulation.eagerImpl table input] *
      result.2.resource) ≤ _
  rw [tsum_probOutput_map_mul]
  cases input with
  | encodingQuery leafIndex =>
      simpa only [encodingRiskStep, Generic.FirstLaneOracleSimulation.eagerImpl, Generic.uniformHashOutput, IsEncodingQuery, if_true] using
        RiskState.expected_step_query_le state leafIndex
  | encodingSignAttempt leafIndex =>
      simpa only [encodingRiskStep, Generic.FirstLaneOracleSimulation.eagerImpl, Generic.uniformHashOutput, IsEncodingQuery, if_false, add_zero]
        using RiskState.expected_step_sign_le state leafIndex
  | uniform n =>
      simp only [encodingRiskStep, IsEncodingQuery, if_false, add_zero]
      rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one le_rfl).trans_eq (one_mul _)
  | probe index target => simp [encodingRiskStep, Generic.FirstLaneOracleSimulation.eagerImpl, IsEncodingQuery]
  | reveal index => simp [encodingRiskStep, Generic.FirstLaneOracleSimulation.eagerImpl, IsEncodingQuery]

omit [Fintype Index] [DecidableEq Index] in
theorem expected_encodingRiskImpl_eq_eager (table : Index → Digest)
    (predicate : (Generic.FirstLaneOracleSimulation.World Index).Domain → Prop) [DecidablePred predicate]
    (computation : OracleComp (Generic.FirstLaneOracleSimulation.World Index) α) (state : RiskState) :
    expectedSimulatedQueryCount (encodingRiskImpl table) predicate computation state =
      expectedSimulatedQueryCount (eagerUnitImpl table) predicate computation () := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind input next ih =>
      rw [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_query_bind]
      congr 1
      change (∑' result, Pr[= result |
        (fun output => (output, encodingRiskStep state input output)) <$> Generic.FirstLaneOracleSimulation.eagerImpl table input] * _) =
        ∑' result, Pr[= result | (fun output => (output, ())) <$> Generic.FirstLaneOracleSimulation.eagerImpl table input] * _
      rw [tsum_probOutput_map_mul, tsum_probOutput_map_mul]
      simp_rw [ih]

omit [Fintype Index] in
theorem encodingRisk_hit_probability_le_expected (table : Index → Digest)
    (computation : OracleComp (Generic.FirstLaneOracleSimulation.World Index) α) :
    Pr[fun result => result.2 = RiskState.hit |
      (simulateQ (encodingRiskImpl table) computation).run (.active Generic.EncodingMonitor.State.empty)] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        expectedSimulatedQueryCount (eagerUnitImpl table) IsEncodingQuery computation () := by
  classical
  have hresource := expectedResource_le_initial_add_rate_mul_expectedQueryCount
    (encodingRiskImpl table) IsEncodingQuery RiskState.resource
    ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ (encodingRiskImpl_expected_step table)
    computation (.active Generic.EncodingMonitor.State.empty)
  simp only [RiskState.resource, Generic.CappedEncodingMonitor.State.pendingRisk_empty, zero_add,
    expected_encodingRiskImpl_eq_eager] at hresource
  apply le_trans _ hresource
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  cases result.2 <;> simp

omit [Fintype Index] [DecidableEq Index] in
theorem encodingRisk_run_eq_trace (table : Index → Digest)
    (computation : OracleComp (Generic.FirstLaneOracleSimulation.World Index) α) (state : RiskState) :
    (simulateQ (encodingRiskImpl table) computation).run state =
      (fun result => (result.1, RiskState.run state result.2.encodingActions)) <$>
        (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table) computation).run := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp [simulateQ_pure, RiskState.run, Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions]
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, Generic.FirstLaneOracleSimulation.eagerTrace_query_bind_run]
      change ((fun output => (output, encodingRiskStep state input output)) <$> Generic.FirstLaneOracleSimulation.eagerImpl table input >>=
          fun result => (simulateQ (encodingRiskImpl table) (next result.1)).run result.2) = _
      simp only [bind_map_left, map_bind, map_pure, ih]
      apply bind_congr
      intro output
      congr 1
      funext result
      congr 1
      cases input <;> simp [RiskState.run, Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions, Generic.FirstLaneOracleSimulation.traceFragment, encodingRiskStep]

omit [Fintype Index] in
/-- Encoding collisions in the existing first-lane trace are paid by actual expected
encoding queries. Signer attempts carry no additional first-lane collision charge. -/
theorem encodingFirstLane_probability_le_expected (table : Index → Digest)
    (computation : OracleComp (Generic.FirstLaneOracleSimulation.World Index) α) :
    Pr[fun result => Generic.CappedEncodingMonitor.runObserved Generic.EncodingMonitor.State.empty
        result.2.encodingActions = true | (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table) computation).run] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
        expectedSimulatedQueryCount (eagerUnitImpl table) IsEncodingQuery computation () := by
  have h := encodingRisk_hit_probability_le_expected table computation
  rw [encodingRisk_run_eq_trace, probEvent_map] at h
  change Pr[fun result => RiskState.run (.active Generic.EncodingMonitor.State.empty)
    result.2.encodingActions = .hit | (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table) computation).run] ≤ _ at h
  simpa only [RiskState.run_active_hit_iff] using h

noncomputable def expectedEagerQueryCount (predicate : (Generic.FirstLaneOracleSimulation.World Index).Domain → Prop)
    [DecidablePred predicate] (computation : OracleComp (Generic.FirstLaneOracleSimulation.World Index) α) : ℝ≥0∞ :=
  ∑' table, Pr[= table | Generic.RevealProbeOracleSimulation.eagerTableSample] *
    expectedSimulatedQueryCount (eagerUnitImpl table) predicate computation ()

theorem encodingFirstLane_eager_probability_le_expected
    (computation : OracleComp (Generic.FirstLaneOracleSimulation.World Index) α) :
    Pr[fun result => Generic.CappedEncodingMonitor.runObserved Generic.EncodingMonitor.State.empty
        result.2.2.encodingActions = true | Generic.FirstLaneOracleSimulation.eagerExperiment computation] ≤
      ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ * expectedEagerQueryCount IsEncodingQuery computation := by
  simp only [Generic.FirstLaneOracleSimulation.eagerExperiment, bind_pure_comp, probEvent_bind_eq_tsum, probEvent_map,
    Function.comp_def]
  calc
    _ ≤ ∑' table, Pr[= table | Generic.RevealProbeOracleSimulation.eagerTableSample] *
        (((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ *
          expectedSimulatedQueryCount (eagerUnitImpl table) IsEncodingQuery computation ()) := by
      apply ENNReal.tsum_le_tsum
      intro table
      exact mul_le_mul' le_rfl (encodingFirstLane_probability_le_expected table computation)
    _ = _ := by
      simp_rw [mul_left_comm (Pr[= _ | _]) (((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹)]
      rw [ENNReal.tsum_mul_left]
      rfl

/-- info: 'XmssSecurity.TargetSum.FirstLaneOracleSimulation.encodingFirstLane_probability_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encodingFirstLane_probability_le_expected

/-- info: 'XmssSecurity.TargetSum.FirstLaneOracleSimulation.encodingFirstLane_eager_probability_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms encodingFirstLane_eager_probability_le_expected

end XmssSecurity.TargetSum.FirstLaneOracleSimulation
