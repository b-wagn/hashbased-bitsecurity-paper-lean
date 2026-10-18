import XmssSecurity.Proof.TargetSum.FirstLaneSampleLimit
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Public counters enforce the joint direct-query and fresh-encoding budget, even after
the source and ideal executions have diverged. An action is credited before its samples
are limited; the counters and observed prefix survive an abort. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.FirstLaneOracleSimulation

structure EncodingBudgetCounters where
  direct : Nat
  encoding : Nat
  samples : Nat

namespace EncodingBudgetCounters

def charge (counters : EncodingBudgetCounters) : Nat :=
  counters.direct + 2 * (counters.samples - counters.encoding)

def credit (counters : EncodingBudgetCounters) (direct encoding : Nat) : EncodingBudgetCounters :=
  ⟨counters.direct + direct, counters.encoding + encoding, counters.samples⟩

def addSamples (counters : EncodingBudgetCounters) (samples : Nat) : EncodingBudgetCounters :=
  { counters with samples := counters.samples + samples }

def sampleFuel (counters : EncodingBudgetCounters) (limit : Nat) : Nat :=
  counters.encoding + (limit - counters.direct) / 2 - counters.samples

theorem charge_le_iff (counters : EncodingBudgetCounters) (limit : Nat) :
    counters.charge ≤ limit ↔ counters.direct ≤ limit ∧
      counters.samples ≤ counters.encoding + (limit - counters.direct) / 2 := by
  unfold charge
  omega

theorem addSamples_charge_mono (counters : EncodingBudgetCounters) (samples : Nat) :
    counters.charge ≤ (counters.addSamples samples).charge := by
  simp only [charge, addSamples]
  omega

theorem addSamples_charge_le_iff (counters : EncodingBudgetCounters) (limit samples : Nat)
    (hbudget : counters.charge ≤ limit) :
    (counters.addSamples samples).charge ≤ limit ↔ samples ≤ counters.sampleFuel limit := by
  rw [charge_le_iff] at hbudget ⊢
  simp only [addSamples, sampleFuel]
  omega

end EncodingBudgetCounters

variable {Index : Type} {α : Type}

noncomputable def limitEncodingAction (limit direct encoding : Nat)
    (counters : EncodingBudgetCounters) (computation : OracleComp (FirstLaneOracleSimulation.World Index) α) :
    OracleComp (FirstLaneOracleSimulation.World Index) (Option α × EncodingBudgetCounters) :=
  let credited := counters.credit direct encoding
  if credited.charge ≤ limit then
    (fun result => (result.1, credited.addSamples (credited.sampleFuel limit - result.2))) <$>
      limitEncodingSamples (credited.sampleFuel limit) computation
  else pure (none, counters)

theorem simulate_limitEncodingAction_eq (table : Index → Digest) (limit direct encoding : Nat)
    (counters : EncodingBudgetCounters) (computation : OracleComp (FirstLaneOracleSimulation.World Index) α)
    (hbound : ∀ result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) computation).run,
      ((counters.credit direct encoding).addSamples result.2.encodingActions.length).charge ≤ limit) :
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) (limitEncodingAction limit direct encoding counters computation)).run =
      (fun result => ((some result.1,
        (counters.credit direct encoding).addSamples result.2.encodingActions.length), result.2)) <$>
          (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) computation).run := by
  let credited := counters.credit direct encoding
  have hbudget : credited.charge ≤ limit := by
    obtain ⟨result, hresult⟩ := probComp_support_nonempty (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) computation).run
    exact (credited.addSamples_charge_mono result.2.encodingActions.length).trans (hbound result hresult)
  have hfuel (result) (hresult : result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) computation).run) :
      result.2.encodingActions.length ≤ credited.sampleFuel limit :=
    (credited.addSamples_charge_le_iff limit result.2.encodingActions.length hbudget).1 (hbound result hresult)
  rw [limitEncodingAction, if_pos hbudget, simulateQ_map, WriterT.run_map,
    simulate_limitEncodingSamples_eq table _ computation hfuel, Functor.map_map]
  simp only [map_eq_bind_pure_comp]
  refine bind_congr_of_forall_mem_support _ fun result hresult => ?_
  have h := hfuel result hresult
  have hcount : credited.sampleFuel limit - (credited.sampleFuel limit - result.2.encodingActions.length) =
      result.2.encodingActions.length := by omega
  change pure ((some result.1, credited.addSamples _), result.2) = _
  rw [hcount]
  rfl

theorem limitEncodingAction_trace_budget (table : Index → Digest) (limit direct encoding : Nat)
    (counters : EncodingBudgetCounters) (computation : OracleComp (FirstLaneOracleSimulation.World Index) α)
    (hbudget : counters.charge ≤ limit)
    (result : (Option α × EncodingBudgetCounters) × FirstLaneOracleSimulation.ActionTrace Index)
    (hresult : result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (limitEncodingAction limit direct encoding counters computation)).run) :
    result.1.2.charge ≤ limit ∧
      result.1.2.samples = counters.samples + result.2.encodingActions.length := by
  let credited := counters.credit direct encoding
  by_cases hcredit : credited.charge ≤ limit
  · rw [limitEncodingAction, if_pos hcredit, simulateQ_map, WriterT.run_map, support_map] at hresult
    obtain ⟨limited, hlimited, rfl⟩ := hresult
    have hcount := limitEncodingSamples_trace_budget table (credited.sampleFuel limit) computation limited hlimited
    have hremaining : credited.sampleFuel limit - limited.1.2 = limited.2.encodingActions.length := by omega
    change (credited.addSamples (credited.sampleFuel limit - limited.1.2)).charge ≤ limit ∧
      (credited.addSamples (credited.sampleFuel limit - limited.1.2)).samples =
        counters.samples + limited.2.encodingActions.length
    rw [hremaining]
    constructor
    · exact (credited.addSamples_charge_le_iff limit _ hcredit).2 (by omega)
    · rfl
  · rw [limitEncodingAction, if_neg hcredit] at hresult
    simp only [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact ⟨hbudget, by simp [FirstLaneOracleSimulation.ActionTrace.encodingActions]⟩

theorem limitEncodingAction_trace_direct (table : Index → Digest) (limit direct encoding : Nat)
    (counters : EncodingBudgetCounters) (computation : OracleComp (FirstLaneOracleSimulation.World Index) α)
    (hbound : computation.IsQueryBoundP FirstLaneOracleSimulation.IsHazardQuery direct)
    (result : (Option α × EncodingBudgetCounters) × FirstLaneOracleSimulation.ActionTrace Index)
    (hresult : result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (limitEncodingAction limit direct encoding counters computation)).run) :
    counters.direct + FirstLaneOracleSimulation.hazardCount result.2 ≤ result.1.2.direct := by
  let credited := counters.credit direct encoding
  by_cases hcredit : credited.charge ≤ limit
  · rw [limitEncodingAction, if_pos hcredit, simulateQ_map, WriterT.run_map, support_map] at hresult
    obtain ⟨limited, hlimited, rfl⟩ := hresult
    have hqueryBound := QueryLimiting.limit_preserves_queryBound IsEncodingSample FirstLaneOracleSimulation.IsHazardQuery
      (credited.sampleFuel limit) direct computation hbound
    have hcount := FirstLaneOracleSimulation.simulate_eagerTrace_support_hazardCount_le table
      (limitEncodingSamples (credited.sampleFuel limit) computation) direct hqueryBound limited hlimited
    change counters.direct + FirstLaneOracleSimulation.hazardCount limited.2 ≤ counters.direct + direct
    omega
  · rw [limitEncodingAction, if_neg hcredit] at hresult
    simp only [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    simp [FirstLaneOracleSimulation.hazardCount]

theorem limitEncodingAction_success_support (table : Index → Digest) (limit direct encoding : Nat)
    (counters : EncodingBudgetCounters) (computation : OracleComp (FirstLaneOracleSimulation.World Index) α)
    (result : (Option α × EncodingBudgetCounters) × FirstLaneOracleSimulation.ActionTrace Index) (value : α)
    (hresult : result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (limitEncodingAction limit direct encoding counters computation)).run)
    (hvalue : result.1.1 = some value) :
    (value, result.2) ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) computation).run := by
  let credited := counters.credit direct encoding
  by_cases hcredit : credited.charge ≤ limit
  · rw [limitEncodingAction, if_pos hcredit, simulateQ_map, WriterT.run_map, support_map] at hresult
    obtain ⟨limited, hlimited, rfl⟩ := hresult
    exact QueryLimiting.limit_success_support IsEncodingSample (FirstLaneOracleSimulation.eagerTraceImpl table)
      (credited.sampleFuel limit) computation limited value hlimited hvalue
  · rw [limitEncodingAction, if_neg hcredit] at hresult
    simp only [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    cases hvalue

/-- info: 'XmssSecurity.TargetSum.FirstLaneOracleSimulation.simulate_limitEncodingAction_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simulate_limitEncodingAction_eq

/-- info: 'XmssSecurity.TargetSum.FirstLaneOracleSimulation.limitEncodingAction_trace_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitEncodingAction_trace_budget

end XmssSecurity.TargetSum.FirstLaneOracleSimulation
