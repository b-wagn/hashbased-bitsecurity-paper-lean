import XmssSecurity.Proof.FirstLaneSampleLimit

/-! Public counters enforce the joint direct-query and fresh-encoding budget, even after
the source and ideal executions have diverged. An action is credited before its samples
are limited; the counters and observed prefix survive an abort. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.FirstLaneOracleSimulation

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
    (counters : EncodingBudgetCounters) (computation : OracleComp (World Index) α) :
    OracleComp (World Index) (Option α × EncodingBudgetCounters) :=
  let credited := counters.credit direct encoding
  if credited.charge ≤ limit then
    (fun result => (result.1, credited.addSamples (credited.sampleFuel limit - result.2))) <$>
      limitEncodingSamples (credited.sampleFuel limit) computation
  else pure (none, counters)

theorem simulate_limitEncodingAction_eq (table : Index → Digest) (limit direct encoding : Nat)
    (counters : EncodingBudgetCounters) (computation : OracleComp (World Index) α)
    (hbound : ∀ result ∈ support (simulateQ (eagerTraceImpl table) computation).run,
      ((counters.credit direct encoding).addSamples result.2.encodingActions.length).charge ≤ limit) :
    (simulateQ (eagerTraceImpl table) (limitEncodingAction limit direct encoding counters computation)).run =
      (fun result => ((some result.1,
        (counters.credit direct encoding).addSamples result.2.encodingActions.length), result.2)) <$>
          (simulateQ (eagerTraceImpl table) computation).run := by
  let credited := counters.credit direct encoding
  have hbudget : credited.charge ≤ limit := by
    obtain ⟨result, hresult⟩ := probComp_support_nonempty (simulateQ (eagerTraceImpl table) computation).run
    exact (credited.addSamples_charge_mono result.2.encodingActions.length).trans (hbound result hresult)
  have hfuel (result) (hresult : result ∈ support (simulateQ (eagerTraceImpl table) computation).run) :
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
    (counters : EncodingBudgetCounters) (computation : OracleComp (World Index) α)
    (hbudget : counters.charge ≤ limit)
    (result : (Option α × EncodingBudgetCounters) × ActionTrace Index)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl table)
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
    exact ⟨hbudget, by simp [ActionTrace.encodingActions]⟩

theorem limitEncodingAction_trace_direct (table : Index → Digest) (limit direct encoding : Nat)
    (counters : EncodingBudgetCounters) (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsHazardQuery direct)
    (result : (Option α × EncodingBudgetCounters) × ActionTrace Index)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl table)
      (limitEncodingAction limit direct encoding counters computation)).run) :
    counters.direct + hazardCount result.2 ≤ result.1.2.direct := by
  let credited := counters.credit direct encoding
  by_cases hcredit : credited.charge ≤ limit
  · rw [limitEncodingAction, if_pos hcredit, simulateQ_map, WriterT.run_map, support_map] at hresult
    obtain ⟨limited, hlimited, rfl⟩ := hresult
    have hqueryBound := QueryLimiting.limit_preserves_queryBound IsEncodingSample IsHazardQuery
      (credited.sampleFuel limit) direct computation hbound
    have hcount := simulate_eagerTrace_support_hazardCount_le table
      (limitEncodingSamples (credited.sampleFuel limit) computation) direct hqueryBound limited hlimited
    change counters.direct + hazardCount limited.2 ≤ counters.direct + direct
    omega
  · rw [limitEncodingAction, if_neg hcredit] at hresult
    simp only [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    simp [hazardCount]

/-- info: 'XmssSecurity.FirstLaneOracleSimulation.simulate_limitEncodingAction_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simulate_limitEncodingAction_eq

/-- info: 'XmssSecurity.FirstLaneOracleSimulation.limitEncodingAction_trace_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitEncodingAction_trace_budget

end XmssSecurity.FirstLaneOracleSimulation
