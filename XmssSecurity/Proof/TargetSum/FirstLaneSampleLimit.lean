import XmssSecurity.Proof.TargetSum.QueryLimiting
import XmssSecurity.Proof.TargetSum.FirstLaneEncodingAcceptance

/-! A public limiter for fresh encoding samples. It keeps the complete observed prefix
when it stops, and does not change computations whose supported traces fit the fuel. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.FirstLaneOracleSimulation

variable {Index : Type} {α : Type}

noncomputable def limitEncodingSamples (fuel : Nat) (computation : OracleComp (World Index) α) :
    OracleComp (World Index) (Option α × Nat) :=
  QueryLimiting.limit IsEncodingSample fuel computation

theorem encodingSamples_traceFragment (input : (World Index).Domain)
    (output : (World Index).Range input) :
    (traceFragment input output).encodingActions.length = if IsEncodingSample input then 1 else 0 := by
  cases input <;> simp [traceFragment, ActionTrace.encodingActions, IsEncodingSample]

theorem eagerTraceImpl_encodingSamples (table : Index → Digest)
    (input : (World Index).Domain) (result : (World Index).Range input × ActionTrace Index)
    (hresult : result ∈ support (eagerTraceImpl table input).run) :
    result.2.encodingActions.length = if IsEncodingSample input then 1 else 0 := by
  have hrun : (eagerTraceImpl table input).run =
      (fun output => (output, traceFragment input output)) <$> eagerImpl table input := by
    simp [eagerTraceImpl, QueryImpl.withTraceAppend_apply, WriterT.run_tell]
  rw [hrun, support_map] at hresult
  obtain ⟨output, _, rfl⟩ := hresult
  exact encodingSamples_traceFragment input output

theorem simulate_limitEncodingSamples_eq (table : Index → Digest) (fuel : Nat)
    (computation : OracleComp (World Index) α)
    (hbound : ∀ result ∈ support (simulateQ (eagerTraceImpl table) computation).run,
      result.2.encodingActions.length ≤ fuel) :
    (simulateQ (eagerTraceImpl table) (limitEncodingSamples fuel computation)).run =
      (fun result => ((some result.1, fuel - result.2.encodingActions.length), result.2)) <$>
        (simulateQ (eagerTraceImpl table) computation).run := by
  exact QueryLimiting.simulate_limit_eq IsEncodingSample (eagerTraceImpl table)
    (fun trace => trace.encodingActions.length) rfl
    (fun left right => by rw [ActionTrace.encodingActions_append, List.length_append])
    (eagerTraceImpl_encodingSamples table) fuel computation hbound

theorem limitEncodingSamples_trace_budget (table : Index → Digest) (fuel : Nat)
    (computation : OracleComp (World Index) α)
    (result : (Option α × Nat) × ActionTrace Index)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl table)
      (limitEncodingSamples fuel computation)).run) :
    result.2.encodingActions.length + result.1.2 = fuel :=
  QueryLimiting.limit_trace_budget IsEncodingSample (eagerTraceImpl table)
    (fun trace => trace.encodingActions.length) rfl
    (fun left right => by rw [ActionTrace.encodingActions_append, List.length_append])
    (eagerTraceImpl_encodingSamples table) fuel computation result hresult

/-- info: 'XmssSecurity.TargetSum.FirstLaneOracleSimulation.simulate_limitEncodingSamples_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simulate_limitEncodingSamples_eq

/-- info: 'XmssSecurity.TargetSum.FirstLaneOracleSimulation.limitEncodingSamples_trace_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitEncodingSamples_trace_budget

end XmssSecurity.TargetSum.FirstLaneOracleSimulation
