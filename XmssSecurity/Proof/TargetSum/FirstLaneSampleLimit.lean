import XmssSecurity.Proof.TargetSum.QueryLimiting
import XmssSecurity.Proof.TargetSum.FirstLaneEncodingAcceptance
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! A public limiter for fresh encoding samples. It keeps the complete observed prefix
when it stops, and does not change computations whose supported traces fit the fuel. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.FirstLaneOracleSimulation

variable {Index : Type} {α : Type}

noncomputable def limitEncodingSamples (fuel : Nat) (computation : OracleComp (Generic.FirstLaneOracleSimulation.World Index) α) :
    OracleComp (Generic.FirstLaneOracleSimulation.World Index) (Option α × Nat) :=
  QueryLimiting.limit IsEncodingSample fuel computation

theorem encodingSamples_traceFragment (input : (Generic.FirstLaneOracleSimulation.World Index).Domain)
    (output : (Generic.FirstLaneOracleSimulation.World Index).Range input) :
    (Generic.FirstLaneOracleSimulation.traceFragment input output).encodingActions.length = if IsEncodingSample input then 1 else 0 := by
  cases input <;> simp [Generic.FirstLaneOracleSimulation.traceFragment, Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions, IsEncodingSample]

theorem eagerTraceImpl_encodingSamples (table : Index → Digest)
    (input : (Generic.FirstLaneOracleSimulation.World Index).Domain) (result : (Generic.FirstLaneOracleSimulation.World Index).Range input × Generic.FirstLaneOracleSimulation.ActionTrace Index)
    (hresult : result ∈ support (Generic.FirstLaneOracleSimulation.eagerTraceImpl table input).run) :
    result.2.encodingActions.length = if IsEncodingSample input then 1 else 0 := by
  have hrun : (Generic.FirstLaneOracleSimulation.eagerTraceImpl table input).run =
      (fun output => (output, Generic.FirstLaneOracleSimulation.traceFragment input output)) <$> Generic.FirstLaneOracleSimulation.eagerImpl table input := by
    simp [Generic.FirstLaneOracleSimulation.eagerTraceImpl, QueryImpl.withTraceAppend_apply, WriterT.run_tell]
  rw [hrun, support_map] at hresult
  obtain ⟨output, _, rfl⟩ := hresult
  exact encodingSamples_traceFragment input output

theorem simulate_limitEncodingSamples_eq (table : Index → Digest) (fuel : Nat)
    (computation : OracleComp (Generic.FirstLaneOracleSimulation.World Index) α)
    (hbound : ∀ result ∈ support (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table) computation).run,
      result.2.encodingActions.length ≤ fuel) :
    (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table) (limitEncodingSamples fuel computation)).run =
      (fun result => ((some result.1, fuel - result.2.encodingActions.length), result.2)) <$>
        (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table) computation).run := by
  exact QueryLimiting.simulate_limit_eq IsEncodingSample (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
    (fun trace => trace.encodingActions.length) rfl
    (fun left right => by rw [Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append])
    (eagerTraceImpl_encodingSamples table) fuel computation hbound

theorem limitEncodingSamples_trace_budget (table : Index → Digest) (fuel : Nat)
    (computation : OracleComp (Generic.FirstLaneOracleSimulation.World Index) α)
    (result : (Option α × Nat) × Generic.FirstLaneOracleSimulation.ActionTrace Index)
    (hresult : result ∈ support (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      (limitEncodingSamples fuel computation)).run) :
    result.2.encodingActions.length + result.1.2 = fuel :=
  QueryLimiting.limit_trace_budget IsEncodingSample (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
    (fun trace => trace.encodingActions.length) rfl
    (fun left right => by rw [Generic.FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append])
    (eagerTraceImpl_encodingSamples table) fuel computation result hresult

/-- info: 'XmssSecurity.TargetSum.FirstLaneOracleSimulation.simulate_limitEncodingSamples_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simulate_limitEncodingSamples_eq

/-- info: 'XmssSecurity.TargetSum.FirstLaneOracleSimulation.limitEncodingSamples_trace_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitEncodingSamples_trace_budget

end XmssSecurity.TargetSum.FirstLaneOracleSimulation
