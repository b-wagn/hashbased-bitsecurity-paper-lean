import Xmss.Proof.TargetSum.QueryLimiting
import Xmss.Proof.TargetSum.FirstLaneEncodingAcceptance
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! A public limiter for fresh encoding samples. It keeps the complete observed prefix
when it stops, and does not change computations whose supported traces fit the fuel. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.FirstLaneOracleSimulation

variable {Index : Type} {α : Type}

noncomputable def limitEncodingSamples (fuel : Nat) (computation : OracleComp (FirstLaneOracleSimulation.World Index) α) :
    OracleComp (FirstLaneOracleSimulation.World Index) (Option α × Nat) :=
  QueryLimiting.limit IsEncodingSample fuel computation

theorem encodingSamples_traceFragment (input : (FirstLaneOracleSimulation.World Index).Domain)
    (output : (FirstLaneOracleSimulation.World Index).Range input) :
    (FirstLaneOracleSimulation.traceFragment input output).encodingActions.length = if IsEncodingSample input then 1 else 0 := by
  cases input <;> simp [FirstLaneOracleSimulation.traceFragment, FirstLaneOracleSimulation.ActionTrace.encodingActions, IsEncodingSample]

theorem eagerTraceImpl_encodingSamples (table : Index → Digest)
    (input : (FirstLaneOracleSimulation.World Index).Domain) (result : (FirstLaneOracleSimulation.World Index).Range input × FirstLaneOracleSimulation.ActionTrace Index)
    (hresult : result ∈ support (FirstLaneOracleSimulation.eagerTraceImpl table input).run) :
    result.2.encodingActions.length = if IsEncodingSample input then 1 else 0 := by
  have hrun : (FirstLaneOracleSimulation.eagerTraceImpl table input).run =
      (fun output => (output, FirstLaneOracleSimulation.traceFragment input output)) <$> FirstLaneOracleSimulation.eagerImpl table input := by
    simp [FirstLaneOracleSimulation.eagerTraceImpl, QueryImpl.withTraceAppend_apply, WriterT.run_tell]
  rw [hrun, support_map] at hresult
  obtain ⟨output, _, rfl⟩ := hresult
  exact encodingSamples_traceFragment input output

theorem simulate_limitEncodingSamples_eq (table : Index → Digest) (fuel : Nat)
    (computation : OracleComp (FirstLaneOracleSimulation.World Index) α)
    (hbound : ∀ result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) computation).run,
      result.2.encodingActions.length ≤ fuel) :
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) (limitEncodingSamples fuel computation)).run =
      (fun result => ((some result.1, fuel - result.2.encodingActions.length), result.2)) <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) computation).run := by
  exact QueryLimiting.simulate_limit_eq IsEncodingSample (FirstLaneOracleSimulation.eagerTraceImpl table)
    (fun trace => trace.encodingActions.length) rfl
    (fun left right => by rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append])
    (eagerTraceImpl_encodingSamples table) fuel computation hbound

theorem limitEncodingSamples_trace_budget (table : Index → Digest) (fuel : Nat)
    (computation : OracleComp (FirstLaneOracleSimulation.World Index) α)
    (result : (Option α × Nat) × FirstLaneOracleSimulation.ActionTrace Index)
    (hresult : result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (limitEncodingSamples fuel computation)).run) :
    result.2.encodingActions.length + result.1.2 = fuel :=
  QueryLimiting.limit_trace_budget IsEncodingSample (FirstLaneOracleSimulation.eagerTraceImpl table)
    (fun trace => trace.encodingActions.length) rfl
    (fun left right => by rw [FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append])
    (eagerTraceImpl_encodingSamples table) fuel computation result hresult

/-- info: 'Xmss.TargetSum.FirstLaneOracleSimulation.simulate_limitEncodingSamples_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms simulate_limitEncodingSamples_eq

/-- info: 'Xmss.TargetSum.FirstLaneOracleSimulation.limitEncodingSamples_trace_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitEncodingSamples_trace_budget

end Xmss.TargetSum.FirstLaneOracleSimulation
