import Xmss.Proof.TargetSum.Direct.LimitedAcceptedProbe
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Bound collisions and the conditional deciding probe in the complete limited
prefix experiment, including its runs after a collision. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Deciding

open CappedExecution FirstLaneOracleSimulation

noncomputable def publicLimitedPrefixExecution (limit : Nat) (adversary : Adversary)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) :
    OracleComp CappedExecution.GlobalFirstLaneWorld LimitedPrefixResult :=
  limitedFirstLanePrefix limit key (adversary.main key.publicKey)
    (CappedExecution.GlobalDirectTracedState.initial (CappedExecution.globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩

abbrev CoupledLimitedPrefixResult := Deciding.BaseKey × (LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)

theorem publicLimitedPrefix_trace_bound (limit : Nat) (adversary : Adversary)
    (key : CappedExecution.ProgrammedGlobalChainKeygenView) (base : CappedExecution.GlobalChainValueIndex → Digest)
    (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedExecution.GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base)
      (publicLimitedPrefixExecution limit adversary key)).run) :
    FirstLaneOracleSimulation.hazardCount result.2 ≤ limit := by
  have hbudget := limitedFirstLanePrefix_trace_budget base limit key (adversary.main key.publicKey)
    (CappedExecution.GlobalDirectTracedState.initial (CappedExecution.globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩
    (by simp [EncodingBudgetCounters.charge]) result hresult
  have hcount := limitedFirstLanePrefix_trace_direct base limit key (adversary.main key.publicKey)
    (CappedExecution.GlobalDirectTracedState.initial (CappedExecution.globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩ result hresult
  have hdirect : result.1.2.direct ≤ limit := (Nat.le_add_right _ _).trans hbudget.1
  simpa only [Nat.zero_add] using hcount.trans hdirect

theorem coupledLimitedPrefix_trace_bound (limit : Nat) (adversary : Adversary)
    (result : CoupledLimitedPrefixResult)
    (hresult : result ∈ support (Deciding.coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary))) :
    FirstLaneOracleSimulation.hazardCount result.2.2 ≤ limit := by
  unfold Deciding.coupledFirstLaneProgram at hresult
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨key, _, outcome, houtcome, rfl⟩ := hresult
  exact publicLimitedPrefix_trace_bound limit adversary key.1 key.2 outcome houtcome

end Xmss.TargetSum.Deciding
