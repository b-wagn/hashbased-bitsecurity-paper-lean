import XmssSecurity.Proof.TargetSum.Direct.LimitedAcceptedProbe
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Bound collisions and the conditional deciding probe in the complete limited
prefix experiment, including its runs after a collision. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

noncomputable def publicLimitedPrefixExecution (limit : Nat) (adversary : Generic.Adversary)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) :
    OracleComp Generic.CappedChain.GlobalFirstLaneWorld LimitedPrefixResult :=
  limitedFirstLanePrefix limit key edgeHigh (adversary.main key.publicKey)
    (Generic.CappedChain.GlobalHighDirectTracedState.initial (Generic.CappedChain.globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩

abbrev CoupledLimitedPrefixResult := Generic.Deciding.BaseHighKey × (LimitedPrefixResult × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)

theorem publicLimitedPrefix_trace_bound (limit : Nat) (adversary : Generic.Adversary)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (base : Generic.CappedChain.GlobalChainValueIndex → Digest)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest)
    (result : LimitedPrefixResult × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl base)
      (publicLimitedPrefixExecution limit adversary key edgeHigh)).run) :
    Generic.FirstLaneOracleSimulation.hazardCount result.2 ≤ limit := by
  have hbudget := limitedFirstLanePrefix_trace_budget base limit key edgeHigh (adversary.main key.publicKey)
    (Generic.CappedChain.GlobalHighDirectTracedState.initial (Generic.CappedChain.globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩
    (by simp [EncodingBudgetCounters.charge]) result hresult
  have hcount := limitedFirstLanePrefix_trace_direct base limit key edgeHigh (adversary.main key.publicKey)
    (Generic.CappedChain.GlobalHighDirectTracedState.initial (Generic.CappedChain.globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩ result hresult
  have hdirect : result.1.2.direct ≤ limit := (Nat.le_add_right _ _).trans hbudget.1
  simpa only [Nat.zero_add] using hcount.trans hdirect

theorem coupledLimitedPrefix_trace_bound (limit : Nat) (adversary : Generic.Adversary)
    (result : CoupledLimitedPrefixResult)
    (hresult : result ∈ support (Generic.Deciding.coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary))) :
    Generic.FirstLaneOracleSimulation.hazardCount result.2.2 ≤ limit := by
  unfold Generic.Deciding.coupledFirstLaneProgram at hresult
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨key, _, outcome, houtcome, rfl⟩ := hresult
  exact publicLimitedPrefix_trace_bound limit adversary key.1.1 key.1.2 key.2 outcome houtcome

end XmssSecurity.TargetSum.Deciding
