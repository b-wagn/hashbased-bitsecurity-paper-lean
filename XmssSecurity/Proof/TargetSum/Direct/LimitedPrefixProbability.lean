import XmssSecurity.Proof.TargetSum.Direct.LimitedFirstLaneExpected

/-! Bound collisions and the conditional deciding probe in the complete limited
prefix experiment, including its runs after a collision. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

noncomputable def publicLimitedPrefixExecution (limit : Nat) (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) (edgeHigh : GlobalChainEdgeIndex → Digest) :
    OracleComp GlobalFirstLaneWorld LimitedPrefixResult :=
  limitedFirstLanePrefix limit key edgeHigh (adversary.main key.publicKey)
    (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩

abbrev CoupledLimitedPrefixResult := BaseHighKey × (LimitedPrefixResult × ActionTrace GlobalChainValueIndex)

theorem publicLimitedPrefix_trace_bound (limit : Nat) (adversary : Adversary)
    (key : ProgrammedGlobalChainKeygenView) (base : GlobalChainValueIndex → Digest)
    (edgeHigh : GlobalChainEdgeIndex → Digest)
    (result : LimitedPrefixResult × ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl base)
      (publicLimitedPrefixExecution limit adversary key edgeHigh)).run) :
    hazardCount result.2 ≤ limit := by
  have hbudget := limitedFirstLanePrefix_trace_budget base limit key edgeHigh (adversary.main key.publicKey)
    (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩
    (by simp [EncodingBudgetCounters.charge]) result hresult
  have hcount := limitedFirstLanePrefix_trace_direct base limit key edgeHigh (adversary.main key.publicKey)
    (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩ result hresult
  have hdirect : result.1.2.direct ≤ limit := (Nat.le_add_right _ _).trans hbudget.1
  simpa only [Nat.zero_add] using hcount.trans hdirect

theorem coupledLimitedPrefix_trace_bound (limit : Nat) (adversary : Adversary)
    (result : CoupledLimitedPrefixResult)
    (hresult : result ∈ support (coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary))) :
    hazardCount result.2.2 ≤ limit := by
  unfold coupledFirstLaneProgram at hresult
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨key, _, outcome, houtcome, rfl⟩ := hresult
  exact publicLimitedPrefix_trace_bound limit adversary key.1.1 key.1.2 key.2 outcome houtcome

end XmssSecurity.TargetSum.Deciding
