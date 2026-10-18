import XmssSecurity.Proof.TargetSum.Direct.FirstLaneBudgetEnforcement
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! A successful limited prefix is a supported execution of the original ideal
experiment with exactly the same output, state, and observations. Its cache and signing
invariants therefore remain available to the deciding-probe argument. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.CappedChain

open FirstLaneOracleSimulation

theorem limitedFirstLanePrefix_success_support {α : Type}
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (limit : Nat) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (state : Generic.CappedChain.GlobalHighDirectTracedState) (counters : EncodingBudgetCounters)
    (result : (Option (α × Generic.CappedChain.GlobalHighDirectTracedState) × EncodingBudgetCounters) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex) (value : α × Generic.CappedChain.GlobalHighDirectTracedState)
    (hresult : result ∈ support (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      (limitedFirstLanePrefix limit key edgeHigh computation state counters)).run)
    (hvalue : result.1.1 = some value) :
    (value, result.2) ∈ support (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      ((simulateQ (Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh) computation).run state)).run := by
  induction computation using OracleComp.inductionOn generalizing state counters result value with
  | pure output =>
      simp only [limitedFirstLanePrefix_pure, simulateQ_pure, WriterT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      simp only [Option.some.injEq] at hvalue
      subst value
      simp
  | query_bind input next ih =>
      rw [limitedFirstLanePrefix_query_bind, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rw [support_map] at htail
      obtain ⟨tail, htail, rfl⟩ := htail
      cases hhandled : head.1.1 with
      | none =>
          simp only [hhandled, simulateQ_pure, WriterT.run_pure, support_pure,
            Set.mem_singleton_iff] at htail
          subst tail
          cases hvalue
      | some handled =>
          simp only [hhandled] at htail
          have hheadOriginal := limitEncodingAction_success_support table limit (Generic.CappedChain.directHashActionCost input)
            (directEncodingActionCost key.secretKey.parameter input) counters
            ((Generic.CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state) head handled hhead hhandled
          have htailOriginal := ih handled.1 handled.2 head.1.2 tail value htail hvalue
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind',
            mem_support_bind_iff, support_map]
          exact ⟨(handled, head.2), hheadOriginal, (value, tail.2), htailOriginal, rfl⟩

theorem limitedFirstLanePrefix_returnedCovered {α : Type}
    (table : Generic.CappedChain.GlobalChainValueIndex → Digest) (limit : Nat) (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + Generic.SigningSpec) α)
    (counters : EncodingBudgetCounters)
    (result : (Option (α × Generic.CappedChain.GlobalHighDirectTracedState) × EncodingBudgetCounters) ×
      Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex) (value : α × Generic.CappedChain.GlobalHighDirectTracedState)
    (hresult : result ∈ support (simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      (limitedFirstLanePrefix limit key edgeHigh computation
        (Generic.CappedChain.GlobalHighDirectTracedState.initial (Generic.CappedChain.globalFilteredCausalKeygenState key)) counters)).run)
    (hvalue : result.1.1 = some value) :
    Generic.CappedChain.GlobalCausalTraceRevealsCovered
      (Generic.CappedChain.GlobalReturnedChainValueCovered value.2.causalState.cache key.secretKey
        value.2.attackerTrace.toSigningLog) result.2.chainActions :=
  Generic.CappedChain.globalFirstLaneAdversary_support_returnedCovered key table edgeHigh computation (value, result.2)
    (limitedFirstLanePrefix_success_support table limit key edgeHigh computation _ counters result value hresult hvalue)

/-- info: 'XmssSecurity.TargetSum.CappedChain.limitedFirstLanePrefix_success_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitedFirstLanePrefix_success_support

end XmssSecurity.TargetSum.CappedChain
