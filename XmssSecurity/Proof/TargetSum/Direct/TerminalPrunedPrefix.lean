import XmssSecurity.Proof.TargetSum.Direct.TerminalCutSoundness
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The public prefix stops before a final nonencoding query when no encoding has
been accepted. Completed executions preserve the original prefix and all its invariants. -/

open OracleComp OracleSpec
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.CappedChain

open FirstLaneOracleSimulation

noncomputable def terminalPrunedFirstLanePrefix {α : Type} (limit : Nat)
    (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CappedChain.GlobalDirectTracedState) (counters : EncodingBudgetCounters) :
    OracleComp CappedChain.GlobalFirstLaneWorld (Option (α × CappedChain.GlobalDirectTracedState) × EncodingBudgetCounters) :=
  OracleComp.recOn computation (fun value state counters => pure (some (value, state), counters))
    (fun input _ next state counters =>
      if TerminalPrefixCut limit key input state counters then pure (none, counters)
      else do
        let result ← limitedFirstLaneAction limit key input state counters
        match result.1 with
        | none => pure (none, result.2)
        | some handled => next handled.1 handled.2 result.2) state counters

theorem terminalPrunedFirstLanePrefix_pure {α : Type} (limit : Nat)
    (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (value : α) (state : CappedChain.GlobalDirectTracedState) (counters : EncodingBudgetCounters) :
    terminalPrunedFirstLanePrefix limit key (pure value) state counters =
      pure (some (value, state), counters) := rfl

theorem terminalPrunedFirstLanePrefix_query_bind {α : Type} (limit : Nat)
    (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (state : CappedChain.GlobalDirectTracedState) (counters : EncodingBudgetCounters) :
    terminalPrunedFirstLanePrefix limit key (liftM ((OracleWorld + SigningSpec).query input) >>= next)
      state counters =
      (if TerminalPrefixCut limit key input state counters then pure (none, counters)
      else do
        let result ← limitedFirstLaneAction limit key input state counters
        match result.1 with
        | none => pure (none, result.2)
        | some handled => terminalPrunedFirstLanePrefix limit key (next handled.1) handled.2 result.2) := rfl

theorem terminalPrunedFirstLanePrefix_trace_budget {α : Type}
    (table : CappedChain.GlobalChainValueIndex → Digest) (limit : Nat) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CappedChain.GlobalDirectTracedState) (counters : EncodingBudgetCounters)
    (hbudget : counters.charge ≤ limit)
    (result : (Option (α × CappedChain.GlobalDirectTracedState) × EncodingBudgetCounters) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (terminalPrunedFirstLanePrefix limit key computation state counters)).run) :
    result.1.2.charge ≤ limit ∧ result.1.2.samples = counters.samples + result.2.encodingActions.length ∧
      counters.direct + FirstLaneOracleSimulation.hazardCount result.2 ≤ result.1.2.direct := by
  induction computation using OracleComp.inductionOn generalizing state counters result with
  | pure value =>
      simp only [terminalPrunedFirstLanePrefix_pure, simulateQ_pure, WriterT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨hbudget, by simp [FirstLaneOracleSimulation.ActionTrace.encodingActions], by simp [FirstLaneOracleSimulation.hazardCount]⟩
  | query_bind input next ih =>
      rw [terminalPrunedFirstLanePrefix_query_bind] at hresult
      by_cases hcut : TerminalPrefixCut limit key input state counters
      · simp only [if_pos hcut, simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
        subst result
        exact ⟨hbudget, by simp [FirstLaneOracleSimulation.ActionTrace.encodingActions], by simp [FirstLaneOracleSimulation.hazardCount]⟩
      · rw [if_neg hcut, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
        obtain ⟨head, hhead, htail⟩ := hresult
        rw [support_map] at htail
        obtain ⟨tail, htail, rfl⟩ := htail
        have hheadBudget := limitEncodingAction_trace_budget table limit (CappedChain.directHashActionCost input)
          (directEncodingActionCost key.secretKey.parameter input) counters
          ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key input).run state) hbudget head hhead
        have hheadDirect := limitEncodingAction_trace_direct table limit (CappedChain.directHashActionCost input)
          (directEncodingActionCost key.secretKey.parameter input) counters
          ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key input).run state)
          (CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl_hazardBound key input state) head hhead
        change tail.1.2.charge ≤ limit ∧
          tail.1.2.samples = counters.samples + (head.2 ++ tail.2).encodingActions.length ∧
          counters.direct + FirstLaneOracleSimulation.hazardCount (head.2 ++ tail.2) ≤ tail.1.2.direct
        cases hhandled : head.1.1 with
        | none =>
            simp only [hhandled, simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at htail
            subst tail
            simpa using And.intro hheadBudget.1 (And.intro hheadBudget.2 hheadDirect)
        | some handled =>
            simp only [hhandled] at htail
            have htailBudget := ih handled.1 handled.2 head.1.2 hheadBudget.1 tail htail
            refine ⟨htailBudget.1, ?_, ?_⟩
            · rw [htailBudget.2.1, hheadBudget.2, FirstLaneOracleSimulation.ActionTrace.encodingActions_append, List.length_append, Nat.add_assoc]
            · rw [FirstLaneOracleSimulation.hazardCount_append]
              omega

theorem terminalPrunedFirstLanePrefix_success_support {α : Type}
    (table : CappedChain.GlobalChainValueIndex → Digest) (limit : Nat) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CappedChain.GlobalDirectTracedState) (counters : EncodingBudgetCounters)
    (result : (Option (α × CappedChain.GlobalDirectTracedState) × EncodingBudgetCounters) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex) (value : α × CappedChain.GlobalDirectTracedState)
    (hresult : result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (terminalPrunedFirstLanePrefix limit key computation state counters)).run)
    (hvalue : result.1.1 = some value) :
    (value, result.2) ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      ((simulateQ (CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key) computation).run state)).run := by
  induction computation using OracleComp.inductionOn generalizing state counters result value with
  | pure output =>
      simp only [terminalPrunedFirstLanePrefix_pure, simulateQ_pure, WriterT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      simp only [Option.some.injEq] at hvalue
      subst value
      simp
  | query_bind input next ih =>
      rw [terminalPrunedFirstLanePrefix_query_bind] at hresult
      by_cases hcut : TerminalPrefixCut limit key input state counters
      · simp only [if_pos hcut, simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
        subst result
        cases hvalue
      · rw [if_neg hcut, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
        obtain ⟨head, hhead, htail⟩ := hresult
        rw [support_map] at htail
        obtain ⟨tail, htail, rfl⟩ := htail
        cases hhandled : head.1.1 with
        | none =>
            simp only [hhandled, simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at htail
            subst tail
            cases hvalue
        | some handled =>
            simp only [hhandled] at htail
            have hheadOriginal := limitEncodingAction_success_support table limit (CappedChain.directHashActionCost input)
              (directEncodingActionCost key.secretKey.parameter input) counters
              ((CappedChain.globalFirstLaneExactTracedMappedAdversaryImpl key input).run state) head handled hhead hhandled
            have htailOriginal := ih handled.1 handled.2 head.1.2 tail value htail hvalue
            simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind',
              mem_support_bind_iff, support_map]
            exact ⟨(handled, head.2), hheadOriginal, (value, tail.2), htailOriginal, rfl⟩

theorem terminalPrunedFirstLanePrefix_returnedCovered {α : Type}
    (table : CappedChain.GlobalChainValueIndex → Digest) (limit : Nat) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (counters : EncodingBudgetCounters)
    (result : (Option (α × CappedChain.GlobalDirectTracedState) × EncodingBudgetCounters) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex) (value : α × CappedChain.GlobalDirectTracedState)
    (hresult : result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (terminalPrunedFirstLanePrefix limit key computation
        (CappedChain.GlobalDirectTracedState.initial (CappedChain.globalFilteredCausalKeygenState key)) counters)).run)
    (hvalue : result.1.1 = some value) :
    CappedChain.GlobalCausalTraceRevealsCovered
      (CappedChain.GlobalReturnedChainValueCovered value.2.causalState.cache key.secretKey
        value.2.attackerTrace.toSigningLog) result.2.chainActions :=
  CappedChain.globalFirstLaneAdversary_support_returnedCovered key table computation (value, result.2)
    (terminalPrunedFirstLanePrefix_success_support table limit key computation _ counters result value hresult hvalue)

/-- info: 'XmssSecurity.TargetSum.CappedChain.terminalPrunedFirstLanePrefix_trace_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminalPrunedFirstLanePrefix_trace_budget

/-- info: 'XmssSecurity.TargetSum.CappedChain.terminalPrunedFirstLanePrefix_returnedCovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminalPrunedFirstLanePrefix_returnedCovered

end XmssSecurity.TargetSum.CappedChain
