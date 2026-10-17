import XmssSecurity.Proof.TargetSum.Direct.TerminalPrunedPrefix

/-! Once the terminal-pruned prefix exhausts its public budget, its remaining
execution emits no further monitor actions. Signing and direct hashing both stop. -/

open OracleComp OracleSpec
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.TargetSum.FirstLaneOracleSimulation

theorem simulate_eagerTrace_zero_special_trace {Index α : Type}
    (table : Index → Digest) (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsSpecialQuery 0)
    (result : α × ActionTrace Index)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl table) computation).run) :
    result.2 = [] := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          rw [simulateQ_query_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
          obtain ⟨head, hhead, htail⟩ := hresult
          simp [eagerTraceImpl, eagerImpl, traceFragment,
            QueryImpl.withTraceAppend_apply, WriterT.run_tell] at hhead
          obtain ⟨output, _, rfl⟩ := hhead
          rw [support_map] at htail
          obtain ⟨tail, htail, rfl⟩ := htail
          exact ih output (by simpa [IsSpecialQuery] using hbound.2 output) tail htail
      | encodingQuery leaf => simp [IsSpecialQuery] at hbound
      | encodingSignAttempt leaf => simp [IsSpecialQuery] at hbound
      | probe index target => simp [IsSpecialQuery] at hbound
      | reveal index => simp [IsSpecialQuery] at hbound

theorem limitEncodingAction_zero_special {Index α : Type}
    (table : Index → Digest) (limit : Nat) (counters : EncodingBudgetCounters)
    (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsSpecialQuery 0)
    (result : (Option α × EncodingBudgetCounters) × ActionTrace Index)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl table)
      (limitEncodingAction limit 0 0 counters computation)).run) :
    counters.charge ≤ result.1.2.charge ∧ result.2 = [] := by
  let credited := counters.credit 0 0
  by_cases hcredit : credited.charge ≤ limit
  · rw [limitEncodingAction, if_pos hcredit, simulateQ_map, WriterT.run_map, support_map] at hresult
    obtain ⟨limited, hlimited, rfl⟩ := hresult
    have hqueryBound := QueryLimiting.limit_preserves_queryBound IsEncodingSample IsSpecialQuery
      (credited.sampleFuel limit) 0 computation hbound
    refine ⟨?_, simulate_eagerTrace_zero_special_trace table _ hqueryBound limited hlimited⟩
    simpa only [credited, EncodingBudgetCounters.credit, Nat.add_zero] using
      EncodingBudgetCounters.addSamples_charge_mono credited (credited.sampleFuel limit - limited.1.2)
  · rw [limitEncodingAction, if_neg hcredit] at hresult
    simp only [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact ⟨le_rfl, rfl⟩

theorem limitEncodingAction_zero_hazards {Index α : Type}
    (table : Index → Digest) (limit : Nat) (counters : EncodingBudgetCounters)
    (computation : OracleComp (World Index) α)
    (hbound : computation.IsQueryBoundP IsHazardQuery 0)
    (result : (Option α × EncodingBudgetCounters) × ActionTrace Index)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl table)
      (limitEncodingAction limit 0 0 counters computation)).run) :
    counters.charge ≤ result.1.2.charge ∧ hazardCount result.2 = 0 := by
  let credited := counters.credit 0 0
  by_cases hcredit : credited.charge ≤ limit
  · rw [limitEncodingAction, if_pos hcredit, simulateQ_map, WriterT.run_map, support_map] at hresult
    obtain ⟨limited, hlimited, rfl⟩ := hresult
    have hqueryBound := QueryLimiting.limit_preserves_queryBound IsEncodingSample IsHazardQuery
      (credited.sampleFuel limit) 0 computation hbound
    have hcount := simulate_eagerTrace_support_hazardCount_le table
      (limitEncodingSamples (credited.sampleFuel limit) computation) 0 hqueryBound limited hlimited
    refine ⟨?_, Nat.eq_zero_of_le_zero hcount⟩
    simpa only [credited, EncodingBudgetCounters.credit, Nat.add_zero] using
      EncodingBudgetCounters.addSamples_charge_mono credited (credited.sampleFuel limit - limited.1.2)
  · rw [limitEncodingAction, if_neg hcredit] at hresult
    simp only [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact ⟨le_rfl, rfl⟩

end XmssSecurity.TargetSum.FirstLaneOracleSimulation

namespace XmssSecurity.TargetSum.CappedChain

open FirstLaneOracleSimulation

theorem globalFirstLaneExactTraced_uniform_zero_special
    (key : ProgrammedGlobalChainKeygenView) (edgeHigh : GlobalChainEdgeIndex → Digest)
    (n : Nat) (state : GlobalHighDirectTracedState) :
    ((globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh (.inl (.inl n))).run state).IsQueryBoundP
      IsSpecialQuery 0 := by
  change (((liftM ((GlobalFirstLaneWorld).query (.uniform n)) :
    OracleComp GlobalFirstLaneWorld (Fin (n + 1))) >>= fun output =>
    pure (output, state.causalState)) >>= fun result =>
      pure (result.1, globalExactTracedNextState key (.inl (.inl n)) state result.1 result.2)).IsQueryBoundP
        IsSpecialQuery 0
  simp [IsSpecialQuery]

theorem terminalPrunedFirstLanePrefix_exhausted_trace_eq_nil {α : Type}
    (table : GlobalChainValueIndex → Digest) (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalHighDirectTracedState) (counters : EncodingBudgetCounters)
    (hexhausted : limit ≤ counters.charge)
    (result : (Option (α × GlobalHighDirectTracedState) × EncodingBudgetCounters) ×
      ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl table)
      (terminalPrunedFirstLanePrefix limit key edgeHigh computation state counters)).run) :
    result.2 = [] := by
  induction computation using OracleComp.inductionOn generalizing state counters result with
  | pure value =>
      simp only [terminalPrunedFirstLanePrefix_pure, simulateQ_pure, WriterT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | query_bind input next ih =>
      rw [terminalPrunedFirstLanePrefix_query_bind] at hresult
      by_cases hcut : TerminalPrefixCut limit key input state counters
      · simp only [if_pos hcut, simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
        subst result
        rfl
      · cases input with
        | inr request =>
            exact (hcut (Or.inr (Or.inl ⟨by omega, request, rfl⟩))).elim
        | inl input =>
            cases input with
            | inr input => exact (hcut (Or.inr (Or.inr ⟨hexhausted, input, rfl⟩))).elim
            | inl input =>
                rw [if_neg hcut, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
                obtain ⟨head, hhead, htail⟩ := hresult
                rw [support_map] at htail
                obtain ⟨tail, htail, rfl⟩ := htail
                have hhead' : head ∈ support (simulateQ (eagerTraceImpl table)
                    (limitEncodingAction limit 0 0 counters
                      ((globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh (.inl (.inl input))).run state))).run := by
                  simpa only [limitedFirstLaneAction, directHashActionCost, directEncodingActionCost,
                    CappedEncodingMonitor.IsEncodingHashQuery, if_false] using hhead
                have hzero := limitEncodingAction_zero_special table limit counters _
                  (globalFirstLaneExactTraced_uniform_zero_special key edgeHigh input state)
                  head hhead'
                change head.2 ++ tail.2 = []
                rw [hzero.2, List.nil_append]
                cases hhandled : head.1.1 with
                | none =>
                    simp only [hhandled, simulateQ_pure, WriterT.run_pure, support_pure,
                      Set.mem_singleton_iff] at htail
                    subst tail
                    rfl
                | some handled =>
                    simp only [hhandled] at htail
                    exact ih handled.1 handled.2 head.1.2 (hexhausted.trans hzero.1) tail htail

theorem terminalPrunedFirstLanePrefix_exhausted_hazardCount_eq_zero {α : Type}
    (table : GlobalChainValueIndex → Digest) (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalHighDirectTracedState) (counters : EncodingBudgetCounters)
    (hexhausted : limit ≤ counters.charge)
    (result : (Option (α × GlobalHighDirectTracedState) × EncodingBudgetCounters) ×
      ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl table)
      (terminalPrunedFirstLanePrefix limit key edgeHigh computation state counters)).run) :
    hazardCount result.2 = 0 := by
  rw [terminalPrunedFirstLanePrefix_exhausted_trace_eq_nil table limit key edgeHigh computation
    state counters hexhausted result hresult]
  rfl

/-- info: 'XmssSecurity.TargetSum.CappedChain.terminalPrunedFirstLanePrefix_exhausted_trace_eq_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminalPrunedFirstLanePrefix_exhausted_trace_eq_nil

/-- info: 'XmssSecurity.TargetSum.CappedChain.terminalPrunedFirstLanePrefix_exhausted_hazardCount_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminalPrunedFirstLanePrefix_exhausted_hazardCount_eq_zero

end XmssSecurity.TargetSum.CappedChain
