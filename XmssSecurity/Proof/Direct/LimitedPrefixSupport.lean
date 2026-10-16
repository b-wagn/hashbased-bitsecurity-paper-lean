import XmssSecurity.Proof.Direct.FirstLaneBudgetEnforcement

/-! A successful limited prefix is a supported execution of the original ideal
experiment with exactly the same output, state, and observations. Its cache and signing
invariants therefore remain available to the deciding-probe argument. -/

open OracleComp OracleSpec

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.CappedChain

open FirstLaneOracleSimulation

theorem limitedFirstLanePrefix_success_support {α : Type}
    (table : GlobalChainValueIndex → Digest) (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : GlobalHighDirectTracedState) (counters : EncodingBudgetCounters)
    (result : (Option (α × GlobalHighDirectTracedState) × EncodingBudgetCounters) ×
      ActionTrace GlobalChainValueIndex) (value : α × GlobalHighDirectTracedState)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl table)
      (limitedFirstLanePrefix limit key edgeHigh computation state counters)).run)
    (hvalue : result.1.1 = some value) :
    (value, result.2) ∈ support (simulateQ (eagerTraceImpl table)
      ((simulateQ (globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh) computation).run state)).run := by
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
          have hheadOriginal := limitEncodingAction_success_support table limit (directHashActionCost input)
            (directEncodingActionCost key.secretKey.parameter input) counters
            ((globalFirstLaneExactTracedMappedAdversaryImpl key edgeHigh input).run state) head handled hhead hhandled
          have htailOriginal := ih handled.1 handled.2 head.1.2 tail value htail hvalue
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, WriterT.run_bind',
            mem_support_bind_iff, support_map]
          exact ⟨(handled, head.2), hheadOriginal, (value, tail.2), htailOriginal, rfl⟩

theorem limitedFirstLanePrefix_returnedCovered {α : Type}
    (table : GlobalChainValueIndex → Digest) (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (counters : EncodingBudgetCounters)
    (result : (Option (α × GlobalHighDirectTracedState) × EncodingBudgetCounters) ×
      ActionTrace GlobalChainValueIndex) (value : α × GlobalHighDirectTracedState)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl table)
      (limitedFirstLanePrefix limit key edgeHigh computation
        (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) counters)).run)
    (hvalue : result.1.1 = some value) :
    GlobalCausalTraceRevealsCovered
      (GlobalReturnedChainValueCovered value.2.causalState.cache key.secretKey
        value.2.attackerTrace.toSigningLog) result.2.chainActions :=
  globalFirstLaneAdversary_support_returnedCovered key table edgeHigh computation (value, result.2)
    (limitedFirstLanePrefix_success_support table limit key edgeHigh computation _ counters result value hresult hvalue)

theorem limitedFirstLanePrefix_acceptedEncoding_implies_trace {α : Type}
    (table : GlobalChainValueIndex → Digest) (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (counters : EncodingBudgetCounters)
    (result : (Option (α × GlobalHighDirectTracedState) × EncodingBudgetCounters) ×
      ActionTrace GlobalChainValueIndex) (value : α × GlobalHighDirectTracedState)
    (hresult : result ∈ support (simulateQ (eagerTraceImpl table)
      (limitedFirstLanePrefix limit key edgeHigh computation
        (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) counters)).run)
    (hvalue : result.1.1 = some value)
    (haccepted : HasAcceptedEncoding key.secretKey.parameter value.2.causalState.cache) :
    TraceHasAcceptedEncoding result.2 := by
  have horiginal := limitedFirstLanePrefix_success_support table limit key edgeHigh computation _ counters
    result value hresult hvalue
  have hgrowth := globalFirstLaneExactTraced_acceptedGrowth table key edgeHigh computation
    (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) (value, result.2) horiginal
  exact (hgrowth haccepted).resolve_left (globalFilteredCausalKeygenState_no_acceptedEncoding key hkey)

def LimitedPrefixHasAcceptedEncoding {α : Type} (parameter : PublicParameter)
    (result : (Option (α × GlobalHighDirectTracedState) × EncodingBudgetCounters) ×
      ActionTrace GlobalChainValueIndex) : Prop :=
  ∃ value, result.1.1 = some value ∧ HasAcceptedEncoding parameter value.2.causalState.cache

theorem limitedFirstLanePrefix_accepted_probability_le_expected {α : Type}
    (table : GlobalChainValueIndex → Digest) (limit : Nat) (key : ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support trajectoryProgrammedGlobalChainKeygen)
    (edgeHigh : GlobalChainEdgeIndex → Digest) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (counters : EncodingBudgetCounters) :
    Pr[LimitedPrefixHasAcceptedEncoding key.secretKey.parameter |
      (simulateQ (eagerTraceImpl table) (limitedFirstLanePrefix limit key edgeHigh computation
        (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) counters)).run] ≤
      Checksum.acceptanceProbability * expectedSimulatedQueryCount (eagerUnitImpl table) IsEncodingSample
        (limitedFirstLanePrefix limit key edgeHigh computation
          (GlobalHighDirectTracedState.initial (globalFilteredCausalKeygenState key)) counters) () := by
  apply le_trans _ (traceEncodingAcceptance_probability_le_expected table _)
  apply probEvent_mono
  intro result hresult haccepted
  obtain ⟨value, hvalue, haccepted⟩ := haccepted
  exact limitedFirstLanePrefix_acceptedEncoding_implies_trace table limit key hkey edgeHigh computation
    counters result value hresult hvalue haccepted

/-- info: 'XmssSecurity.CappedChain.limitedFirstLanePrefix_success_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitedFirstLanePrefix_success_support

/-- info: 'XmssSecurity.CappedChain.limitedFirstLanePrefix_accepted_probability_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms limitedFirstLanePrefix_accepted_probability_le_expected

end XmssSecurity.CappedChain
