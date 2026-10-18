import XmssSecurity.Proof.TargetSum.Direct.TerminalPrunedPrefix
import XmssSecurity.Proof.TargetSum.Direct.CachedEncodingCost
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! A terminal-pruned execution can spend its last direct-query unit only after
encoding activity. This gives a one-unit saving on executions with zero encoding credit. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.FirstLaneOracleSimulation

theorem limitEncodingAction_counter_shape {Index α : Type}
    (table : Index → Digest) (limit direct encoding : Nat) (counters : EncodingBudgetCounters)
    (computation : OracleComp (FirstLaneOracleSimulation.World Index) α)
    (result : (Option α × EncodingBudgetCounters) × FirstLaneOracleSimulation.ActionTrace Index)
    (hresult : result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (limitEncodingAction limit direct encoding counters computation)).run) :
    result.1.2 = counters ∨ ∃ samples,
      result.1.2 = (counters.credit direct encoding).addSamples samples := by
  let credited := counters.credit direct encoding
  by_cases hcredit : credited.charge ≤ limit
  · rw [limitEncodingAction, if_pos hcredit, simulateQ_map, WriterT.run_map, support_map] at hresult
    obtain ⟨limited, _hlimited, rfl⟩ := hresult
    exact Or.inr ⟨_, rfl⟩
  · rw [limitEncodingAction, if_neg hcredit] at hresult
    simp only [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact Or.inl rfl

end XmssSecurity.TargetSum.FirstLaneOracleSimulation

namespace XmssSecurity.TargetSum.CappedChain

open FirstLaneOracleSimulation

theorem hasAcceptedEncoding_samples_positive (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (samples : Nat)
    (hcount : cachedEncodingInputCount cache parameter = (samples : ℝ≥0∞))
    (haccepted : HasAcceptedEncoding parameter cache) : 0 < samples := by
  obtain ⟨input, output, hcached, hencoding, _hvalid⟩ := haccepted
  obtain ⟨leaf, hleaf⟩ := Option.isSome_iff_exists.mp hencoding
  obtain ⟨payload, rfl⟩ := exists_encodingInput_of_encodingInputLeafIndex?_eq_some parameter input leaf hleaf
  have hone := one_le_cachedEncodingInputCount_of_cached parameter cache leaf payload (by simp [hcached])
  rw [hcount] at hone
  have hnat : 1 ≤ samples := by exact_mod_cast hone
  omega

theorem limitedFirstLaneAction_last_unit_requires_activity
    (table : CappedChain.GlobalChainValueIndex → Digest) (limit : Nat) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (input : (OracleWorld + SigningSpec).Domain)
    (state : CappedChain.GlobalHighDirectTracedState) (counters : EncodingBudgetCounters)
    (hprevious : counters.direct < limit ∨ 0 < counters.encoding + counters.samples)
    (hcache : HasAcceptedEncoding key.secretKey.parameter state.causalState.cache →
      0 < counters.encoding + counters.samples)
    (hcut : ¬TerminalPrefixCut limit key input state counters)
    (result : (Option ((OracleWorld + SigningSpec).Range input × CappedChain.GlobalHighDirectTracedState) ×
      EncodingBudgetCounters) × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (limitedFirstLaneAction limit key input state counters)).run) :
    result.1.2.direct < limit ∨ 0 < result.1.2.encoding + result.1.2.samples := by
  have hshape := limitEncodingAction_counter_shape table limit (CappedChain.directHashActionCost input)
    (directEncodingActionCost key.secretKey.parameter input) counters _ result hresult
  rcases hshape with hsame | ⟨samples, hshape⟩
  · simpa only [hsame] using hprevious
  · rw [hshape]
    by_cases hactivity : 0 < counters.encoding + counters.samples
    · right
      simp only [EncodingBudgetCounters.credit, EncodingBudgetCounters.addSamples]
      omega
    · have hdirect : counters.direct < limit := hprevious.resolve_right hactivity
      have hrejecting : ¬HasAcceptedEncoding key.secretKey.parameter state.causalState.cache :=
        fun h => hactivity (hcache h)
      cases input with
      | inr request =>
          exact Or.inl hdirect
      | inl input =>
          cases input with
          | inl n => exact Or.inl hdirect
          | inr hashInput =>
              by_cases hencoding : CappedEncodingMonitor.IsEncodingHashQuery key.secretKey.parameter (.inr hashInput)
              · right
                simp only [EncodingBudgetCounters.credit, EncodingBudgetCounters.addSamples,
                  directEncodingActionCost, if_pos hencoding]
                omega
              · left
                have hroom : counters.charge + 1 < limit := by
                  by_contra! hroom
                  exact hcut (Or.inl ⟨hroom, hrejecting, hashInput, rfl, hencoding⟩)
                change counters.direct + 1 < limit
                unfold EncodingBudgetCounters.charge at hroom
                omega

theorem terminalPrunedFirstLanePrefix_last_unit_requires_activity {α : Type}
    (table : CappedChain.GlobalChainValueIndex → Digest) (limit : Nat) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : CappedChain.GlobalHighDirectTracedState) (counters : EncodingBudgetCounters)
    (hbudget : counters.charge ≤ limit)
    (hprevious : counters.direct < limit ∨ 0 < counters.encoding + counters.samples)
    (hcacheCount : cachedEncodingInputCount state.causalState.cache key.secretKey.parameter =
      (counters.samples : ℝ≥0∞))
    (result : (Option (α × CappedChain.GlobalHighDirectTracedState) × EncodingBudgetCounters) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (terminalPrunedFirstLanePrefix limit key computation state counters)).run) :
    result.1.2.direct < limit ∨ 0 < result.1.2.encoding + result.1.2.samples := by
  induction computation using OracleComp.inductionOn generalizing state counters result with
  | pure value =>
      simp only [terminalPrunedFirstLanePrefix_pure, simulateQ_pure, WriterT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hprevious
  | query_bind input next ih =>
      rw [terminalPrunedFirstLanePrefix_query_bind] at hresult
      by_cases hcut : TerminalPrefixCut limit key input state counters
      · simp only [if_pos hcut, simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
        subst result
        exact hprevious
      · rw [if_neg hcut, simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
        obtain ⟨head, hhead, htail⟩ := hresult
        rw [support_map] at htail
        obtain ⟨tail, htail, rfl⟩ := htail
        have hheadActivity := limitedFirstLaneAction_last_unit_requires_activity table limit key
          input state counters hprevious (fun h => by
            have hpositive := hasAcceptedEncoding_samples_positive _ _ _ hcacheCount h
            omega) hcut head hhead
        have hheadBudget := limitEncodingAction_trace_budget table limit (CappedChain.directHashActionCost input)
          (directEncodingActionCost key.secretKey.parameter input) counters _ hbudget head hhead
        cases hhandled : head.1.1 with
        | none =>
            simp only [hhandled, simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at htail
            subst tail
            exact hheadActivity
        | some handled =>
            simp only [hhandled] at htail
            have hheadOriginal := limitEncodingAction_success_support table limit (CappedChain.directHashActionCost input)
              (directEncodingActionCost key.secretKey.parameter input) counters _ head handled hhead hhandled
            have hnextCount := globalFirstLaneExactTraced_query_encodingCountGrowth table key
              input state (handled, head.2) hheadOriginal
            change cachedEncodingInputCount handled.2.causalState.cache key.secretKey.parameter = _ at hnextCount
            have hnextCount' : cachedEncodingInputCount handled.2.causalState.cache key.secretKey.parameter =
                (head.1.2.samples : ℝ≥0∞) := by
              rw [hnextCount, hcacheCount, hheadBudget.2, Nat.cast_add]
            exact ih handled.1 handled.2 head.1.2 hheadBudget.1 hheadActivity hnextCount' tail htail

theorem terminalPrunedFirstLanePrefix_hazardCount_lt_of_no_activity {α : Type}
    (table : CappedChain.GlobalChainValueIndex → Digest) (limit : Nat) (hpositive : 0 < limit)
    (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (result : (Option (α × CappedChain.GlobalHighDirectTracedState) × EncodingBudgetCounters) ×
      FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
      (terminalPrunedFirstLanePrefix limit key computation
        (CappedChain.GlobalHighDirectTracedState.initial (CappedChain.globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩)).run)
    (hactivity : result.1.2.encoding + result.1.2.samples = 0) :
    FirstLaneOracleSimulation.hazardCount result.2 < limit := by
  let initial := CappedChain.GlobalHighDirectTracedState.initial (CappedChain.globalFilteredCausalKeygenState key)
  have hcacheCount : cachedEncodingInputCount initial.causalState.cache key.secretKey.parameter = 0 :=
    globalFilteredCausalKeygenState_encodingCount_zero key hkey
  have hlast := terminalPrunedFirstLanePrefix_last_unit_requires_activity table limit key
    computation initial ⟨0, 0, 0⟩ (by simp [EncodingBudgetCounters.charge]) (Or.inl hpositive)
    (by simpa only [Nat.cast_zero] using hcacheCount) result hresult
  have hbudget := terminalPrunedFirstLanePrefix_trace_budget table limit key computation initial
    ⟨0, 0, 0⟩ (by simp [EncodingBudgetCounters.charge]) result hresult
  dsimp only at hbudget
  omega

/-- info: 'XmssSecurity.TargetSum.CappedChain.terminalPrunedFirstLanePrefix_last_unit_requires_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminalPrunedFirstLanePrefix_last_unit_requires_activity

/-- info: 'XmssSecurity.TargetSum.CappedChain.terminalPrunedFirstLanePrefix_hazardCount_lt_of_no_activity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminalPrunedFirstLanePrefix_hazardCount_lt_of_no_activity

end XmssSecurity.TargetSum.CappedChain
