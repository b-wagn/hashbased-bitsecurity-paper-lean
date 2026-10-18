import XmssSecurity.Proof.TargetSum.Direct.TerminalActivityCancellation
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Charge the final prefix query and the deciding probe together to source encoding
activity, retaining the one-query saving on paths with no such activity. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Deciding

open CappedChain FirstLaneOracleSimulation

noncomputable def terminalAcceptedPrefixProbeExecution (limit : Nat) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery) :
    OracleComp CappedChain.GlobalFirstLaneWorld LimitedPrefixResult := do
  let result ← terminalPrunedFirstLanePrefix limit key computation
    (CappedChain.GlobalHighDirectTracedState.initial (CappedChain.globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩
  match result.1 with
  | none => pure result
  | some completed =>
      if (Deciding.forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1).isSome then
        let _ ← Deciding.publicDecidingProbe completed.1.epoch
          (Deciding.signedEncoding completed.2.causalState.cache key.secretKey.parameter
            completed.2.attackerTrace.toSigningLog completed.1.epoch)
          (Deciding.prefixProbeEncoding completed.2.causalState.cache key.secretKey.parameter completed.1)
          completed.1.signature.chainValue
        pure result
      else pure result

theorem terminalAcceptedPrefixProbeExecution_eager (limit : Nat) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (base : CappedChain.GlobalChainValueIndex → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery) :
    (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base) (terminalAcceptedPrefixProbeExecution limit key computation)).run =
      appendLimitedAcceptedPrefixProbe base key <$>
        (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl base) (terminalPrunedFirstLanePrefix limit key computation
          (CappedChain.GlobalHighDirectTracedState.initial (CappedChain.globalFilteredCausalKeygenState key)) ⟨0, 0, 0⟩)).run := by
  unfold terminalAcceptedPrefixProbeExecution
  simp only [simulateQ_bind, WriterT.run_bind', map_eq_bind_pure_comp]
  apply bind_congr
  rintro ⟨⟨completed, counters⟩, trace⟩
  cases completed with
  | none => simp [appendLimitedAcceptedPrefixProbe, Prod.map]
  | some completed =>
      by_cases haccepted : (Deciding.forgedEncoding completed.2.causalState.cache key.secretKey.parameter completed.1).isSome
      · simp only [haccepted, if_true, simulateQ_bind, WriterT.run_bind', Deciding.publicDecidingProbe_eager,
          pure_bind, simulateQ_pure, WriterT.run_pure, map_pure]
        simp [appendLimitedAcceptedPrefixProbe, haccepted, Deciding.prefixProbeResult, Prod.map]
      · simp [haccepted, appendLimitedAcceptedPrefixProbe, Prod.map]

noncomputable def publicTerminalAcceptedPrefixProbeExecution (limit : Nat) (adversary : Adversary)
    (key : CappedChain.ProgrammedGlobalChainKeygenView) :
    OracleComp CappedChain.GlobalFirstLaneWorld LimitedPrefixResult :=
  terminalAcceptedPrefixProbeExecution limit key (adversary.main key.publicKey)

theorem coupledTerminalAcceptedProbe_eq_map (limit : Nat) (adversary : Adversary) :
    Deciding.coupledFirstLaneProgram (publicTerminalAcceptedPrefixProbeExecution limit adversary) =
      (fun result : CoupledLimitedPrefixResult =>
        (result.1, appendLimitedAcceptedPrefixProbe result.1.2 result.1.1 result.2)) <$>
          Deciding.coupledFirstLaneProgram (publicTerminalPrefixExecution limit adversary) := by
  unfold Deciding.coupledFirstLaneProgram publicTerminalAcceptedPrefixProbeExecution publicTerminalPrefixExecution
  simp only [map_bind, map_pure, terminalAcceptedPrefixProbeExecution_eager, bind_map_left]

theorem coupledTerminalPrefix_trace_bound (limit : Nat) (adversary : Adversary)
    (result : CoupledLimitedPrefixResult)
    (hresult : result ∈ support (Deciding.coupledFirstLaneProgram (publicTerminalPrefixExecution limit adversary))) :
    FirstLaneOracleSimulation.hazardCount result.2.2 ≤ limit := by
  unfold Deciding.coupledFirstLaneProgram at hresult
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
  obtain ⟨key, _, outcome, houtcome, rfl⟩ := hresult
  have hbudget := terminalPrunedFirstLanePrefix_trace_budget key.2 limit key.1
    (adversary.main key.1.publicKey)
    (CappedChain.GlobalHighDirectTracedState.initial (CappedChain.globalFilteredCausalKeygenState key.1)) ⟨0, 0, 0⟩
    (by simp [EncodingBudgetCounters.charge]) outcome houtcome
  dsimp only at hbudget
  unfold EncodingBudgetCounters.charge at hbudget
  change FirstLaneOracleSimulation.hazardCount outcome.2 ≤ limit
  omega

theorem coupledTerminalAcceptedProbe_trace_bound (limit : Nat) (adversary : Adversary)
    (result : CoupledLimitedPrefixResult)
    (hresult : result ∈ support (Deciding.coupledFirstLaneProgram (publicTerminalAcceptedPrefixProbeExecution limit adversary))) :
    FirstLaneOracleSimulation.hazardCount result.2.2 ≤ limit + 1 := by
  rw [coupledTerminalAcceptedProbe_eq_map, support_map] at hresult
  obtain ⟨prefixResult, hprefix, rfl⟩ := hresult
  have hcount := coupledTerminalPrefix_trace_bound limit adversary prefixResult hprefix
  rw [hazardCount_appendLimitedAcceptedPrefixProbe]
  split_ifs <;> omega

theorem terminalPrefix_probe_hazardCount_le (limit : Nat) (hpositive : 0 < limit)
    (table : CappedChain.GlobalChainValueIndex → Digest) (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (result : LimitedPrefixResult × FirstLaneOracleSimulation.ActionTrace CappedChain.GlobalChainValueIndex)
    (hcount : FirstLaneOracleSimulation.hazardCount result.2 ≤ limit) :
    FirstLaneOracleSimulation.hazardCount (appendLimitedAcceptedPrefixProbe table key result).2 ≤
      (limit - 1) + if TerminalPrefixExtraCharge limit key result then 2 else 0 := by
  rw [hazardCount_appendLimitedAcceptedPrefixProbe]
  by_cases hextra : TerminalPrefixExtraCharge limit key result
  · rw [if_pos hextra]
    split_ifs <;> omega
  · have hshort : FirstLaneOracleSimulation.hazardCount result.2 < limit := by
      exact Nat.lt_of_not_ge (fun h => hextra (Or.inl h))
    have hrejected : ¬LimitedPrefixForgedEncodingAccepted key result := fun h => hextra (Or.inr h)
    rw [if_neg hextra, if_neg hrejected]
    omega

theorem expectedCoupledTerminalProbe_hazards_le (limit : Nat) (hpositive : 0 < limit)
    (adversary : Adversary) :
    expectedCoupledHazards (limit + 1) (publicTerminalAcceptedPrefixProbeExecution limit adversary) ≤
      ((limit - 1 : Nat) : ℝ≥0∞) + 2 *
        Pr[CoupledTerminalExtraCharge limit | Deciding.coupledFirstLaneProgram (publicTerminalPrefixExecution limit adversary)] := by
  unfold expectedCoupledHazards
  rw [coupledTerminalAcceptedProbe_eq_map, tsum_probOutput_map_mul, probEvent_eq_tsum_ite]
  calc
    _ ≤ ∑' result, Pr[= result | Deciding.coupledFirstLaneProgram (publicTerminalPrefixExecution limit adversary)] *
        (((limit - 1 : Nat) : ℝ≥0∞) + if CoupledTerminalExtraCharge limit result then 2 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support (Deciding.coupledFirstLaneProgram (publicTerminalPrefixExecution limit adversary))
      · apply mul_le_mul' le_rfl
        have hcount := terminalPrefix_probe_hazardCount_le limit hpositive result.1.2 result.1.1 result.2
          (coupledTerminalPrefix_trace_bound limit adversary result hresult)
        have hmin := (Nat.min_le_right (limit + 1)
          (FirstLaneOracleSimulation.hazardCount (appendLimitedAcceptedPrefixProbe result.1.2 result.1.1 result.2).2)).trans hcount
        exact_mod_cast hmin
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ = _ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul, ← ENNReal.tsum_mul_left]
      congr 1
      apply tsum_congr
      intro result
      split_ifs <;> simp [mul_comm]

theorem coupledTerminalProbedHit_probability_le (adversary : Adversary) (limit : Nat) (hpositive : 0 < limit) :
    Pr[CoupledLimitedProbedHit | Deciding.coupledFirstLaneProgram (publicTerminalPrefixExecution limit adversary)] ≤
      ((limit - 1 : Nat) : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (2 * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) *
          Pr[CoupledTerminalExtraCharge limit | Deciding.coupledFirstLaneProgram (publicTerminalPrefixExecution limit adversary)] := by
  have hevent : Pr[CoupledLimitedProbedHit |
      Deciding.coupledFirstLaneProgram (publicTerminalPrefixExecution limit adversary)] =
      Pr[fun result => FirstLaneOracleSimulation.CombinedHit result.1.2 (FirstLaneOracleSimulation.enforceHazardTrace (limit + 1) result.2.2) |
        Deciding.coupledFirstLaneProgram (publicTerminalAcceptedPrefixProbeExecution limit adversary)] := by
    calc
      _ = Pr[fun result => FirstLaneOracleSimulation.CombinedHit result.1.2 result.2.2 |
          Deciding.coupledFirstLaneProgram (publicTerminalAcceptedPrefixProbeExecution limit adversary)] := by
        rw [coupledTerminalAcceptedProbe_eq_map, probEvent_map]
        rfl
      _ = _ := by
        apply probEvent_congr' (fun result hresult => ?_) rfl
        rw [FirstLaneOracleSimulation.enforceHazardTrace_eq_self_of_count_le _ _
          (coupledTerminalAcceptedProbe_trace_bound limit adversary result hresult)]
  rw [hevent]
  apply (coupled_enforcedHit_probability_le_expected (limit + 1) _).trans
  simpa only [mul_add, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul' (le_refl (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹))
      (expectedCoupledTerminalProbe_hazards_le limit hpositive adversary)

theorem sourceCountedPrefixFirstLane_probability_le_terminal_credit
    (adversary : Adversary) (limit : Nat) (hpositive : 0 < limit)
    (hbudget : ∀ key ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    Pr[SourceCountedPrefixFirstLane | sourceCountedPrefixProgram adversary] ≤
      ((limit - 1 : Nat) : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (2 * (Direct.expectedDirectEncodingQueries adversary + Direct.expectedSourceSignerHashes adversary)) /
          ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  apply (accepted_event_probability_le_of_relTriple SourceCountedPrefixFirstLane SourceCountedPrefixEncodingActivity
    (CoupledTerminalExtraCharge limit) CoupledLimitedProbedHit _ _ (by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, digestBits])
    (terminalPrefix_activity_cancellation_coupling adversary limit hpositive hbudget)
    (coupledTerminalProbedHit_probability_le adversary limit hpositive)).trans
  simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using add_le_add
    (le_refl (((limit - 1 : Nat) : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)))
    (mul_le_mul' (le_refl (2 * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹))
      (sourceCountedPrefix_encodingActivity_probability_le adversary))

theorem acceptedPrefixFirstLane_probability_le_terminal_credit
    (adversary : Adversary) (limit : Nat) (hpositive : 0 < limit)
    (hbudget : ∀ key ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Concrete.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    Pr[fun result => AcceptedPrefixFirstLaneEvent result.1 result.2 | Deciding.sourcePrefixProgram adversary] ≤
      ((limit - 1 : Nat) : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (2 * (Direct.expectedDirectEncodingQueries adversary + Direct.expectedSourceSignerHashes adversary)) /
          ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  rw [← sourceCountedPrefixProgram_source_projection, probEvent_map]
  exact sourceCountedPrefixFirstLane_probability_le_terminal_credit adversary limit hpositive hbudget

/-- info: 'XmssSecurity.TargetSum.Deciding.acceptedPrefixFirstLane_probability_le_terminal_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms acceptedPrefixFirstLane_probability_le_terminal_credit

end XmssSecurity.TargetSum.Deciding

