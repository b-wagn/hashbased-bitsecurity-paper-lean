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

def CoupledLimitedPrefixAccepted (result : CoupledLimitedPrefixResult) : Prop :=
  LimitedPrefixForgedEncodingAccepted result.1.1.1 result.2

def CoupledLimitedPrefixHit (result : CoupledLimitedPrefixResult) : Prop :=
  CombinedHit result.1.1.2 result.2.2

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

theorem coupledLimitedPrefix_hit_probability_le (limit : Nat) (adversary : Adversary) :
    Pr[CoupledLimitedPrefixHit | coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary)] ≤
      (limit : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  calc
    _ = Pr[fun result => CombinedHit result.1.1.2 (enforceHazardTrace limit result.2.2) |
        coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary)] := by
      apply probEvent_congr' (fun result hresult => ?_) rfl
      rw [enforceHazardTrace_eq_self_of_count_le _ _ (coupledLimitedPrefix_trace_bound limit adversary result hresult)]
      rfl
    _ ≤ ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ *
        expectedCoupledHazards limit (publicLimitedPrefixExecution limit adversary) :=
      coupled_enforcedHit_probability_le_expected limit _
    _ ≤ _ := by
      simpa only [div_eq_mul_inv, mul_comm] using
        mul_le_mul' (le_refl (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹)) (expectedCoupledHazards_le limit _)

theorem coupledLimitedAcceptedProbe_eq_map (limit : Nat) (adversary : Adversary) :
    coupledFirstLaneProgram (publicLimitedAcceptedPrefixProbeExecution limit adversary) =
      (fun result : CoupledLimitedPrefixResult =>
        (result.1, appendLimitedAcceptedPrefixProbe result.1.1.2 result.1.1.1 result.2)) <$>
          coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary) := by
  unfold coupledFirstLaneProgram publicLimitedAcceptedPrefixProbeExecution publicLimitedPrefixExecution
  simp only [map_bind, map_pure, limitedAcceptedPrefixProbeExecution_eager, bind_map_left]

theorem expectedCoupledLimitedProbe_hazards_le (limit : Nat) (adversary : Adversary) :
    expectedCoupledHazards (limit + 1) (publicLimitedAcceptedPrefixProbeExecution limit adversary) ≤
      (limit : ℝ≥0∞) +
        Pr[CoupledLimitedPrefixAccepted | coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary)] := by
  classical
  unfold expectedCoupledHazards
  rw [coupledLimitedAcceptedProbe_eq_map, tsum_probOutput_map_mul, probEvent_eq_tsum_ite]
  calc
    _ ≤ ∑' result, Pr[= result | coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary)] *
        ((limit : ℝ≥0∞) + if CoupledLimitedPrefixAccepted result then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support (coupledFirstLaneProgram (publicLimitedPrefixExecution limit adversary))
      · apply mul_le_mul' le_rfl
        have hcount := coupledLimitedPrefix_trace_bound limit adversary result hresult
        rw [hazardCount_appendLimitedAcceptedPrefixProbe]
        change ((min (limit + 1) (hazardCount result.2.2 +
          if CoupledLimitedPrefixAccepted result then 1 else 0) : Nat) : ℝ≥0∞) ≤ _
        split_ifs <;> exact_mod_cast (by omega : min (limit + 1) (hazardCount result.2.2 + _) ≤ limit + _)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ = _ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]
      congr 1
      apply tsum_congr
      intro result
      split_ifs <;> simp

/-- info: 'XmssSecurity.TargetSum.Deciding.expectedCoupledLimitedProbe_hazards_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expectedCoupledLimitedProbe_hazards_le

/-- info: 'XmssSecurity.TargetSum.Deciding.coupledLimitedPrefix_hit_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coupledLimitedPrefix_hit_probability_le

end XmssSecurity.TargetSum.Deciding
