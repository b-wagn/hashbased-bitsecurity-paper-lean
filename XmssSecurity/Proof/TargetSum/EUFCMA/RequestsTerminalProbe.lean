import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsPublicTrace
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The stopped prefix and its fresh deciding probe spend at most q-1 hazards,
plus two opportunities only on a branch showing activity or a fresh encoding. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

namespace XmssSecurity.TargetSum.EUFCMA.Requests
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding FirstLaneOracleSimulation

def PublicExtra (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (result : Generic.Forgery × Generic.CappedChain.GlobalHighDirectTracedState) : Prop :=
  encodingActive key.secretKey.parameter result.2.attackerTrace = true ∨ PublicFreshAccepted key result

def CoupledExtra (result : Generic.Deciding.BaseHighKey ×
    ((Generic.Forgery × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)) : Prop :=
  PublicExtra result.1.1.1 result.2.1

theorem public_stopped_probe_hazards_le (adversary : Generic.Adversary) (q : ℕ) (hpositive : 0 < q)
    (hbound : IsQueryBound adversary q) (table : Generic.CappedChain.GlobalChainValueIndex → Digest)
    (key : Generic.CappedChain.ProgrammedGlobalChainKeygenView) (hparameter : key.publicKey.parameter = key.secretKey.parameter)
    (edgeHigh : Generic.CappedChain.GlobalChainEdgeIndex → Digest)
    (result : (Generic.Forgery × Generic.CappedChain.GlobalHighDirectTracedState) × Generic.FirstLaneOracleSimulation.ActionTrace Generic.CappedChain.GlobalChainValueIndex)
    (hresult : result ∈ support ((simulateQ (Generic.FirstLaneOracleSimulation.eagerTraceImpl table)
      (Generic.Deciding.publicPrefixExecution (stoppedAdversary q adversary) key edgeHigh)).run)) :
    Generic.FirstLaneOracleSimulation.hazardCount (appendFreshPrefixProbe q table key result).2 ≤
      (q - 1) + if PublicExtra key result.1 then 2 else 0 := by
  have h := public_stopped_hazards_le_encoding adversary q hpositive hbound table key hparameter edgeHigh result hresult
  rw [hazardCount_appendFreshPrefixProbe]
  by_cases hextra : PublicExtra key result.1
  · rw [if_pos hextra]
    split_ifs at h ⊢ <;> omega
  · have hinactive : encodingActive key.secretKey.parameter result.1.2.attackerTrace = false :=
      Bool.eq_false_iff.mpr (fun h => hextra (Or.inl h))
    have hrejected : ¬PublicFreshAccepted key result.1 := fun h => hextra (Or.inr h)
    simp only [if_neg hextra, if_neg hrejected, hinactive, Bool.false_eq_true, if_false, Nat.add_zero] at h ⊢
    exact (Nat.min_le_right _ _).trans h

theorem expected_stopped_probe_hazards_le (adversary : Generic.Adversary) (q : ℕ) (hpositive : 0 < q)
    (hbound : IsQueryBound adversary q) :
    expectedCoupledHazards (q + 1) (publicFreshPrefixProbeExecution q (stoppedAdversary q adversary)) ≤
      ((q - 1 : ℕ) : ℝ≥0∞) +
        2 * Pr[CoupledExtra | Generic.Deciding.coupledFirstLaneProgram (Generic.Deciding.publicPrefixExecution (stoppedAdversary q adversary))] := by
  unfold expectedCoupledHazards
  rw [coupledFreshPrefixProbe_eq_map, tsum_probOutput_map_mul, probEvent_eq_tsum_ite]
  calc
    _ ≤ ∑' result, Pr[= result | Generic.Deciding.coupledFirstLaneProgram (Generic.Deciding.publicPrefixExecution (stoppedAdversary q adversary))] *
        (((q - 1 : ℕ) : ℝ≥0∞) + if CoupledExtra result then 2 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support
          (Generic.Deciding.coupledFirstLaneProgram (Generic.Deciding.publicPrefixExecution (stoppedAdversary q adversary)))
      · apply mul_le_mul' le_rfl
        unfold Generic.Deciding.coupledFirstLaneProgram at hresult
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hresult
        obtain ⟨key, hkey, outcome, houtcome, rfl⟩ := hresult
        have hkey' := Generic.CappedChain.coupledGlobalChainKeygenWithBaseHighFull_support_keyView key hkey
        have hparameter : key.1.1.publicKey.parameter = key.1.1.secretKey.parameter :=
          Generic.CappedChain.keygen_parameter_eq key.1.1.keyResult (Generic.CappedChain.trajectoryProgrammedGlobalChainKeygen_support_keyResult _ hkey')
        have h := (Nat.min_le_right (q + 1) _).trans
          (public_stopped_probe_hazards_le adversary q hpositive hbound key.1.2 key.1.1 hparameter key.2 outcome houtcome)
        exact_mod_cast h
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ = _ := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul, ← ENNReal.tsum_mul_left]
      congr 1
      apply tsum_congr
      intro result
      split_ifs <;> simp [mul_comm]

theorem stopped_probedHit_probability_le (adversary : Generic.Adversary) (q : ℕ) (hpositive : 0 < q)
    (hbound : IsQueryBound adversary q) :
    Pr[CoupledFreshProbedHit q | Generic.Deciding.coupledFirstLaneProgram (Generic.Deciding.publicPrefixExecution (stoppedAdversary q adversary))] ≤
      ((q - 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (2 * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) *
          Pr[CoupledExtra | Generic.Deciding.coupledFirstLaneProgram (Generic.Deciding.publicPrefixExecution (stoppedAdversary q adversary))] := by
  have hhit : Pr[CoupledFreshProbedHit q |
      Generic.Deciding.coupledFirstLaneProgram (Generic.Deciding.publicPrefixExecution (stoppedAdversary q adversary))] =
      Pr[fun result => Generic.FirstLaneOracleSimulation.CombinedHit result.1.1.2 (Generic.FirstLaneOracleSimulation.enforceHazardTrace (q + 1) result.2.2) |
        Generic.Deciding.coupledFirstLaneProgram (publicFreshPrefixProbeExecution q (stoppedAdversary q adversary))] := by
    rw [coupledFreshPrefixProbe_eq_map, probEvent_map]
    apply probEvent_congr' (fun result _ => ?_) rfl
    simp only [Function.comp_def]
    rw [Generic.FirstLaneOracleSimulation.enforceHazardTrace_eq_self_of_count_le _ _ (hazardCount_appendFreshPrefixProbe_le q _ _ _)]
    rfl
  rw [hhit]
  apply (coupled_enforcedHit_probability_le_expected (q + 1) _).trans
  simpa only [div_eq_mul_inv, mul_add, mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul' (le_refl (((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹))
      (expected_stopped_probe_hazards_le adversary q hpositive hbound)

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.stopped_probedHit_probability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stopped_probedHit_probability_le

end XmssSecurity.TargetSum.EUFCMA.Requests
