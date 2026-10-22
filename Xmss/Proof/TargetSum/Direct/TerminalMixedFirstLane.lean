import Xmss.Proof.TargetSum.Direct.TerminalActivityBound
import Xmss.Proof.TargetSum.Direct.MixedFirstLane
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Average the terminal saving over the independently sampled fallback encoding.
Invalid fallback encodings use the sharper cached-prefix bound. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Deciding

open CappedExecution FirstLaneOracleSimulation Direct

theorem mixedEncodingPrefixEvent_probability_le_terminal_credit
    (adversary : Adversary) (limit : Nat) (hpositive : 0 < limit)
    (hbudget : ∀ key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Keygen.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) (fallback : Option Encoding) :
    Pr[fun result => MixedEncodingPrefixEvent result.1 result.2 fallback | Deciding.sourcePrefixProgram adversary] ≤
      ((limit - 1 : Nat) : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (2 * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) *
          (Direct.expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary +
            if fallback.isSome then 1 else 0) := by
  cases fallback with
  | none =>
      simpa [MixedEncodingPrefixEvent, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        acceptedPrefixFirstLane_probability_le_terminal_credit adversary limit hpositive hbudget
  | some encoding =>
      have hbound := mixedEncodingPrefixEvent_probability_le adversary limit hbudget (some encoding)
      simp only [Option.isSome_some, or_true] at hbound
      simp at hbound
      simp only [Option.isSome_some, if_true]
      have hlimit : (limit : ℝ≥0∞) = ((limit - 1 : Nat) : ℝ≥0∞) + 1 := by
        exact_mod_cast (Nat.sub_add_cancel hpositive).symm
      apply hbound.trans
      calc
        _ = ((limit - 1 : Nat) : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
            (2 * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) * 1 := by
          rw [hlimit]
          simp only [div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat]
          ring
        _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl (le_add_left le_rfl))


theorem mixedEncodingPrefixProbability_le_terminal_credit (adversary : Adversary) (limit : Nat) (hpositive : 0 < limit)
    (hbudget : ∀ key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Keygen.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    mixedEncodingPrefixProbability adversary ≤
      ((limit - 1 : Nat) : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        (2 * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) *
          (Direct.expectedDirectEncodingQueries adversary + Direct.expectedSourceSignerHashes adversary +
            TargetSum.acceptanceProbability) := by
  let base := ((limit - 1 : Nat) : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)
  let rate := 2 * ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
  let credit := Direct.expectedDirectEncodingQueries adversary + Direct.expectedSourceSignerHashes adversary
  unfold mixedEncodingPrefixProbability mixedEncodingPrefixProgram
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' output : Digest, Pr[= output | $ᵗ Digest] *
        (base + rate * (credit + if Code.ValidDigest (output) then 1 else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro output
      apply mul_le_mul' le_rfl
      simp only [bind_pure_comp, probEvent_map, Function.comp_def]
      have h := mixedEncodingPrefixEvent_probability_le_terminal_credit adversary limit hpositive hbudget
        (Code.decodeDigest (output))
      have hvalid : (Code.decodeDigest (output)).isSome ↔
          Code.ValidDigest (output) := Option.isSome_iff_exists
      simp only [hvalid] at h
      exact h
    _ = base + rate * (credit + TargetSum.acceptanceProbability) := by
      rw [mul_add]
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]
      congr 1
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]
      congr 1
      rw [← TargetSum.probEvent_validDigest_uniform, probEvent_eq_tsum_ite,
        ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro output
      split_ifs <;> simp only [mul_one, mul_zero]
      exact mul_comm _ _

theorem decidingFirstLane_probability_le_terminal_credit
    (adversary : Adversary) (limit : Nat) (hpositive : 0 < limit)
    (hbudget : ∀ key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Keygen.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    Pr[Deciding.WinningDecidingFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] ≤
      ((limit - 1 : Nat) : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        ((2 + TargetSum.acceptanceProbability) *
          (Direct.expectedDirectEncodingQueries adversary + expectedSourceSignerHashes adversary) +
            2 * TargetSum.acceptanceProbability) / ((2 ^ digestBits : Nat) : ℝ≥0∞) := by
  apply (decidingFirstLane_probability_le_mixed_add_encoding adversary).trans
  apply (add_le_add (mixedEncodingPrefixProbability_le_terminal_credit adversary limit hpositive hbudget)
    (freshSourceEncodingProbability_le_source_credit adversary)).trans_eq
  simp only [div_eq_mul_inv]
  ring

/-- info: 'Xmss.TargetSum.Deciding.decidingFirstLane_probability_le_terminal_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decidingFirstLane_probability_le_terminal_credit

end Xmss.TargetSum.Deciding

