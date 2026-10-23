import Xmss.Proof.TargetSum.Direct.MixedEncodingProbeBound
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Average the joint prefix bound over a fresh hash output. Cached and fresh
encodings share one prefix budget, and the fallback probe pays only its acceptance rate. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.Deciding

open CappedExecution FirstLaneOracleSimulation

abbrev MixedEncodingPrefixResult :=
  (CappedExecution.ProgrammedGlobalChainKeygenView × (Forgery × CappedExecution.SourceExactTracedState)) × Digest

noncomputable def mixedEncodingPrefixProgram (adversary : Adversary) : ProbComp MixedEncodingPrefixResult := do
  let output ← ($ᵗ Digest)
  let prefixPair ← Deciding.sourcePrefixProgram adversary
  pure (prefixPair, output)

noncomputable def mixedEncodingPrefixProbability (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun pair => MixedEncodingPrefixEvent pair.1.1 pair.1.2
    (Code.decodeDigest (pair.2)) | mixedEncodingPrefixProgram adversary]

theorem mixedEncodingPrefixProbability_le (adversary : Adversary) (limit : Nat)
    (hbudget : ∀ key ∈ support CappedExecution.trajectoryProgrammedGlobalChainKeygen,
      CountedSourceBudget (Keygen.materializePrecomputation key.cache key.secretKey)
        limit (adversary.main key.publicKey) (CountedSourceState.initial key.cache)) :
    mixedEncodingPrefixProbability adversary ≤
      (limit : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞) +
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ * (TargetSum.acceptanceProbability *
          (Direct.expectedDirectEncodingQueries adversary + Direct.expectedSourceSignerHashes adversary) +
            TargetSum.acceptanceProbability) := by
  let base := (limit : ℝ≥0∞) / ((2 ^ digestBits : Nat) : ℝ≥0∞)
  let rate := ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹
  let credit := TargetSum.acceptanceProbability *
    (Direct.expectedDirectEncodingQueries adversary + Direct.expectedSourceSignerHashes adversary)
  unfold mixedEncodingPrefixProbability mixedEncodingPrefixProgram
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' output : Digest, Pr[= output | $ᵗ Digest] *
        (base + rate * (credit + if Code.ValidDigest (output) then 1 else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro output
      apply mul_le_mul' le_rfl
      simp only [bind_pure_comp, probEvent_map, Function.comp_def]
      have h := mixedEncodingPrefixEvent_probability_le_source_credit adversary limit hbudget
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

/-- info: 'Xmss.TargetSum.Deciding.mixedEncodingPrefixProbability_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mixedEncodingPrefixProbability_le

end Xmss.TargetSum.Deciding
