import XmssSecurity.Proof.TargetSum.EUFCMA.FreshMixedFirstLane
import XmssSecurity.Proof.TargetSum.EUFCMA.FreshExpectedPrefix
import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsTerminalFirstLane
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Average the shared prefix over the verifier's fresh encoding. Rejected
fallbacks retain the cached-prefix bound; accepted fallbacks cost one probe. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding

theorem freshMixedPrefixProbability_le_of_cached (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (base credit extra : ℝ≥0∞)
    (hcached : Pr[fun result => FreshPrefixFirstLaneEvent result.1 result.2 | Deciding.sourcePrefixProgram adversary] ≤
      base + credit)
    (hgeneral : ((D + 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) ≤ base + extra) :
    freshMixedPrefixProbability adversary ≤ base + credit + TargetSum.acceptanceProbability * extra := by
  unfold freshMixedPrefixProbability mixedEncodingPrefixProgram
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' output : HashOutput, Pr[= output | $ᵗ HashOutput] *
        (base + credit + if Code.ValidDigest (Generic.truncateHash output) then extra else 0) := by
      apply ENNReal.tsum_le_tsum
      intro output
      apply mul_le_mul' le_rfl
      simp only [bind_pure_comp, probEvent_map, Function.comp_def]
      by_cases hvalid : Code.ValidDigest (Generic.truncateHash output)
      · rw [if_pos hvalid]
        apply le_trans (probEvent_mono'' (fun _ h => h.2))
        apply (mixedPrefix_probability_le_direct adversary D hD _).trans
        exact hgeneral.trans (by simp only [add_assoc]; exact add_le_add le_rfl (le_add_left le_rfl))
      · rw [if_neg hvalid, add_zero]
        have hnone : Code.decodeDigest (Generic.truncateHash output) = none := by
          cases hdecode : Code.decodeDigest (Generic.truncateHash output) with
          | none => rfl
          | some encoding => exact (hvalid ⟨encoding, hdecode⟩).elim
        simp only [hnone]
        refine (le_of_eq ?_).trans hcached
        congr 1
        funext result
        exact propext (freshMixedPrefixEvent_none result.1 result.2)
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]
      congr 1
      rw [← TargetSum.probEvent_validDigest_uniformHashOutput, probEvent_eq_tsum_ite,
        ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro output
      split_ifs <;> simp only [mul_zero, zero_mul]

theorem freshMixedPrefixProbability_le_expected (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    freshMixedPrefixProbability adversary ≤
      (D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (TargetSum.acceptanceProbability * (Direct.expectedDirectEncodingQueries adversary + 1)) /
          ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  have h := freshMixedPrefixProbability_le_of_cached adversary D hD
    ((D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))
    ((TargetSum.acceptanceProbability * Direct.expectedDirectEncodingQueries adversary) /
      ((2 ^ digestBits : ℕ) : ℝ≥0∞))
    (1 / ((2 ^ digestBits : ℕ) : ℝ≥0∞))
    (freshPrefixFirstLane_probability_le_expected adversary D hD)
    (by simp only [Nat.cast_add, Nat.cast_one, ENNReal.add_div]; exact le_rfl)
  apply h.trans_eq
  simp only [div_eq_mul_inv]
  ring

theorem freshMixedPrefixProbability_le_terminal (adversary : Adversary) (q : ℕ)
    (hpositive : 0 < q) (hbound : Requests.IsQueryBound adversary q) :
    freshMixedPrefixProbability adversary ≤
      ((q - 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (2 * Direct.expectedDirectEncodingQueries adversary + 2 * TargetSum.acceptanceProbability) /
          ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  have h := freshMixedPrefixProbability_le_of_cached adversary q hbound.direct
    (((q - 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))
    ((2 * Direct.expectedDirectEncodingQueries adversary) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))
    (2 / ((2 ^ digestBits : ℕ) : ℝ≥0∞))
    (Requests.freshPrefixFirstLane_probability_le_terminal adversary q hpositive hbound)
    (by
      rw [show q + 1 = (q - 1) + 2 by omega]
      simp only [Nat.cast_add, Nat.cast_ofNat, ENNReal.add_div]; exact le_rfl)
  apply h.trans_eq
  simp only [div_eq_mul_inv]
  ring

/-- info: 'XmssSecurity.TargetSum.EUFCMA.freshMixedPrefixProbability_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshMixedPrefixProbability_le_expected

/-- info: 'XmssSecurity.TargetSum.EUFCMA.freshMixedPrefixProbability_le_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshMixedPrefixProbability_le_terminal

end XmssSecurity.TargetSum.EUFCMA
