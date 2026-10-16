import XmssSecurity.Proof.EUFCMA.FreshMixedFirstLane
import XmssSecurity.Proof.EUFCMA.FreshExpectedPrefix
import XmssSecurity.Proof.EUFCMA.RequestsTerminalFirstLane

/-! Average the shared prefix over the verifier's fresh encoding. Rejected
fallbacks retain the cached-prefix bound; accepted fallbacks cost one probe. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.EUFCMA

open Concrete CappedChain Deciding

theorem freshMixedPrefixProbability_le_of_cached (adversary : XmssSecurity.Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (base credit extra : ℝ≥0∞)
    (hcached : Pr[fun result => FreshPrefixFirstLaneEvent result.1 result.2 | sourcePrefixProgram adversary] ≤
      base + credit)
    (hgeneral : ((D + 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) ≤ base + extra) :
    freshMixedPrefixProbability adversary ≤ base + credit + Checksum.acceptanceProbability * extra := by
  unfold freshMixedPrefixProbability mixedEncodingPrefixProgram
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' output : HashOutput, Pr[= output | $ᵗ HashOutput] *
        (base + credit + if Checksum.ValidDigest (truncateHash output) then extra else 0) := by
      apply ENNReal.tsum_le_tsum
      intro output
      apply mul_le_mul' le_rfl
      simp only [bind_pure_comp, probEvent_map, Function.comp_def]
      by_cases hvalid : Checksum.ValidDigest (truncateHash output)
      · rw [if_pos hvalid]
        apply le_trans (probEvent_mono'' (fun _ h => h.2))
        apply (mixedPrefix_probability_le_direct adversary D hD _).trans
        exact hgeneral.trans (by simp only [add_assoc]; exact add_le_add le_rfl (le_add_left le_rfl))
      · rw [if_neg hvalid, add_zero]
        have hnone : Checksum.decodeDigest (truncateHash output) = none := by
          cases hdecode : Checksum.decodeDigest (truncateHash output) with
          | none => rfl
          | some encoding => exact (hvalid ⟨encoding, hdecode⟩).elim
        simpa only [hnone, freshMixedPrefixEvent_none] using hcached
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
        tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]
      congr 1
      rw [← Checksum.probEvent_validDigest_uniformHashOutput, probEvent_eq_tsum_ite,
        ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro output
      split_ifs <;> simp only [mul_zero, zero_mul]

theorem freshMixedPrefixProbability_le_expected (adversary : XmssSecurity.Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    freshMixedPrefixProbability adversary ≤
      (D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (Checksum.acceptanceProbability * (Direct.expectedDirectEncodingQueries adversary + 1)) /
          ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  have h := freshMixedPrefixProbability_le_of_cached adversary D hD
    ((D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))
    ((Checksum.acceptanceProbability * Direct.expectedDirectEncodingQueries adversary) /
      ((2 ^ digestBits : ℕ) : ℝ≥0∞))
    (1 / ((2 ^ digestBits : ℕ) : ℝ≥0∞))
    (freshPrefixFirstLane_probability_le_expected adversary D hD)
    (by simp only [Nat.cast_add, Nat.cast_one, ENNReal.add_div]; exact le_rfl)
  apply h.trans_eq
  simp only [div_eq_mul_inv]
  ring

theorem freshMixedPrefixProbability_le_terminal (adversary : XmssSecurity.Adversary) (q : ℕ)
    (hpositive : 0 < q) (hbound : Requests.IsQueryBound adversary q) :
    freshMixedPrefixProbability adversary ≤
      ((q - 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (2 * Direct.expectedDirectEncodingQueries adversary + 2 * Checksum.acceptanceProbability) /
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

/-- info: 'XmssSecurity.EUFCMA.freshMixedPrefixProbability_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshMixedPrefixProbability_le_expected

/-- info: 'XmssSecurity.EUFCMA.freshMixedPrefixProbability_le_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshMixedPrefixProbability_le_terminal

end XmssSecurity.EUFCMA
