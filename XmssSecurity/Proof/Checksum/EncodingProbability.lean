import XmssSecurity.Proof.Checksum.CappedEncodingRejection

/-! The acceptance probability of the checksummed encoding: every digest decodes. -/

open OracleComp ENNReal
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.Checksum

/-- Every digest encodes, so a uniform digest is accepted with probability one. -/
noncomputable def acceptanceProbability : ℝ≥0∞ := 1

theorem probEvent_validDigest_uniform :
    Pr[ValidDigest | $ᵗ Digest] = acceptanceProbability := by
  rw [probEvent_uniformSample]
  change (validDigests.card : ℝ≥0∞) / Fintype.card Digest = _
  rw [validDigests_card]
  simp [acceptanceProbability, ENNReal.div_self]

theorem acceptanceProbability_pos : 0 < acceptanceProbability := by
  simp [acceptanceProbability]

theorem acceptanceProbability_ne_top : acceptanceProbability ≠ ⊤ := by
  simp [acceptanceProbability]

theorem acceptanceProbability_eq_one : acceptanceProbability = 1 := rfl

/-- The digits of a codeword sum to at most `len_1 · (2^w - 1) = 301`: the checksum digits sum to
at most the checksum, which the message digits fall short of their maximum by. -/
theorem sum_digits_le (encoding : Encoding) (hvalid : Valid encoding) :
    ∑ chain, (encoding chain).val ≤ messageDigits * (chainLength - 1) := by
  have hsplit := Fin.sum_univ_add (a := messageDigits) (b := checksumDigits)
    (fun chain => (encoding chain).val)
  have hsplit' : ∑ chain, (encoding chain).val =
      ∑ i, (messagePart encoding i).val + ∑ j, (encoding (checksumChain j)).val := hsplit
  rw [hsplit']
  have hcheck : ∑ j, (encoding (checksumChain j)).val ≤ checksum (messagePart encoding) := by
    simp only [hvalid.2]
    have hdigits : checksum (messagePart encoding) =
        64 * (checksumDigit (checksum (messagePart encoding)) (0 : Fin 3)).val +
          8 * (checksumDigit (checksum (messagePart encoding)) (1 : Fin 3)).val +
            (checksumDigit (checksum (messagePart encoding)) (2 : Fin 3)).val :=
      checksum_eq_digits (checksum (messagePart encoding)) (checksum_lt_pow _)
    change ∑ j : Fin 3, (checksumDigit (checksum (messagePart encoding)) j).val ≤ _
    rw [Fin.sum_univ_three]
    omega
  have htotal : ∑ i, (messagePart encoding i).val + checksum (messagePart encoding) =
      messageDigits * (chainLength - 1) := by
    unfold checksum
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _i : Fin messageDigits, (chainLength - 1) := by
        apply Finset.sum_congr rfl
        intro i _
        have := (messagePart encoding i).isLt
        simp only [chainLength, winternitzBits] at *
        omega
      _ = _ := by simp
  omega

end XmssSecurity.Checksum.Checksum
