import Xmss.Proof.Generic.CappedEncodingRejection
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Generic.EncodingRejectionProbability
/-! The acceptance probability of the checksummed encoding: every digest decodes. -/

open OracleComp ENNReal
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open Xmss.Generic

namespace Xmss.Checksum

theorem validDigests_card : Code.validDigests.card = 2 ^ digestBits := by
  have huniv : Code.validDigests = Finset.univ :=
    Finset.filter_true_of_mem fun digest _ => ⟨encode digest, rfl⟩
  rw [huniv, Finset.card_univ]
  simp

/-- The digits of a codeword sum to at most `len_1 · (2^w - 1) = 480`: the checksum digits sum to
at most the checksum, which the message digits fall short of their maximum by. -/
theorem sum_digits_le (encoding : Encoding) (hvalid : Valid encoding) :
    ∑ chain, (encoding chain).val ≤ messageDigits * (chainLength - 1) := by
  have hsplit := Fin.sum_univ_add (a := messageDigits) (b := checksumDigits)
    (fun chain => (encoding chain).val)
  have hsplit' : ∑ chain, (encoding chain).val =
      ∑ i, (messagePart encoding i).val + ∑ j, (encoding (checksumChain j)).val := hsplit
  rw [hsplit']
  have hcheck : ∑ j, (encoding (checksumChain j)).val ≤ checksum (messagePart encoding) := by
    unfold Valid at hvalid
    simp only [hvalid]
    have hdigits : checksum (messagePart encoding) =
        256 * (checksumDigit (checksum (messagePart encoding)) (0 : Fin 3)).val +
          16 * (checksumDigit (checksum (messagePart encoding)) (1 : Fin 3)).val +
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

@[simp] theorem code_acceptanceProbability : Code.acceptanceProbability = 1 := by
  unfold Code.acceptanceProbability
  rw [Checksum.validDigests_card]
  exact ENNReal.div_self (by simp) (by simp)

scoped instance signerBound : Code.SignerBound where
  capped_rejection_bound_lt := by
    rw [code_acceptanceProbability]
    show (1 - 1) ^ signingAttemptLimit + (signingAttemptLimit : ℝ≥0∞) * signingAttemptLimit *
        ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ < 1 / 32
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [signingAttemptLimit, digestBits, ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_inv]

end Xmss.Checksum
