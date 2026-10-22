import Xmss.Proof.Checksum.EncodingLemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Choose a message chain whose digit changed. Its average remaining length is smaller than
the worst-case chain length, because the forged digest is sampled after the forgery is fixed. -/

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

namespace Xmss.Checksum.HiddenSibling

local instance : NeZero messageDigits := ⟨by decide⟩

/-- The first changed message digit, with zero as an unused fallback for identical words. -/
def firstMessageDifference (signed forged : Fin messageDigits → Digit) : Fin messageDigits :=
  ((List.finRange messageDigits).find? fun i => decide (signed i ≠ forged i)).getD 0

theorem firstMessageDifference_eq_zero (signed forged : Fin messageDigits → Digit)
    (h : signed 0 ≠ forged 0) : firstMessageDifference signed forged = 0 := by
  unfold firstMessageDifference
  change ((List.finRange (31 + 1)).find? fun i => decide (signed i ≠ forged i)).getD 0 = 0
  rw [List.finRange_succ]
  rw [List.find?_cons_of_pos (by simpa using h)]
  rfl

theorem firstMessageDifference_ne (signed forged : Fin messageDigits → Digit)
    (hne : signed ≠ forged) :
    signed (firstMessageDifference signed forged) ≠ forged (firstMessageDifference signed forged) := by
  unfold firstMessageDifference
  cases hfind : (List.finRange messageDigits).find? (fun i => decide (signed i ≠ forged i)) with
  | none =>
      rw [List.find?_eq_none] at hfind
      exfalso
      apply hne
      funext i
      simpa using hfind i (List.mem_finRange i)
  | some i =>
      simpa using List.find?_some hfind

/-- Distinct digests give distinct digits on the selected message chain. -/
theorem encode_firstMessageDifference_ne (signed forged : Digest) (hne : signed ≠ forged) :
    encode signed (Checksum.messageChain
        (firstMessageDifference (messageDigit signed) (messageDigit forged))) ≠
      encode forged (Checksum.messageChain
        (firstMessageDifference (messageDigit signed) (messageDigit forged))) := by
  simp only [Checksum.encode_messageChain]
  exact firstMessageDifference_ne _ _ (fun h => hne (Checksum.messageDigit_injective h))

/-- Splitting a digest into its high 124 bits and low four-bit digit. -/
def digestHighLowEquiv : (Fin (2 ^ 124) × Digit) ≃ Digest :=
  finProdFinEquiv.trans ((finCongr (by norm_num [chainLength, winternitzBits, digestBits])).trans
    BitVec.equivFin.toEquiv.symm)

theorem messageDigit_zero_highLow (high : Fin (2 ^ 124)) (low : Digit) :
    messageDigit (digestHighLowEquiv (high, low)) 0 = low := by
  apply Fin.ext
  simp only [messageDigit, winternitzBits, Fin.val_zero, Nat.mul_zero,
    BitVec.toFin_extractLsb', Nat.shiftRight_zero]
  change (low.val + 16 * high.val) % 16 = low.val
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt low.isLt

/-- Each low digit occurs exactly `2^124` times among the digests. -/
theorem sum_messageDigit_zero (f : Digit → ℕ) :
    (∑ digest : Digest, f (messageDigit digest 0)) = 2 ^ 124 * ∑ digit : Digit, f digit := by
  rw [← digestHighLowEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, messageDigit_zero_highLow]
  simp

theorem sum_digit_away_ge : ∀ excluded : Digit,
    105 ≤ ∑ digit : Digit, if digit = excluded then 0 else digit.val := by
  decide +kernel

/-- Even ignoring every digest whose first digit agrees, the selected forged digit contributes
at least `105 / 16` on average. This bound is uniform in the signed word. -/
theorem sum_firstMessageDifference_digit_ge (signed : Fin messageDigits → Digit) :
    105 * 2 ^ 124 ≤
      ∑ digest : Digest, (messageDigit digest (firstMessageDifference signed (messageDigit digest))).val := by
  calc
    _ ≤ 2 ^ 124 * ∑ digit : Digit, if digit = signed 0 then 0 else digit.val := by
      rw [Nat.mul_comm 105]
      exact Nat.mul_le_mul_left (2 ^ 124) (sum_digit_away_ge (signed 0))
    _ = ∑ digest : Digest, if messageDigit digest 0 = signed 0 then 0 else
        (messageDigit digest 0).val := (sum_messageDigit_zero _).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro digest _
      by_cases h : messageDigit digest 0 = signed 0
      · simp [h]
      · rw [if_neg h, firstMessageDifference_eq_zero signed (messageDigit digest) (Ne.symm h)]

private theorem sum_remaining_le {α : Type} [Fintype α] (f : α → ℕ)
    (hf : ∀ a, f a ≤ 48) (lower upper : ℕ)
    (hlower : lower ≤ ∑ a, f a) (hbudget : Fintype.card α * 48 ≤ upper + lower) :
    (∑ a, (48 - f a)) ≤ upper := by
  rw [Finset.sum_tsub_distrib Finset.univ (fun a _ => hf a)]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  omega

/-- The selected structural path averages at most `663 / 16 = 41.4375` queries. -/
theorem sum_firstMessageDifference_path_le (signed : Fin messageDigits → Digit) :
    (∑ digest : Digest,
      (48 - (messageDigit digest (firstMessageDifference signed (messageDigit digest))).val)) ≤
        663 * 2 ^ 124 := by
  refine sum_remaining_le _ ?_ (105 * 2 ^ 124) _ (sum_firstMessageDifference_digit_ge signed) ?_
  · intro digest
    have h := (messageDigit digest (firstMessageDifference signed (messageDigit digest))).isLt
    change _ < 16 at h
    omega
  · have hcard : Fintype.card Digest = 2 ^ 128 := by simp [digestBits]
    calc
      Fintype.card Digest * 48 = 2 ^ 128 * 48 := congrArg (· * 48) hcard
      _ ≤ _ := by norm_num

end Xmss.Checksum.HiddenSibling
