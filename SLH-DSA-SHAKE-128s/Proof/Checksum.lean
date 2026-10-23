import «SLH-DSA-SHAKE-128s».Proof.Experiment
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

/-!
# Checksum arithmetic

These lemmas count the chain steps specified by Algorithm 8. Connecting this count to an
oracle implementation of the full verifier is a separate proof obligation.
-/

namespace SlhDsaSecurity.Checksum

theorem checksum_le (digits : MessageDigits) : checksum digits ≤ 480 := by
  calc
    _ ≤ ∑ _ : Fin messageDigits, (w - 1) :=
      Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)
    _ = 480 := by norm_num [messageDigits, n, winternitzBits, w]

theorem chainVerificationCalls_eq (digits : MessageDigits) :
    chainVerificationCalls digits =
      45 + 255 * (checksum digits / 256) + 15 * (checksum digits % 256 / 16) := by
  have h := checksum_le digits
  change checksum digits +
    (∑ i : Fin 3, (15 - (checksumDigit (checksum digits) i).val)) = _
  norm_num [Fin.sum_univ_succ, checksumDigit, checksumDigits, w, winternitzBits]
  omega

theorem chainVerificationCalls_bounds (digits : MessageDigits) :
    45 ≤ chainVerificationCalls digits ∧ chainVerificationCalls digits ≤ 510 := by
  rw [chainVerificationCalls_eq]
  have h := checksum_le digits
  omega

end SlhDsaSecurity.Checksum
