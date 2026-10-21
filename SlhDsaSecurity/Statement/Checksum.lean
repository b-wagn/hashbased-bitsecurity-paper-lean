import SlhDsaSecurity.Statement.Types
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Standard WOTS+ checksum

FIPS 205, Algorithms 7 and 8: read message nibbles most significant first, then append
the three most significant nibbles of the two-byte, left-shifted checksum. Equivalently,
append the three base-16 digits of the unshifted checksum, most significant first.
-/

namespace SlhDsaSecurity

abbrev Digit := Fin w
abbrev MessageDigits := Fin messageDigits → Digit
abbrev Encoding := Fin chains → Digit

namespace Checksum

def messageDigit (message : Digest) (i : Fin messageDigits) : Digit :=
  (message.extractLsb' (winternitzBits * (messageDigits - 1 - i.val)) winternitzBits).toFin

def checksum (digits : MessageDigits) : Nat := ∑ i, (w - 1 - (digits i).val)

def checksumDigit (csum : Nat) (i : Fin checksumDigits) : Digit :=
  ⟨csum / w ^ (checksumDigits - 1 - i.val) % w, Nat.mod_lt _ (by decide)⟩

def encode (message : Digest) : Encoding := fun i =>
  if h : i.val < messageDigits then messageDigit message ⟨i.val, h⟩
  else checksumDigit (checksum (messageDigit message))
    ⟨i.val - messageDigits, by have := i.isLt; simp only [chains] at *; omega⟩

/-- Number of calls to F in Algorithm 8, before the final WOTS public-key compression. -/
def chainVerificationCalls (digits : MessageDigits) : Nat :=
  (∑ i, (w - 1 - (digits i).val)) +
    ∑ i : Fin checksumDigits, (w - 1 - (checksumDigit (checksum digits) i).val)

end Checksum
end SlhDsaSecurity
