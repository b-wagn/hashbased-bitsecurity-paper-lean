import XmssSecurity.Statement.Scheme.Types

/-!
# The WOTS encoding with a checksum

The code of the XMSS instance, as in SLH-DSA (FIPS 205, Algorithms 7 and 8): a 128-bit digest is
read as `len_1 = 43` digits of `w = 3` bits, and the checksum `csum = Σ (2^w - 1 - x_i)` of these
digits is appended as `len_2 = 3` further digits. Every digest encodes; signing makes a single
attempt.

Digits are read in the little-endian layout of this instance: message digit `i` consists of the
digest bits `3i, 3i + 1, 3i + 2`, least significant first. The last message digit has only the
two bits `126` and `127`, the missing top bit counting as zero (`len_1 = ⌈128 / 3⌉`). The checksum
digits are the base-`2^w` digits of `csum`, most significant first. This is what FIPS 205 obtains
by shifting `csum` left by `(8 - (len_2 · w) mod 8) mod 8 = 7` bits, serializing it as two bytes,
and reading `len_2` digits with `base_2b`.
-/

namespace XmssSecurity

namespace Checksum

/-- Message digit `i`: the three digest bits at offset `3i` (bits beyond the digest are zero). -/
def messageDigit (digest : Digest) (i : Fin messageDigits) : Digit :=
  (digest.extractLsb' (winternitzBits * i.val) winternitzBits).toFin

/-- `csum = Σ_i (2^w - 1 - x_i)` over the message digits. -/
def checksum (digits : Fin messageDigits → Digit) : Nat :=
  ∑ i, (chainLength - 1 - (digits i).val)

/-- Checksum digit `j`: the base-`2^w` digit of `csum` of weight `(2^w)^(len_2 - 1 - j)`. -/
def checksumDigit (csum : Nat) (j : Fin checksumDigits) : Digit :=
  ⟨csum / chainLength ^ (checksumDigits - 1 - j.val) % chainLength,
    Nat.mod_lt _ (by decide)⟩

/-- The codeword of a digest: the message digits on the first `len_1` chains, followed by the
checksum digits on the last `len_2` chains. -/
def encode (digest : Digest) : Encoding := fun i =>
  if h : i.val < messageDigits then messageDigit digest ⟨i.val, h⟩
  else checksumDigit (checksum (messageDigit digest))
    ⟨i.val - messageDigits, by have := i.isLt; simp only [numChains, messageDigits, checksumDigits] at *; omega⟩

end Checksum

end XmssSecurity
