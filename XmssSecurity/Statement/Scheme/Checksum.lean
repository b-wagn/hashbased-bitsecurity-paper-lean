import XmssSecurity.Statement.Scheme.Xmss

/-!
# The WOTS encoding with a checksum

A digest gives 32 four-bit message digits, least significant first. Append the three
base-16 digits of `Σ (15 - x_i)`, most significant first, giving 35 chains.
This uses the WOTS checksum construction of FIPS 205 with this instance's message-digit layout. Every digest encodes, so signing needs one attempt.
-/

namespace XmssSecurity

namespace Checksum

/-- `len_1 = ⌈n / w⌉`: the number of digits of the message digest. -/
def messageDigits : Nat := 32

/-- `len_2 = ⌊log_{2^w}(len_1 · (2^w - 1))⌋ + 1`: the number of checksum digits. -/
def checksumDigits : Nat := 3

/-- `v = len_1 + len_2 = 35`: the code length, i.e. the number of chains. The first `len_1`
chains carry the message digits and the last `len_2` the checksum digits. -/
def numChains : Nat := 35

abbrev ChainIndex := Fin numChains
abbrev Encoding := ChainIndex → Digit

/-- Message digit `i`: the four digest bits at offset `4i`. -/
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

/-- The checksummed encoding: `v = 35` chains, every digest decodes, and a single randomizer
trial. -/
def wotsEncoding : WotsEncoding where
  numChains := numChains
  decode := fun digest => some (encode digest)
  signingAttempts := 1

end Checksum

/-- XMSS with the WOTS encoding with a checksum. -/
noncomputable def xmssChecksum :=
  xmss Checksum.wotsEncoding

end XmssSecurity
