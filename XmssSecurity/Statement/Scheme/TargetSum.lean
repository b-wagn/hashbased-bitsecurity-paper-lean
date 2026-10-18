import XmssSecurity.Statement.Scheme.Xmss

/-!
# XMSS with the target-sum encoding

The XMSS instance of `doc/xmss/main.tex` of the leanVM repository: its code is the target-sum
code. A 128-bit digest is read as `v = 42` digits of `w = 3` bits, and it decodes to an encoding
exactly when its two padding bits are clear and the digits sum to the target sum `T = 195`. The
signer tries at most `A_max = 2^32` randomizers.

| Symbol  | Lean                  | Value   | Meaning                                 |
|---------|-----------------------|---------|-----------------------------------------|
| `v`     | `numChains`           | 42      | code length (number of chains)          |
| `T`     | `targetSum`           | 195     | target sum                              |
| `A_max` | `signingAttemptLimit` | `2^32`  | maximum randomizer trials per signature |

`xmssTargetSum` is the resulting scheme.
-/

namespace XmssSecurity

namespace TargetSum

/-- `v`: the code length, i.e. the number of chains. -/
def numChains : Nat := 42

/-- `T`: the target sum. -/
def targetSum : Nat := 195

/-- `A_max`: the maximum number of randomizer trials per signature. -/
def signingAttemptLimit : Nat := 2 ^ 32

abbrev ChainIndex := Fin numChains
abbrev Encoding := ChainIndex → Digit

/-! ### The target-sum code

`v = 42` chunks of `w = 3` bits, 21 in each half of the digest, one pinned bit per half, and the
code is the words of digit sum `T = 195`. -/

/-- The digit sum of a word. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- Membership in the code `C`: digit sum `T`. -/
def Valid (x : Encoding) : Prop := sum x = targetSum

instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))

/-- `v / 2 = 21` digits in each half of the digest. -/
def digitsPerHalf : Nat := numChains / 2

/-- Offset of a three-bit digit, skipping padding bits 63 and 127. -/
def digitOffset (i : ChainIndex) : Nat :=
  winternitzBits * i.val + if i.val < digitsPerHalf then 0 else 1

/-- `x_i`, the three bits of the digest at the digit's offset. -/
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- Decode the concrete little-endian layout used by `IncEnc`: 21 three-bit digits, padding bit 63, 21 digits, and padding bit 127. A digest decodes exactly when both padding bits are clear and the digits reach the target sum. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if digest.getLsbD 63 = false ∧ digest.getLsbD 127 = false ∧ Valid (digestEncoding digest)
  then some (digestEncoding digest) else none

/-- The target-sum encoding: `v = 42` chains, the target-sum decoder, and `A_max = 2^32`
randomizer trials. -/
def wotsEncoding : WotsEncoding where
  numChains := numChains
  decode := decodeDigest
  signingAttempts := signingAttemptLimit

end TargetSum

/-- XMSS with the target-sum encoding. -/
noncomputable def xmssTargetSum :=
  xmss TargetSum.wotsEncoding

end XmssSecurity
