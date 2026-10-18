import XmssSecurity.Statement.Scheme.Xmss

/-!
# XMSS with the target-sum encoding

A digest decodes when padding bits 63 and 127 are zero and its 42 three-bit digits sum to 195.
The signer tries at most `2^32` randomizers. `xmssTargetSum` is the resulting scheme.
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

/-! ### The target-sum code -/

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

/-- Decode exactly when the padding bits are zero and the digit sum is `targetSum`. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if digest.getLsbD 63 = false ∧ digest.getLsbD 127 = false ∧ Valid (digestEncoding digest)
  then some (digestEncoding digest) else none

/-- The target-sum encoding and signing-attempt limit. -/
def wotsEncoding : WotsEncoding where
  numChains := numChains
  decode := decodeDigest
  signingAttempts := signingAttemptLimit

end TargetSum

/-- XMSS with the target-sum encoding. -/
noncomputable def xmssTargetSum :=
  xmss TargetSum.wotsEncoding

end XmssSecurity
