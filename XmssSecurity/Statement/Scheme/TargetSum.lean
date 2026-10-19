import XmssSecurity.Statement.Scheme.Xmss

/-!
# XMSS with the target-sum encoding

A digest is read as 32 four-bit digits and decodes exactly when their sum is 330.
The signer tries at most `2^32` randomizers. `xmssTargetSum` is the resulting scheme.
-/

namespace XmssSecurity

namespace TargetSum

/-- `v`: the code length, i.e. the number of chains. -/
def numChains : Nat := 32

/-- `T`: the target sum. -/
def targetSum : Nat := 330

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

/-- Offset of a four-bit digit in the digest. -/
def digitOffset (i : ChainIndex) : Nat :=
  winternitzBits * i.val

/-- `x_i`, the four bits of the digest at the digit's offset. -/
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- Decode exactly when the digit sum is `targetSum`. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if Valid (digestEncoding digest)
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
