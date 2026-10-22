import Xmss.Statement.Scheme.Xmss

/-!
# XMSS with the target-sum encoding

A digest is read as 32 four-bit digits, least significant first, and decodes exactly when
their sum is 330. All 128 bits are used.
The signer tries at most `2^32` randomizers. `xmssTargetSum` is the resulting scheme.
-/

namespace Xmss

namespace TargetSum

/-- `v`: the code length, i.e. the number of chains. -/
def numChains : Nat := 32

/-- `T`: the target sum. -/
def targetSum : Nat := 330

/-- `K`: the maximum number of randomizer trials per signature. -/
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

/-- The codeword of a digest: `x_i` is the four digest bits at the digit's offset. -/
def encode (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- Decode exactly when the digit sum is `targetSum`. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if Valid (encode digest)
  then some (encode digest) else none

/-- The target-sum encoding and signing-attempt limit. -/
def wotsEncoding : WotsEncoding where
  numChains := numChains
  decodeDigest := decodeDigest
  signingAttemptLimit := signingAttemptLimit

end TargetSum

/-- XMSS with the target-sum encoding. -/
noncomputable def xmssTargetSum :=
  xmss TargetSum.wotsEncoding

end Xmss
