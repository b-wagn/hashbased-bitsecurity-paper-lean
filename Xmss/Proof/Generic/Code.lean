import Xmss.Statement.Scheme.Xmss
import Mathlib.Data.BitVec

/-!
# The WOTS code, as the proofs use it

The proofs under `Proof/Generic/` hold for any WOTS code with the properties of the class `Code`:
a partial decoder from digests to codewords that is injective where it decodes, codewords that do
not dominate one another, a bound on the chain steps one verification walks, and some digest that
decodes. The target-sum code (`Proof/TargetSum/Code.lean`) and the checksummed code
(`Proof/Checksum/Code.lean`) are its two instances.
-/

open OracleComp ENNReal
open scoped BigOperators

namespace Xmss.Generic

/-- A WOTS code with the properties the proofs use. -/
class Code where
  /-- `v`, the number of chains. -/
  numChains : Nat
  numChains_pos : 0 < numChains
  /-- Chain tweaks carry `2^w · i + step` in 32 bits. -/
  numChains_lt : numChains < 2 ^ 28
  /-- The partial decoder from digests to codewords. -/
  decodeDigest : Digest → Option (Fin numChains → Digit)
  /-- Membership in the code. -/
  Valid : (Fin numChains → Digit) → Prop
  validDecidable : DecidablePred Valid
  /-- `A_max`, the maximum number of randomizer trials of the signer. -/
  signingAttemptLimit : Nat
  signingAttemptLimit_pos : 0 < signingAttemptLimit
  /-- Randomizer trials are numbered in 32 bits. -/
  signingAttemptLimit_le : signingAttemptLimit ≤ 2 ^ 32
  /-- A bound on the chain steps one verification walks. -/
  verificationChainHashes : Nat
  decodeDigest_valid {digest : Digest} {x : Fin numChains → Digit} :
    decodeDigest digest = some x → Valid x
  digest_eq_of_decodeDigest_eq_some {left right : Digest} {x : Fin numChains → Digit} :
    decodeDigest left = some x → decodeDigest right = some x → left = right
  eq_of_pointwiseLE_of_valid {x y : Fin numChains → Digit} :
    Valid x → Valid y → (∀ i, x i ≤ y i) → x = y
  verificationWork_le {x : Fin numChains → Digit} :
    Valid x → ∑ i, (chainLength - 1 - (x i).val) ≤ verificationChainHashes
  exists_decodes : ∃ digest x, decodeDigest digest = some x

attribute [reducible, instance] Code.validDecidable

variable [Code]

/-- A chain. -/
abbrev ChainIndex := Fin Code.numChains

/-- A word of `v` digits, one per chain. -/
abbrev Encoding := ChainIndex → Digit

namespace Code

def PointwiseLE (x y : Encoding) : Prop := ∀ i, x i ≤ y i

def Incomparable (x y : Encoding) : Prop := ¬PointwiseLE x y ∧ ¬PointwiseLE y x

/-- The chain steps the verifier walks for an encoding. -/
def verificationWork (x : Encoding) : Nat :=
  ∑ i, (chainLength - 1 - (x i).val)

/-- The verifier's domain-separated WOTS chain positions for one encoding. -/
abbrev SuffixPosition (x : Encoding) :=
  Σ i : ChainIndex, Fin (chainLength - 1 - (x i).val)

theorem card_suffixPosition (x : Encoding) :
    Fintype.card (SuffixPosition x) = verificationWork x := by
  rw [Fintype.card_sigma]
  simp [verificationWork]

/-- The verifier's chain positions of a valid encoding, numbered injectively. -/
noncomputable def enumerateSuffixPositions (x : Encoding) (hx : Valid x) :
    SuffixPosition x ↪ Fin verificationChainHashes :=
  (Fintype.equivFin (SuffixPosition x)).toEmbedding.trans
    (Fin.castLEEmb (by rw [card_suffixPosition]; exact verificationWork_le hx))

/-- Two distinct encoding-hash inputs decoding to the same encoding form a target collision. -/
theorem hash_collision_of_same_decodedEncoding {α : Type} (hash : α → Digest)
    {left right : α} {x : Encoding} (hne : left ≠ right)
    (hleft : decodeDigest (hash left) = some x)
    (hright : decodeDigest (hash right) = some x) :
    left ≠ right ∧ hash left = hash right :=
  ⟨hne, digest_eq_of_decodeDigest_eq_some hleft hright⟩

theorem incomparable_of_valid_of_ne {x y : Encoding} (hx : Valid x) (hy : Valid y)
    (hne : x ≠ y) : Incomparable x y := by
  constructor
  · exact fun hxy => hne (eq_of_pointwiseLE_of_valid hx hy hxy)
  · exact fun hyx => hne (eq_of_pointwiseLE_of_valid hy hx hyx).symm

/-- A different valid encoding moves backward on at least one chain. -/
theorem exists_forged_lt_signed {signedEncoding forgedEncoding : Encoding}
    (hsigned : Valid signedEncoding) (hforged : Valid forgedEncoding)
    (hne : signedEncoding ≠ forgedEncoding) :
    ∃ i, forgedEncoding i < signedEncoding i := by
  have hnot := (incomparable_of_valid_of_ne hsigned hforged hne).1
  simpa only [PointwiseLE, not_forall, not_le] using hnot

end Code

end Xmss.Generic
