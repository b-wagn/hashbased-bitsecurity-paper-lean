import XmssSecurity.Proof.IdealStatement
import Mathlib.Data.BitVec

namespace XmssSecurity

/-- An upper bound on the WOTS chain edges one verification walks: `v · (2^w - 1) = 322`. -/
def verificationChainHashes : Nat := numChains * (chainLength - 1)

namespace Checksum

open scoped BigOperators

def PointwiseLE (x y : Encoding) : Prop := ∀ i, x i ≤ y i

def Incomparable (x y : Encoding) : Prop := ¬PointwiseLE x y ∧ ¬PointwiseLE y x

def verificationWork (x : Encoding) : Nat :=
  ∑ i, (chainLength - 1 - (x i).val)

/-- The verifier's domain-separated WOTS chain positions for one encoding. -/
abbrev SuffixPosition (x : Encoding) :=
  Σ i : ChainIndex, Fin (chainLength - 1 - (x i).val)

/-- Every encoding makes the verifier walk at most `322` WOTS chain edges. -/
theorem verificationWork_le (x : Encoding) : verificationWork x ≤ verificationChainHashes := by
  unfold verificationWork verificationChainHashes
  calc
    _ ≤ ∑ _i : ChainIndex, (chainLength - 1) := Finset.sum_le_sum fun i _ => Nat.sub_le _ _
    _ = _ := by simp

/-- The verifier's chain positions, numbered injectively below `322`. -/
def enumerateSuffixPositions (x : Encoding) (_hx : Valid x) :
    SuffixPosition x ↪ Fin verificationChainHashes where
  toFun position := ⟨(chainLength - 1) * position.1.val + position.2.val, by
    have hchain := position.1.isLt
    have hstep := position.2.isLt
    simp only [verificationChainHashes, numChains, chainLength, winternitzBits] at *
    omega⟩
  inj' := by
    rintro ⟨i, k⟩ ⟨i', k'⟩ h
    have hk := k.isLt
    have hk' := k'.isLt
    simp only [Fin.mk.injEq, chainLength, winternitzBits] at h hk hk'
    have hi : i = i' := Fin.ext (by omega)
    subst hi
    have : k = k' := Fin.ext (by omega)
    subst this
    rfl

/-! ### Chains of the message and of the checksum -/

theorem messageChain_val (i : Fin messageDigits) : (messageChain i).val = i.val := rfl

theorem checksumChain_val (j : Fin checksumDigits) :
    (checksumChain j).val = messageDigits + j.val := rfl

/-- Every chain carries a message digit or a checksum digit. -/
theorem chain_cases (chain : ChainIndex) :
    (∃ i, chain = messageChain i) ∨ (∃ j, chain = checksumChain j) := by
  by_cases h : chain.val < messageDigits
  · exact Or.inl ⟨⟨chain.val, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨chain.val - messageDigits, ?_⟩, Fin.ext ?_⟩
    · have := chain.isLt
      simp only [numChains, messageDigits, checksumDigits] at *
      omega
    · simp only [checksumChain_val]
      omega

theorem encode_messageChain (digest : Digest) (i : Fin messageDigits) :
    encode digest (messageChain i) = messageDigit digest i := by
  unfold encode
  rw [dif_pos (by simp [messageChain_val])]
  rfl

theorem encode_checksumChain (digest : Digest) (j : Fin checksumDigits) :
    encode digest (checksumChain j) = checksumDigit (checksum (messageDigit digest)) j := by
  unfold encode
  rw [dif_neg (by simp [checksumChain_val])]
  congr 1
  ext
  simp [checksumChain_val]

theorem messagePart_encode (digest : Digest) : messagePart (encode digest) = messageDigit digest := by
  funext i
  exact encode_messageChain digest i

/-- The checksum is at most `len_1 · (2^w - 1) = 301`. -/
theorem checksum_le (digits : Fin messageDigits → Digit) :
    checksum digits ≤ messageDigits * (chainLength - 1) := by
  unfold checksum
  calc
    _ ≤ ∑ _i : Fin messageDigits, (chainLength - 1) := Finset.sum_le_sum fun i _ => Nat.sub_le _ _
    _ = _ := by simp

/-- The three checksum digits represent the checksum exactly. -/
theorem checksum_eq_digits (csum : Nat) (hcsum : csum < chainLength ^ checksumDigits) :
    csum = chainLength ^ 2 * (checksumDigit csum ⟨0, by decide⟩).val +
      chainLength * (checksumDigit csum ⟨1, by decide⟩).val +
        (checksumDigit csum ⟨2, by decide⟩).val := by
  simp only [checksumDigit, checksumDigits, chainLength, winternitzBits] at *
  norm_num at *
  omega

/-- Digitwise comparison of checksum digits compares the checksums. -/
theorem checksum_le_of_digits_le {left right : Nat}
    (hleft : left < chainLength ^ checksumDigits) (hright : right < chainLength ^ checksumDigits)
    (hdigits : ∀ j, checksumDigit left j ≤ checksumDigit right j) : left ≤ right := by
  rw [checksum_eq_digits left hleft, checksum_eq_digits right hright]
  have h0 := hdigits ⟨0, by decide⟩
  have h1 := hdigits ⟨1, by decide⟩
  have h2 := hdigits ⟨2, by decide⟩
  rw [Fin.le_def] at h0 h1 h2
  simp only [chainLength, winternitzBits] at *
  omega

theorem checksum_lt_pow (digits : Fin messageDigits → Digit) :
    checksum digits < chainLength ^ checksumDigits :=
  (checksum_le digits).trans_lt (by decide)

/-! ### Validity -/

theorem messageDigit_last_lt (digest : Digest) : (messageDigit digest lastMessageDigit).val < 4 := by
  unfold messageDigit lastMessageDigit
  change (BitVec.extractLsb' _ _ digest).toNat < 4
  have hdigest := digest.isLt
  simp only [winternitzBits, messageDigits, digestBits] at *
  simp [BitVec.extractLsb'_toNat]
  omega

theorem encode_valid (digest : Digest) : Valid (encode digest) := by
  refine ⟨?_, fun j => ?_⟩
  · rw [encode_messageChain]
    exact messageDigit_last_lt digest
  · rw [encode_checksumChain, messagePart_encode]

theorem decodeDigest_eq_some_iff {digest : Digest} {x : Encoding} :
    decodeDigest digest = some x ↔ encode digest = x ∧ Valid x := by
  unfold decodeDigest
  constructor
  · intro h
    have hx := Option.some.inj h
    exact ⟨hx, hx ▸ encode_valid digest⟩
  · exact fun h => congrArg some h.1

theorem decodeDigest_valid {digest : Digest} {x : Encoding} (h : decodeDigest digest = some x) :
    Valid x :=
  (decodeDigest_eq_some_iff.mp h).2

/-- The message digits determine the digest. -/
theorem messageDigit_injective : Function.Injective messageDigit := by
  intro left right hdigits
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  have hbelow : bit < 128 := by simpa [digestBits] using hbit
  let digit : Fin messageDigits := ⟨bit / winternitzBits, by
    change bit / 3 < 43
    omega⟩
  let offsetBit := bit % winternitzBits
  have hoffsetBit : offsetBit < winternitzBits := Nat.mod_lt bit (by decide)
  have hoffset : winternitzBits * digit.val + offsetBit = bit := by
    change 3 * (bit / 3) + bit % 3 = bit
    have := Nat.mod_add_div bit 3
    omega
  have hextract :
      left.extractLsb' (winternitzBits * digit.val) winternitzBits =
        right.extractLsb' (winternitzBits * digit.val) winternitzBits := by
    apply BitVec.toFin_injective
    exact congrFun hdigits digit
  have hlocalBit := congrArg (fun value => value.getLsbD offsetBit) hextract
  simpa [BitVec.getLsbD_extractLsb', hoffsetBit, hoffset] using hlocalBit

theorem encode_injective : Function.Injective encode := by
  intro left right h
  apply messageDigit_injective
  rw [← messagePart_encode left, ← messagePart_encode right, h]

/-- A digest is determined by its encoding. -/
theorem digest_eq_of_decodeDigest_eq_some {left right : Digest} {x : Encoding}
    (hleft : decodeDigest left = some x) (hright : decodeDigest right = some x) :
    left = right :=
  encode_injective ((decodeDigest_eq_some_iff.mp hleft).1.trans
    (decodeDigest_eq_some_iff.mp hright).1.symm)

/-- Two distinct encoding-hash inputs decoding to the same encoding form a target collision. -/
theorem hash_collision_of_same_decodedEncoding {α : Type} (hash : α → Digest)
    {left right : α} {x : Encoding} (hne : left ≠ right)
    (hleft : decodeDigest (hash left) = some x)
    (hright : decodeDigest (hash right) = some x) :
    left ≠ right ∧ hash left = hash right :=
  ⟨hne, digest_eq_of_decodeDigest_eq_some hleft hright⟩

/-- No codeword dominates another one: the checksum increases when message digits decrease. -/
theorem eq_of_pointwiseLE_of_valid {x y : Encoding} (hx : Valid x) (hy : Valid y)
    (hxy : PointwiseLE x y) : x = y := by
  have hmessage : ∀ i, (messagePart x i).val ≤ (messagePart y i).val := fun i => hxy _
  -- The checksum of `y` is at most the checksum of `x`.
  have hdown : checksum (messagePart y) ≤ checksum (messagePart x) := by
    unfold checksum
    exact Finset.sum_le_sum fun i _ => Nat.sub_le_sub_left (hmessage i) _
  -- The checksum digits of `x` are at most those of `y`.
  have hup : checksum (messagePart x) ≤ checksum (messagePart y) := by
    apply checksum_le_of_digits_le (checksum_lt_pow _) (checksum_lt_pow _)
    intro j
    rw [← hx.2 j, ← hy.2 j]
    exact hxy _
  have hcsum : checksum (messagePart x) = checksum (messagePart y) := le_antisymm hup hdown
  have hterms : ∀ i, (messagePart x i).val = (messagePart y i).val := by
    have hsum : ∑ i, (chainLength - 1 - (messagePart y i).val) =
        ∑ i, (chainLength - 1 - (messagePart x i).val) := hcsum.symm
    have hle : ∀ i ∈ Finset.univ, chainLength - 1 - (messagePart y i).val ≤
        chainLength - 1 - (messagePart x i).val := fun i _ => Nat.sub_le_sub_left (hmessage i) _
    have heach := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
    intro i
    have hi := heach i (Finset.mem_univ i)
    have hxi := (messagePart x i).isLt
    have hyi := (messagePart y i).isLt
    have := hmessage i
    simp only [chainLength, winternitzBits] at *
    omega
  funext chain
  rcases chain_cases chain with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact Fin.ext (hterms i)
  · have hparts : messagePart x = messagePart y := funext fun i => Fin.ext (hterms i)
    rw [hx.2 j, hy.2 j, hparts]

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

end Checksum

end XmssSecurity
