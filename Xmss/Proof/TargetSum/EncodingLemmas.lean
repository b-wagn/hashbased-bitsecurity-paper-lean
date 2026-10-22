import Xmss.Statement.Scheme.TargetSum
import Mathlib.Data.BitVec

namespace Xmss.TargetSum

def verificationChainHashes : Nat := numChains * (chainLength - 1) - targetSum

open scoped BigOperators

def PointwiseLE (x y : Encoding) : Prop := ∀ i, x i ≤ y i

def verificationWork (x : Encoding) : Nat :=
  ∑ i, (chainLength - 1 - (x i).val)

/-- Every valid encoding makes the verifier walk exactly 150 WOTS chain edges. -/
theorem verificationWork_eq (x : Encoding) (hx : Valid x) :
    verificationWork x = verificationChainHashes := by
  unfold Valid sum at hx
  unfold verificationWork verificationChainHashes
  rw [Finset.sum_tsub_distrib Finset.univ]
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact congrArg (numChains * (chainLength - 1) - ·) hx
  · intro i _
    exact Nat.le_pred_of_lt (x i).isLt

/-- All 128 digest bits are partitioned into the 32 four-bit digits. -/
theorem encode_injective : Function.Injective encode := by
  intro left right hencoding
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  have hbelow : bit < 128 := by simpa [digestBits] using hbit
  let chain : ChainIndex := ⟨bit / winternitzBits, by
    change bit / 4 < 32
    omega⟩
  let offsetBit := bit % winternitzBits
  have hoffsetBit : offsetBit < winternitzBits := Nat.mod_lt bit (by decide)
  have hoffset : digitOffset chain + offsetBit = bit := by
    change 4 * (bit / 4) + bit % 4 = bit
    have := Nat.mod_add_div bit 4
    omega
  have hextract :
      left.extractLsb' (digitOffset chain) winternitzBits =
        right.extractLsb' (digitOffset chain) winternitzBits := by
    apply BitVec.toFin_injective
    exact congrFun hencoding chain
  have hlocalBit := congrArg (fun value => value.getLsbD offsetBit) hextract
  simpa [BitVec.getLsbD_extractLsb', hoffsetBit, hoffset] using hlocalBit

theorem decodeDigest_eq_some_iff {digest : Digest} {x : Encoding} :
    decodeDigest digest = some x ↔ encode digest = x ∧ Valid x := by
  unfold decodeDigest
  split <;> rename_i hvalid
  · simp only [Option.some.injEq]
    exact ⟨fun h => ⟨h, h ▸ hvalid⟩, And.left⟩
  · constructor
    · intro h; cases h
    · rintro ⟨h, hx⟩
      exact (hvalid (h.symm ▸ hx)).elim

theorem decodeDigest_zero_eq_none : decodeDigest (0 : Digest) = none := by
  have hsum : sum (encode (0 : Digest)) = 0 := by
    unfold sum
    apply Finset.sum_eq_zero
    intro chain _
    simp [encode]
  unfold decodeDigest
  rw [if_neg]
  change sum (encode (0 : Digest)) ≠ targetSum
  rw [hsum]
  decide

/-- Each encoding determines one exact 128-bit digest. -/
theorem digest_eq_of_decodeDigest_eq_some {left right : Digest} {x : Encoding}
    (hleft : decodeDigest left = some x) (hright : decodeDigest right = some x) :
    left = right :=
  encode_injective ((decodeDigest_eq_some_iff.mp hleft).1.trans
    (decodeDigest_eq_some_iff.mp hright).1.symm)

theorem eq_of_pointwiseLE_of_valid {x y : Encoding} (hx : Valid x) (hy : Valid y)
    (hxy : PointwiseLE x y) : x = y := by
  by_contra hne
  have hlt : ∃ i ∈ Finset.univ, (x i).val < (y i).val := by
    by_contra h
    push Not at h
    apply hne
    funext i
    exact Fin.ext (Nat.le_antisymm (hxy i) (h i (Finset.mem_univ i)))
  have hsum : sum x < sum y := by
    apply Finset.sum_lt_sum
    · intro i _
      exact hxy i
    · exact hlt
  exact (Nat.ne_of_lt hsum) (hx.trans hy.symm)

def exampleValidEncoding : Encoding := fun chain =>
  if chain.val < 22 then ⟨15, by decide⟩ else ⟨0, by decide⟩

theorem exampleValidEncoding_valid : Valid exampleValidEncoding := by
  unfold Valid sum
  rw [Finset.sum_fin_eq_sum_range]
  norm_num [exampleValidEncoding, targetSum, numChains, chainLength,
    Finset.sum_range_succ]

theorem card_digest_eq_card_encoding :
    Fintype.card Digest = Fintype.card Encoding := by
  simp [digestBits, numChains, chainLength, winternitzBits]

theorem encode_surjective : Function.Surjective encode :=
  ((Fintype.bijective_iff_injective_and_card encode).2
    ⟨encode_injective, card_digest_eq_card_encoding⟩).2

theorem exists_decodes : ∃ digest x, decodeDigest digest = some x := by
  obtain ⟨digest, hdigest⟩ := encode_surjective exampleValidEncoding
  exact ⟨digest, exampleValidEncoding, decodeDigest_eq_some_iff.mpr
    ⟨hdigest, exampleValidEncoding_valid⟩⟩

end Xmss.TargetSum
