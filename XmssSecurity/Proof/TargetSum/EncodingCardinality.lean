import XmssSecurity.Proof.Generic.CappedEncodingRejection
import XmssSecurity.Proof.TargetSum.Code
/-! Counting admissible target-sum encodings. -/

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.TargetSum

/-- Digit strings of a given length and sum. -/
abbrev Words (radix length total : ℕ) :=
  {digits : Fin length → Fin radix // ∑ i, (digits i).val = total}

noncomputable def wordCount (radix length total : ℕ) : ℕ :=
  Fintype.card (Words radix length total)

def wordsSuccEquiv (radix length total : ℕ) :
    Words radix (length + 1) total ≃
      Σ digit : Fin radix, {tail : Fin length → Fin radix // digit.val + ∑ i, (tail i).val = total} where
  toFun word := ⟨word.1 0, fun i => word.1 i.succ, by
    simpa only [Fin.sum_univ_succ] using word.2⟩
  invFun word := ⟨Fin.cases word.1 word.2.1, by
    simpa only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ] using word.2.2⟩
  left_inv word := by
    apply Subtype.ext
    funext i
    cases i using Fin.cases <;> rfl
  right_inv word := by
    rcases word with ⟨digit, tail, htotal⟩
    rfl

theorem wordCount_succ (radix length total : ℕ) :
    wordCount radix (length + 1) total =
      ∑ digit : Fin radix, if digit.val ≤ total then wordCount radix length (total - digit.val) else 0 := by
  rw [wordCount, Fintype.card_congr (wordsSuccEquiv radix length total), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro digit _
  by_cases hle : digit.val ≤ total
  · rw [if_pos hle]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun tail => by omega)
  · rw [if_neg hle]
    letI : IsEmpty {tail : Fin length → Fin radix // digit.val + ∑ i, (tail i).val = total} :=
      ⟨fun word => by have h := word.2; omega⟩
    exact Fintype.card_eq_zero

theorem wordCount_zero (radix total : ℕ) :
    wordCount radix 0 total = if total = 0 then 1 else 0 := by
  classical
  unfold wordCount Words
  by_cases htotal : total = 0
  · subst total
    simp
  · simp [htotal, Ne.symm htotal]

/-- One finite row of the convolution, retaining only totals at most `cap`. -/
def countRowStep (radix cap : ℕ) (previous : List ℕ) : List ℕ :=
  (List.range (cap + 1)).map fun total =>
    ∑ digit : Fin radix, if digit.val ≤ total then previous.getD (total - digit.val) 0 else 0

def countRow (radix cap : ℕ) : ℕ → List ℕ
  | 0 => (List.range (cap + 1)).map fun total => if total = 0 then 1 else 0
  | length + 1 => countRowStep radix cap (countRow radix cap length)

theorem countRowStep_getD (radix cap : ℕ) (previous : List ℕ) (total : ℕ)
    (htotal : total ≤ cap) :
    (countRowStep radix cap previous).getD total 0 =
      ∑ digit : Fin radix, if digit.val ≤ total then previous.getD (total - digit.val) 0 else 0 := by
  simp [countRowStep, List.getD_eq_getElem?_getD, show total < cap + 1 by omega]

theorem countRow_getD_eq_wordCount (radix cap length total : ℕ) (htotal : total ≤ cap) :
    (countRow radix cap length).getD total 0 = wordCount radix length total := by
  induction length generalizing total with
  | zero =>
      rw [countRow, wordCount_zero]
      simp [List.getD_eq_getElem?_getD, show total < cap + 1 by omega]
  | succ length ih =>
      rw [countRow, countRowStep_getD _ _ _ _ htotal, wordCount_succ]
      apply Finset.sum_congr rfl
      intro digit _
      split
      · rw [ih _ (by omega)]
      · rfl

theorem validDigest_encoding_valid (digest : Digest) (hdigest : Code.ValidDigest digest) :
    Valid (digestEncoding digest) := by
  obtain ⟨encoding, hencoding⟩ := hdigest
  have hview := decodeDigest_eq_some_iff.mp hencoding
  have hdigits : digestEncoding digest = encoding := congrArg Prod.fst hview.1
  exact hdigits ▸ hview.2

noncomputable def validDigestEquivEncoding : {digest : Digest // Code.ValidDigest digest} ≃
    {encoding : Encoding // Valid encoding} :=
  Equiv.ofBijective (fun digest => ⟨digestEncoding digest.1,
    validDigest_encoding_valid digest.1 digest.2⟩) (by
      constructor
      · intro left right heq
        apply Subtype.ext
        apply digestView_injective
        apply Prod.ext
        · exact congrArg Subtype.val heq
        · obtain ⟨leftEncoding, hleft⟩ := left.2
          obtain ⟨rightEncoding, hright⟩ := right.2
          have hleftPadding := congrArg Prod.snd (decodeDigest_eq_some_iff.mp hleft).1
          have hrightPadding := congrArg Prod.snd (decodeDigest_eq_some_iff.mp hright).1
          exact hleftPadding.trans hrightPadding.symm
      · intro encoding
        obtain ⟨digest, hdigest⟩ := TargetSum.digestView_surjective (encoding.1, 0)
        refine ⟨⟨digest, encoding.1, decodeDigest_eq_some_iff.mpr ⟨hdigest, encoding.2⟩⟩, ?_⟩
        apply Subtype.ext
        exact congrArg Prod.fst hdigest)

theorem validDigests_card_eq_wordCount :
    Code.validDigests.card = wordCount chainLength numChains targetSum := by
  rw [Code.validDigests, ← Fintype.card_subtype, Fintype.card_congr validDigestEquivEncoding]
  rfl

end XmssSecurity.TargetSum.TargetSum
