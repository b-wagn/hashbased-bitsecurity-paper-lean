import XmssSecurity.Proof.TargetSum.EncodingCardinality
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Distinct target-sum encodings obtained by moving one unit between two digits. -/

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.Attack

abbrev DecreasingChain (encoding : Encoding) :=
  {chain : ChainIndex // 0 < (encoding chain).val}

abbrev IncreasingChain (encoding : Encoding) :=
  {chain : ChainIndex // (encoding chain).val + 1 < chainLength}

/-- Decrease the first chain and increase a distinct second chain. -/
abbrev DigitTransfer (encoding : Encoding) :=
  Σ lower : DecreasingChain encoding,
    {upper : ChainIndex // (encoding upper).val + 1 < chainLength ∧ upper ≠ lower.1}

theorem decreasingChain_card_lower (encoding : Encoding) (hvalid : Code.Valid encoding) :
    28 ≤ Fintype.card (DecreasingChain encoding) := by
  let indices := Finset.univ.filter fun chain => 0 < (encoding chain).val
  have hsum : ∑ chain ∈ indices, (encoding chain).val = targetSum := by
    rw [Finset.sum_filter]
    change (∑ chain, if 0 < (encoding chain).val then (encoding chain).val else 0) = targetSum
    have heq : ∀ chain, (if 0 < (encoding chain).val then (encoding chain).val else 0) =
        (encoding chain).val := by intro chain; split_ifs <;> omega
    simp_rw [heq]
    exact hvalid
  have hle : ∑ chain ∈ indices, (encoding chain).val ≤ indices.card * 7 := by
    calc
      _ ≤ ∑ _chain ∈ indices, 7 := Finset.sum_le_sum fun chain _ => by
        have h := (encoding chain).isLt
        norm_num [chainLength, winternitzBits] at h
        omega
      _ = _ := by simp
  rw [hsum] at hle
  have hcard : Fintype.card (DecreasingChain encoding) = indices.card := by
    rw [Fintype.card_subtype]
  norm_num [targetSum] at hle
  omega

theorem increasingChain_card_lower (encoding : Encoding) (hvalid : Code.Valid encoding) :
    15 ≤ Fintype.card (IncreasingChain encoding) := by
  let indices := Finset.univ.filter fun chain => (encoding chain).val + 1 < chainLength
  have hsum : ∑ chain ∈ indices, (7 - (encoding chain).val) = 99 := by
    rw [Finset.sum_filter]
    have heq : ∀ chain, (if (encoding chain).val + 1 < chainLength then 7 - (encoding chain).val else 0) =
        7 - (encoding chain).val := by
      intro chain
      have h := (encoding chain).isLt
      norm_num [chainLength, winternitzBits] at h ⊢
      omega
    simp_rw [heq]
    simpa [TargetSum.verificationWork, verificationChainHashes, chainLength, winternitzBits,
      numChains, targetSum] using TargetSum.verificationWork_eq encoding hvalid
  have hle : ∑ chain ∈ indices, (7 - (encoding chain).val) ≤ indices.card * 7 := by
    calc
      _ ≤ ∑ _chain ∈ indices, 7 := Finset.sum_le_sum fun chain _ => Nat.sub_le _ _
      _ = _ := by simp
  rw [hsum] at hle
  have hcard : Fintype.card (IncreasingChain encoding) = indices.card := by
    rw [Fintype.card_subtype]
  omega

theorem digitTransfer_card_lower (encoding : Encoding) (hvalid : Code.Valid encoding) :
    392 ≤ Fintype.card (DigitTransfer encoding) := by
  have hdecrease := decreasingChain_card_lower encoding hvalid
  have hincrease := increasingChain_card_lower encoding hvalid
  have hchoices : ∀ lower : DecreasingChain encoding,
      14 ≤ Fintype.card {upper : ChainIndex //
        (encoding upper).val + 1 < chainLength ∧ upper ≠ lower.1} := by
    intro lower
    let indices := Finset.univ.filter fun chain => (encoding chain).val + 1 < chainLength
    have hcard : Fintype.card {upper : ChainIndex //
        (encoding upper).val + 1 < chainLength ∧ upper ≠ lower.1} =
        (indices.erase lower.1).card := by
      rw [Fintype.card_subtype]
      apply congrArg Finset.card
      ext upper
      simp [indices, and_comm]
    rw [hcard]
    have htotal : Fintype.card (IncreasingChain encoding) = indices.card := by
      rw [Fintype.card_subtype]
    have h := Finset.pred_card_le_card_erase (s := indices) (a := lower.1)
    omega
  rw [Fintype.card_sigma]
  calc
    392 ≤ Fintype.card (DecreasingChain encoding) * 14 := by omega
    _ = ∑ _lower : DecreasingChain encoding, 14 := by simp
    _ ≤ _ := Finset.sum_le_sum fun lower _ => hchoices lower

def transferEncoding (encoding : Encoding) (transfer : DigitTransfer encoding) : Encoding :=
  Function.update (Function.update encoding transfer.1.1
    ⟨(encoding transfer.1.1).val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) (encoding transfer.1.1).isLt⟩)
    transfer.2.1 ⟨(encoding transfer.2.1).val + 1, transfer.2.2.1⟩

@[simp]
theorem transferEncoding_lower (encoding : Encoding) (transfer : DigitTransfer encoding) :
    (transferEncoding encoding transfer transfer.1.1).val = (encoding transfer.1.1).val - 1 := by
  simp [transferEncoding, Ne.symm transfer.2.2.2]

@[simp]
theorem transferEncoding_upper (encoding : Encoding) (transfer : DigitTransfer encoding) :
    (transferEncoding encoding transfer transfer.2.1).val = (encoding transfer.2.1).val + 1 := by
  simp [transferEncoding]

theorem transferEncoding_other (encoding : Encoding) (transfer : DigitTransfer encoding)
    (chain : ChainIndex) (hlower : chain ≠ transfer.1.1) (hupper : chain ≠ transfer.2.1) :
    transferEncoding encoding transfer chain = encoding chain := by
  simp [transferEncoding, hlower, hupper]

theorem transferEncoding_valid (encoding : Encoding) (hvalid : Code.Valid encoding)
    (transfer : DigitTransfer encoding) : Code.Valid (transferEncoding encoding transfer) := by
  have hpoint : ∀ chain, (transferEncoding encoding transfer chain).val +
      (if chain = transfer.1.1 then 1 else 0) =
      (encoding chain).val + (if chain = transfer.2.1 then 1 else 0) := by
    intro chain
    by_cases hlower : chain = transfer.1.1
    · subst chain
      simp only [transferEncoding_lower, if_true, if_neg (Ne.symm transfer.2.2.2), Nat.add_zero]
      have h := transfer.1.2
      omega
    · by_cases hupper : chain = transfer.2.1
      · subst chain
        simp [hlower]
      · rw [transferEncoding_other _ _ _ hlower hupper]
        simp [hlower, hupper]
  have hsum := congrArg (fun values : ChainIndex → ℕ => ∑ chain, values chain) (funext hpoint)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  change (∑ chain, (transferEncoding encoding transfer chain).val) = targetSum
  change (∑ chain, (encoding chain).val) = targetSum at hvalid
  omega

theorem transferEncoding_lt_iff (encoding : Encoding) (transfer : DigitTransfer encoding)
    (chain : ChainIndex) :
    (transferEncoding encoding transfer chain).val < (encoding chain).val ↔ chain = transfer.1.1 := by
  by_cases hlower : chain = transfer.1.1
  · subst chain
    simp only [transferEncoding_lower, iff_true]
    have h := transfer.1.2
    omega
  · by_cases hupper : chain = transfer.2.1
    · subst chain
      simp [hlower]
    · rw [transferEncoding_other _ _ _ hlower hupper]
      simp [hlower]

theorem transferEncoding_gt_iff (encoding : Encoding) (transfer : DigitTransfer encoding)
    (chain : ChainIndex) :
    (encoding chain).val < (transferEncoding encoding transfer chain).val ↔ chain = transfer.2.1 := by
  by_cases hupper : chain = transfer.2.1
  · subst chain
    simp
  · by_cases hlower : chain = transfer.1.1
    · subst chain
      simp only [transferEncoding_lower, hupper, iff_false]
      omega
    · rw [transferEncoding_other _ _ _ hlower hupper]
      simp [hupper]

theorem transferEncoding_injective (encoding : Encoding) : Function.Injective (transferEncoding encoding) := by
  intro left right heq
  have hlower : left.1.1 = right.1.1 := by
    apply (transferEncoding_lt_iff encoding right left.1.1).mp
    rw [← heq]
    exact (transferEncoding_lt_iff encoding left left.1.1).mpr rfl
  have hupper : left.2.1 = right.2.1 := by
    apply (transferEncoding_gt_iff encoding right left.2.1).mp
    rw [← heq]
    exact (transferEncoding_gt_iff encoding left left.2.1).mpr rfl
  rcases left with ⟨⟨leftLower, hleftLower⟩, ⟨leftUpper, hleftUpper⟩⟩
  rcases right with ⟨⟨rightLower, hrightLower⟩, ⟨rightUpper, hrightUpper⟩⟩
  dsimp only at hlower hupper
  subst rightLower
  subst rightUpper
  rfl

/-- The unique digest containing the encoding and zero padding bits. -/
noncomputable def digestOfEncoding (encoding : Encoding) : Digest :=
  Classical.choose (TargetSum.digestView_surjective (encoding, 0))

theorem digestOfEncoding_view (encoding : Encoding) :
    TargetSum.digestView (digestOfEncoding encoding) = (encoding, 0) :=
  Classical.choose_spec (TargetSum.digestView_surjective (encoding, 0))

theorem digestOfEncoding_injective : Function.Injective digestOfEncoding := by
  intro left right heq
  have hview := congrArg TargetSum.digestView heq
  rw [digestOfEncoding_view, digestOfEncoding_view] at hview
  exact congrArg Prod.fst hview

theorem digestOfEncoding_decode (encoding : Encoding) (hvalid : Code.Valid encoding) :
    Code.decodeDigest (digestOfEncoding encoding) = some encoding :=
  TargetSum.decodeDigest_eq_some_iff.mpr ⟨digestOfEncoding_view encoding, hvalid⟩

noncomputable def neighborDigests (encoding : Encoding) : Finset Digest :=
  Finset.univ.image fun transfer : DigitTransfer encoding => digestOfEncoding (transferEncoding encoding transfer)

theorem neighborDigests_card (encoding : Encoding) :
    (neighborDigests encoding).card = Fintype.card (DigitTransfer encoding) := by
  unfold neighborDigests
  have hinj : Function.Injective (fun transfer : DigitTransfer encoding =>
      digestOfEncoding (transferEncoding encoding transfer)) :=
    fun _ _ heq => transferEncoding_injective encoding (digestOfEncoding_injective heq)
  rw [Finset.card_image_of_injective _ hinj]
  exact Finset.card_univ

theorem neighborDigests_card_lower (encoding : Encoding) (hvalid : Code.Valid encoding) :
    392 ≤ (neighborDigests encoding).card := by
  rw [neighborDigests_card]
  exact digitTransfer_card_lower encoding hvalid

/-- info: 'XmssSecurity.TargetSum.Attack.neighborDigests_card_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neighborDigests_card_lower

end XmssSecurity.TargetSum.Attack
