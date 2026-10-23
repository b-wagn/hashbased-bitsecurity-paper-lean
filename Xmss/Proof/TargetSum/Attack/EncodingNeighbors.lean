import Xmss.Proof.TargetSum.EncodingCardinality
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Distinct target-sum encodings obtained by moving one unit between two digits. -/

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open Xmss.Generic

namespace Xmss.TargetSum.Attack

abbrev DecreasingChain (encoding : Encoding) :=
  {chain : ChainIndex // 0 < (encoding chain).val}

abbrev IncreasingChain (encoding : Encoding) :=
  {chain : ChainIndex // (encoding chain).val + 1 < chainLength}

/-- Decrease the first chain and increase a distinct second chain. -/
abbrev DigitTransfer (encoding : Encoding) :=
  Σ lower : DecreasingChain encoding,
    {upper : ChainIndex // (encoding upper).val + 1 < chainLength ∧ upper ≠ lower.1}

theorem decreasingChain_card_lower (encoding : Encoding) (hvalid : Code.Valid encoding) :
    22 ≤ Fintype.card (DecreasingChain encoding) := by
  let indices := Finset.univ.filter fun chain => 0 < (encoding chain).val
  have hsum : ∑ chain ∈ indices, (encoding chain).val = targetSum := by
    rw [Finset.sum_filter]
    change (∑ chain, if 0 < (encoding chain).val then (encoding chain).val else 0) = targetSum
    have heq : ∀ chain, (if 0 < (encoding chain).val then (encoding chain).val else 0) =
        (encoding chain).val := by intro chain; split_ifs <;> omega
    simp_rw [heq]
    exact hvalid
  have hle : ∑ chain ∈ indices, (encoding chain).val ≤ indices.card * 15 := by
    calc
      _ ≤ ∑ _chain ∈ indices, 15 := Finset.sum_le_sum fun chain _ => by
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
    10 ≤ Fintype.card (IncreasingChain encoding) := by
  let indices := Finset.univ.filter fun chain => (encoding chain).val + 1 < chainLength
  have hsum : ∑ chain ∈ indices, (15 - (encoding chain).val) = 150 := by
    rw [Finset.sum_filter]
    have heq : ∀ chain, (if (encoding chain).val + 1 < chainLength then 15 - (encoding chain).val else 0) =
        15 - (encoding chain).val := by
      intro chain
      have h := (encoding chain).isLt
      norm_num [chainLength, winternitzBits] at h ⊢
      omega
    simp_rw [heq]
    simpa [TargetSum.verificationWork, verificationChainHashes, chainLength, winternitzBits,
      numChains, targetSum] using TargetSum.verificationWork_eq encoding hvalid
  have hle : ∑ chain ∈ indices, (15 - (encoding chain).val) ≤ indices.card * 15 := by
    calc
      _ ≤ ∑ _chain ∈ indices, 15 := Finset.sum_le_sum fun chain _ => Nat.sub_le _ _
      _ = _ := by simp
  rw [hsum] at hle
  have hcard : Fintype.card (IncreasingChain encoding) = indices.card := by
    rw [Fintype.card_subtype]
  omega

/-- The pairs `(j, i)` with `j ≠ i`, `x_j ≥ 1`, and `x_i ≤ 2^w - 2`, as in the paper. There are
`lows.card * highs.card - (lows ∩ highs).card` of them, hence at least `220`: the sum `T = 330`
forces `22 ≤ lows.card` and `10 ≤ highs.card`, and the two sets cover all `32` chains. -/
theorem digitTransfer_card_lower (encoding : Encoding) (hvalid : Code.Valid encoding) :
    220 ≤ Fintype.card (DigitTransfer encoding) := by
  classical
  set lows := Finset.univ.filter fun chain : ChainIndex => 0 < (encoding chain).val with hlowsDef
  set highs := Finset.univ.filter fun chain : ChainIndex =>
    (encoding chain).val + 1 < chainLength with hhighsDef
  have hcardLow : Fintype.card (DecreasingChain encoding) = lows.card := Fintype.card_subtype _
  have hcardHigh : Fintype.card (IncreasingChain encoding) = highs.card := Fintype.card_subtype _
  have hlow : 22 ≤ lows.card := hcardLow ▸ decreasingChain_card_lower encoding hvalid
  have hhigh : 10 ≤ highs.card := hcardHigh ▸ increasingChain_card_lower encoding hvalid
  -- Every digit is either positive or below the top, so the two sets cover all chains.
  have hunion : lows ∪ highs = Finset.univ := by
    ext chain
    have hlt := (encoding chain).isLt
    norm_num [chainLength, winternitzBits] at hlt
    simp only [hlowsDef, hhighsDef, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true, chainLength, winternitzBits]
    omega
  have hcover : lows.card + highs.card = 32 + (lows ∩ highs).card := by
    have hcards := Finset.card_union_add_card_inter lows highs
    rw [hunion, Finset.card_univ] at hcards
    simpa [numChains] using hcards.symm
  -- The number of partners of a fixed lowerable chain.
  have hchoices : ∀ lower : DecreasingChain encoding,
      Fintype.card {upper : ChainIndex // (encoding upper).val + 1 < chainLength ∧ upper ≠ lower.1}
        = (highs.erase lower.1).card := by
    intro lower
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext upper
    simp [hhighsDef, and_comm]
  rw [Fintype.card_sigma]
  simp only [hchoices]
  rw [← Finset.sum_subtype lows (fun chain => by simp [hlowsDef]) fun chain => (highs.erase chain).card]
  -- Split the lowerable chains by whether they are also raisable.
  have hinter : ∑ chain ∈ lows ∩ highs, (highs.erase chain).card
      = (lows ∩ highs).card * (highs.card - 1) := by
    rw [Finset.sum_congr rfl fun chain hchain => Finset.card_erase_of_mem
      (Finset.mem_inter.mp hchain).2, Finset.sum_const, smul_eq_mul]
  have hdiff : ∑ chain ∈ lows \ highs, (highs.erase chain).card = (lows \ highs).card * highs.card := by
    rw [Finset.sum_congr rfl fun chain hchain => congrArg Finset.card
      (Finset.erase_eq_of_notMem (Finset.mem_sdiff.mp hchain).2), Finset.sum_const, smul_eq_mul]
  rw [← Finset.sum_inter_add_sum_sdiff lows highs fun chain => (highs.erase chain).card, hinter, hdiff]
  have hparts := Finset.card_inter_add_card_sdiff lows highs
  obtain ⟨partners, hpartners⟩ : ∃ partners, highs.card = partners + 1 := ⟨highs.card - 1, by omega⟩
  rw [hpartners]
  have hsum : (lows ∩ highs).card * (partners + 1 - 1) + (lows \ highs).card * (partners + 1)
      = lows.card * partners + (lows \ highs).card := by
    simp only [Nat.add_sub_cancel]
    rw [← hparts]
    ring
  rw [hsum]
  have hmul : 22 * partners ≤ lows.card * partners := Nat.mul_le_mul_right partners hlow
  have hrest : (lows \ highs).card + partners = 31 := by omega
  generalize lows.card * partners = product at hmul ⊢
  omega

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

/-- The unique digest containing the encoding and all 128 bits. -/
noncomputable def digestOfEncoding (encoding : Encoding) : Digest :=
  Classical.choose (TargetSum.encode_surjective encoding)

theorem encode_digestOfEncoding (encoding : Encoding) :
    encode (digestOfEncoding encoding) = encoding :=
  Classical.choose_spec (TargetSum.encode_surjective encoding)

theorem digestOfEncoding_injective : Function.Injective digestOfEncoding := by
  intro left right heq
  have hview := congrArg encode heq
  rw [encode_digestOfEncoding, encode_digestOfEncoding] at hview
  exact hview

theorem digestOfEncoding_decode (encoding : Encoding) (hvalid : Code.Valid encoding) :
    Code.decodeDigest (digestOfEncoding encoding) = some encoding :=
  TargetSum.decodeDigest_eq_some_iff.mpr ⟨encode_digestOfEncoding encoding, hvalid⟩

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
    220 ≤ (neighborDigests encoding).card := by
  rw [neighborDigests_card]
  exact digitTransfer_card_lower encoding hvalid

/-- info: 'Xmss.TargetSum.Attack.neighborDigests_card_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neighborDigests_card_lower

end Xmss.TargetSum.Attack
