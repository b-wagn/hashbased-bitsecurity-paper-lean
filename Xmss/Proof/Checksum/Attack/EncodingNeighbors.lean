import Xmss.Proof.Checksum.EncodingProbability
import Xmss.Proof.Checksum.Code

/-! Codewords obtained from a codeword by moving one unit from one chain to another.

A transfer lowers one chain by one step and raises another one by one step. It keeps the code
when it moves a unit between two message digits (the checksum is unchanged), when it lowers a
message digit and raises the last checksum digit (the checksum grows by one), or when it raises a
message digit and lowers the last checksum digit (the checksum shrinks by one). Except for the all-zero and all-fifteen message words, every codeword has
at least `31` such neighbors. -/

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace Xmss.Checksum

/-! ### Every codeword is the encoding of a digest -/

theorem messagePart_injective_of_valid {x y : Encoding} (hx : Valid x) (hy : Valid y)
    (h : messagePart x = messagePart y) : x = y := by
  funext chain
  rcases chain_cases chain with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact congrFun h i
  · rw [hx j, hy j, h]

theorem card_messageDigits :
    Fintype.card (Fin messageDigits → Digit) = 2 ^ digestBits := by
  norm_num [messageDigits, chainLength, winternitzBits, digestBits]

/-- The encoding is a bijection from digests onto the code. -/
theorem exists_digest_of_valid {x : Encoding} (hx : Valid x) : ∃ digest, encode digest = x := by
  let toCode : Digest → {x : Encoding // Valid x} := fun digest => ⟨encode digest, encode_valid digest⟩
  have hinj : Function.Injective toCode := fun left right h =>
    encode_injective (congrArg Subtype.val h)
  let toMessage : {x : Encoding // Valid x} → (Fin messageDigits → Digit) :=
    fun x => messagePart x.1
  have hmessage : Function.Injective toMessage := fun left right h =>
    Subtype.ext (messagePart_injective_of_valid left.2 right.2 h)
  have hcard : Fintype.card Digest = Fintype.card {x : Encoding // Valid x} := by
    apply le_antisymm (Fintype.card_le_of_injective toCode hinj)
    calc
      _ ≤ _ := Fintype.card_le_of_injective toMessage hmessage
      _ = 2 ^ digestBits := card_messageDigits
      _ = _ := by simp
  obtain ⟨digest, hdigest⟩ :=
    ((Fintype.bijective_iff_injective_and_card toCode).2 ⟨hinj, hcard⟩).2 ⟨x, hx⟩
  exact ⟨digest, congrArg Subtype.val hdigest⟩

namespace Attack

abbrev DecreasingChain (encoding : Encoding) :=
  {chain : ChainIndex // 0 < (encoding chain).val}

abbrev IncreasingChain (encoding : Encoding) :=
  {chain : ChainIndex // (encoding chain).val + 1 < chainLength}

/-- Decrease the first chain and increase a distinct second chain. -/
abbrev DigitTransfer (encoding : Encoding) :=
  Σ lower : DecreasingChain encoding,
    {upper : ChainIndex // (encoding upper).val + 1 < chainLength ∧ upper ≠ lower.1}

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

/-- The value of a transferred chain, as a natural number. -/
theorem transferEncoding_val (encoding : Encoding) (transfer : DigitTransfer encoding)
    (chain : ChainIndex) :
    (transferEncoding encoding transfer chain).val + (if chain = transfer.1.1 then 1 else 0) =
      (encoding chain).val + (if chain = transfer.2.1 then 1 else 0) := by
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

/-! ### The transfers that keep the code -/

/-- Message digits that can be raised within the code. -/
def raisable (encoding : Encoding) : Finset (Fin messageDigits) :=
  Finset.univ.filter fun i => (encoding (messageChain i)).val + 1 < chainLength

/-- Message digits that can be lowered. -/
def lowerable (encoding : Encoding) : Finset (Fin messageDigits) :=
  Finset.univ.filter fun i => 0 < (encoding (messageChain i)).val

theorem messageChain_ne_checksumChain (i : Fin messageDigits) (j : Fin checksumDigits) :
    messageChain i ≠ checksumChain j := by
  intro h
  have := congrArg Fin.val h
  simp only [messageChain_val, checksumChain_val] at this
  have := i.isLt
  simp only [messageDigits] at *
  omega

theorem messageChain_injective : Function.Injective messageChain := fun i j h =>
  Fin.ext (by simpa only [messageChain_val] using congrArg Fin.val h)

/-- The checksum of the message digits of a transferred word, through the pointwise identity of
`transferEncoding_val`. -/
theorem checksum_transfer (encoding : Encoding) (transfer : DigitTransfer encoding) :
    checksum (messagePart (transferEncoding encoding transfer)) +
        (if ∃ i, transfer.2.1 = messageChain i then 1 else 0) =
      checksum (messagePart encoding) + (if ∃ j, transfer.1.1 = messageChain j then 1 else 0) := by
  classical
  have hpoint : ∀ i : Fin messageDigits,
      (chainLength - 1 - (messagePart (transferEncoding encoding transfer) i).val) +
          (if messageChain i = transfer.2.1 then 1 else 0) =
        (chainLength - 1 - (messagePart encoding i).val) +
          (if messageChain i = transfer.1.1 then 1 else 0) := by
    intro i
    have hval := transferEncoding_val encoding transfer (messageChain i)
    have hbound := (transferEncoding encoding transfer (messageChain i)).isLt
    have hbound' := (encoding (messageChain i)).isLt
    simp only [messagePart] at *
    simp only [chainLength, winternitzBits] at *
    split_ifs at hval ⊢ <;> omega
  have hsum := congrArg (fun values : Fin messageDigits → ℕ => ∑ i, values i) (funext hpoint)
  simp only [Finset.sum_add_distrib] at hsum
  have hcount : ∀ chain : ChainIndex,
      (∑ i : Fin messageDigits, if messageChain i = chain then 1 else 0) =
        if ∃ i, chain = messageChain i then 1 else 0 := by
    intro chain
    split_ifs with h
    · obtain ⟨i, rfl⟩ := h
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        simp [messageChain_injective.ne hk]
      · simp
    · apply Finset.sum_eq_zero
      intro k _
      simp only [ite_eq_right_iff, one_ne_zero, imp_false]
      exact fun hk => h ⟨k, hk.symm⟩
  rw [hcount, hcount] at hsum
  exact hsum

/-- A transfer keeps the code when its checksum digits are those of the new checksum. -/
theorem transferEncoding_valid_of (encoding : Encoding) (_hvalid : Valid encoding)
    (transfer : DigitTransfer encoding)
    (_hroom : ∀ i, transfer.2.1 = messageChain i → (encoding (messageChain i)).val + 1 < chainLength)
    (hdigits : ∀ j, transferEncoding encoding transfer (checksumChain j) =
      checksumDigit (checksum (messagePart (transferEncoding encoding transfer))) j) :
    Valid (transferEncoding encoding transfer) :=
  hdigits

theorem raisable_room (encoding : Encoding) {i : Fin messageDigits} (hi : i ∈ raisable encoding) :
    (encoding (messageChain i)).val + 1 < chainLength :=
  (Finset.mem_filter.mp hi).2

/-- Lower message digit `j` and raise message digit `i`. -/
def messageTransfer (encoding : Encoding) (j i : Fin messageDigits) (hj : j ∈ lowerable encoding)
    (hi : i ∈ raisable encoding) (hne : i ≠ j) : DigitTransfer encoding :=
  ⟨⟨messageChain j, (Finset.mem_filter.mp hj).2⟩,
    ⟨messageChain i, raisable_room encoding hi, messageChain_injective.ne hne⟩⟩

theorem messageTransfer_valid (encoding : Encoding) (hvalid : Valid encoding)
    (j i : Fin messageDigits) (hj : j ∈ lowerable encoding) (hi : i ∈ raisable encoding)
    (hne : i ≠ j) : Valid (transferEncoding encoding (messageTransfer encoding j i hj hi hne)) := by
  let transfer := messageTransfer encoding j i hj hi hne
  apply transferEncoding_valid_of encoding hvalid transfer
  · intro k hk
    have : i = k := messageChain_injective hk
    subst this
    exact (Finset.mem_filter.mp hi).2
  · intro c
    have hsum := checksum_transfer encoding transfer
    have hup : ∃ k, transfer.2.1 = messageChain k := ⟨i, rfl⟩
    have hlow : ∃ k, transfer.1.1 = messageChain k := ⟨j, rfl⟩
    rw [if_pos hup, if_pos hlow] at hsum
    have hcsum : checksum (messagePart (transferEncoding encoding transfer)) =
        checksum (messagePart encoding) := by omega
    rw [hcsum, transferEncoding_other encoding transfer _
      (messageChain_ne_checksumChain j c).symm (messageChain_ne_checksumChain i c).symm]
    exact hvalid c

/-- The transfers that keep the code. -/
abbrev ValidTransfer (encoding : Encoding) :=
  {transfer : DigitTransfer encoding // Valid (transferEncoding encoding transfer)}

/-- The neighbor attack is analyzed on words with enough movable message digits: writing `L` for
the lowerable and `R` for the raisable message digits, the paper's neighbor count is
`|L| · |R| - |L ∩ R| = (|L| - 1) · (|R| - 1) + 31`, so this asks for at least `220` neighbors. -/
def GoodEncoding (encoding : Encoding) : Prop :=
  189 ≤ ((lowerable encoding).card - 1) * ((raisable encoding).card - 1)

instance : DecidablePred GoodEncoding := fun _ => by unfold GoodEncoding; infer_instance

/-- The pairs `(j, i)` with `j ≠ i`, `x_j ≥ 1`, and `x_i ≤ 2^w - 2`, as in the paper: moving one
unit between two message digits keeps the message digit sum, hence the checksum digits. There are
`|L| · |R| - |L ∩ R| = (|L| - 1) · (|R| - 1) + 31` of them, so a good codeword has at least
`189 + 31 = 220` neighbors. -/
theorem validTransfer_card_lower (encoding : Encoding) (hvalid : Valid encoding)
    (hgood : GoodEncoding encoding) :
    220 ≤ Fintype.card (ValidTransfer encoding) := by
  classical
  unfold GoodEncoding at hgood
  set lows := lowerable encoding with hlowsDef
  set highs := raisable encoding with hhighsDef
  -- Every message digit is either positive or below the top, so the two sets cover all digits.
  have hunion : lows ∪ highs = Finset.univ := by
    ext i
    have hlt := (encoding (messageChain i)).isLt
    norm_num [chainLength, winternitzBits] at hlt
    simp only [hlowsDef, hhighsDef, lowerable, raisable, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true, chainLength, winternitzBits]
    omega
  have hcover : lows.card + highs.card = 32 + (lows ∩ highs).card := by
    have hcards := Finset.card_union_add_card_inter lows highs
    rw [hunion, Finset.card_univ] at hcards
    simpa [messageDigits] using hcards.symm
  have hparts := Finset.card_inter_add_card_sdiff lows highs
  -- `189 ≤ (|L| - 1) · (|R| - 1)` forces both sets to be nonempty.
  have hlowPos : 1 ≤ lows.card := by
    rcases Nat.eq_zero_or_pos lows.card with hzero | hpos
    · rw [hzero] at hgood; simp at hgood
    · exact hpos
  have hhighPos : 1 ≤ highs.card := by
    rcases Nat.eq_zero_or_pos highs.card with hzero | hpos
    · rw [hzero] at hgood; simp at hgood
    · exact hpos
  obtain ⟨lowered, hlowered⟩ : ∃ lowered, lows.card = lowered + 1 := ⟨lows.card - 1, by omega⟩
  obtain ⟨partners, hpartners⟩ : ∃ partners, highs.card = partners + 1 := ⟨highs.card - 1, by omega⟩
  have hproduct : 189 ≤ lowered * partners := by
    rw [hlowered, hpartners] at hgood
    simpa using hgood
  -- The ordered pairs of a lowerable and a distinct raisable digit, as valid transfers.
  let transfers : (Σ lower : {j // j ∈ lows}, {i // i ∈ highs.erase lower.1}) →
      ValidTransfer encoding := fun pair =>
    ⟨messageTransfer encoding pair.1.1 pair.2.1 pair.1.2
        (Finset.mem_of_mem_erase pair.2.2) (Finset.ne_of_mem_erase pair.2.2),
      messageTransfer_valid encoding hvalid _ _ _ _ _⟩
  have hinj : Function.Injective transfers := by
    rintro ⟨⟨lowerLeft, hlowerLeft⟩, ⟨upperLeft, hupperLeft⟩⟩
      ⟨⟨lowerRight, hlowerRight⟩, ⟨upperRight, hupperRight⟩⟩ heq
    have hlower := congrArg (fun transfer : ValidTransfer encoding => transfer.1.1.1) heq
    have hupper := congrArg (fun transfer : ValidTransfer encoding => transfer.1.2.1) heq
    obtain rfl := messageChain_injective hlower
    obtain rfl := messageChain_injective hupper
    rfl
  have hcard := Fintype.card_le_of_injective transfers hinj
  rw [Fintype.card_sigma] at hcard
  simp only [Fintype.card_coe] at hcard
  rw [← Finset.sum_subtype lows (fun j => by simp [hlowsDef])
    fun j => (highs.erase j).card] at hcard
  -- Split the lowerable digits by whether they are also raisable.
  have hinter : ∑ j ∈ lows ∩ highs, (highs.erase j).card
      = (lows ∩ highs).card * (highs.card - 1) := by
    rw [Finset.sum_congr rfl fun j hj => Finset.card_erase_of_mem (Finset.mem_inter.mp hj).2,
      Finset.sum_const, smul_eq_mul]
  have hdiff : ∑ j ∈ lows \ highs, (highs.erase j).card = (lows \ highs).card * highs.card := by
    rw [Finset.sum_congr rfl fun j hj => congrArg Finset.card
      (Finset.erase_eq_of_notMem (Finset.mem_sdiff.mp hj).2), Finset.sum_const, smul_eq_mul]
  rw [← Finset.sum_inter_add_sum_sdiff lows highs fun j => (highs.erase j).card, hinter, hdiff,
    hpartners] at hcard
  -- `|L ∩ R| · (|R| - 1) + |L \ R| · |R| = (|L| - 1) · (|R| - 1) + |R| - 1 + |L \ R|`.
  have hsum : (lows ∩ highs).card * (partners + 1 - 1) + (lows \ highs).card * (partners + 1)
      = lowered * partners + (partners + (lows \ highs).card) := by
    have hmd : (lows ∩ highs).card + (lows \ highs).card = lowered + 1 := by omega
    have hregroup : (lows ∩ highs).card * partners + (lows \ highs).card * (partners + 1)
        = ((lows ∩ highs).card + (lows \ highs).card) * partners + (lows \ highs).card := by ring
    simp only [Nat.add_sub_cancel]
    rw [hregroup, hmd]
    ring
  rw [hsum] at hcard
  have hrest : partners + (lows \ highs).card = 31 := by omega
  rw [hrest] at hcard
  omega

/-! ### The neighbor digests -/

/-- The digest of a codeword. -/
noncomputable def digestOfEncoding (encoding : Encoding) : Digest :=
  if hvalid : Valid encoding then Classical.choose (exists_digest_of_valid hvalid) else 0

theorem encode_digestOfEncoding (encoding : Encoding) (hvalid : Valid encoding) :
    encode (digestOfEncoding encoding) = encoding := by
  unfold digestOfEncoding
  rw [dif_pos hvalid]
  exact Classical.choose_spec (exists_digest_of_valid hvalid)

theorem digestOfEncoding_decode (encoding : Encoding) (hvalid : Valid encoding) :
    decodeDigest (digestOfEncoding encoding) = some encoding := by
  unfold decodeDigest
  rw [encode_digestOfEncoding encoding hvalid]

/-- The transfers that keep the code. -/
noncomputable def neighborTransfers (encoding : Encoding) : Finset (DigitTransfer encoding) := by
  classical
  exact Finset.univ.filter fun transfer => Valid (transferEncoding encoding transfer)

theorem mem_neighborTransfers {encoding : Encoding} {transfer : DigitTransfer encoding} :
    transfer ∈ neighborTransfers encoding ↔ Valid (transferEncoding encoding transfer) := by
  classical
  unfold neighborTransfers
  simp

noncomputable def neighborDigests (encoding : Encoding) : Finset Digest :=
  (neighborTransfers encoding).image fun transfer =>
    digestOfEncoding (transferEncoding encoding transfer)

theorem neighborDigests_card (encoding : Encoding) :
    (neighborDigests encoding).card = (neighborTransfers encoding).card := by
  unfold neighborDigests
  apply Finset.card_image_of_injOn
  intro left hleft right hright heq
  apply transferEncoding_injective encoding
  have hl := encode_digestOfEncoding _ (mem_neighborTransfers.mp hleft)
  have hr := encode_digestOfEncoding _ (mem_neighborTransfers.mp hright)
  rw [← hl, ← hr]
  exact congrArg encode heq

theorem neighborTransfers_card (encoding : Encoding) :
    (neighborTransfers encoding).card = Fintype.card (ValidTransfer encoding) := by
  classical
  unfold neighborTransfers
  rw [Fintype.card_subtype]

theorem neighborDigests_card_lower (encoding : Encoding) (hvalid : Valid encoding)
    (hgood : GoodEncoding encoding) :
    220 ≤ (neighborDigests encoding).card := by
  rw [neighborDigests_card, neighborTransfers_card]
  exact validTransfer_card_lower encoding hvalid hgood

/-- info: 'Xmss.Checksum.Attack.neighborDigests_card_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neighborDigests_card_lower

end Attack

end Xmss.Checksum
