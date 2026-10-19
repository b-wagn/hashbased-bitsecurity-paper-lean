import XmssSecurity.Proof.Checksum.EncodingProbability
import XmssSecurity.Proof.Checksum.Code

/-! Codewords obtained from a codeword by moving one unit from one chain to another.

A transfer lowers one chain by one step and raises another one by one step. It keeps the code
when it moves a unit between two message digits (the checksum is unchanged), when it lowers a
message digit and raises the last checksum digit (the checksum grows by one), or when it raises a
message digit and lowers the last checksum digit (the checksum shrinks by one). Except for the all-zero and all-fifteen message words, every codeword has
at least `31` such neighbors. -/

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum

namespace Checksum

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

end Checksum

namespace Attack

open Checksum

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

/-! ### The three kinds of transfers that keep the code -/

/-- The last checksum digit, of weight one. -/
def lastChecksumChain : ChainIndex := checksumChain ⟨2, by decide⟩

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
theorem transferEncoding_valid_of (encoding : Encoding) (hvalid : Valid encoding)
    (transfer : DigitTransfer encoding)
    (hroom : ∀ i, transfer.2.1 = messageChain i → (encoding (messageChain i)).val + 1 < chainLength)
    (hdigits : ∀ j, transferEncoding encoding transfer (checksumChain j) =
      checksumDigit (checksum (messagePart (transferEncoding encoding transfer))) j) :
    Valid (transferEncoding encoding transfer) :=
  hdigits

theorem checksumChain_injective : Function.Injective checksumChain := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simp only [checksumChain_val] at this; omega)

theorem lastChecksumChain_ne_messageChain (i : Fin messageDigits) :
    lastChecksumChain ≠ messageChain i :=
  (messageChain_ne_checksumChain i _).symm

/-- The last checksum digit is the checksum modulo `2^w`. -/
theorem lastChecksumDigit_eq (encoding : Encoding) (hvalid : Valid encoding) :
    (encoding lastChecksumChain).val = checksum (messagePart encoding) % chainLength := by
  unfold lastChecksumChain
  rw [hvalid]
  simp [checksumDigit, checksumDigits]

theorem raisable_room (encoding : Encoding) {i : Fin messageDigits} (hi : i ∈ raisable encoding) :
    (encoding (messageChain i)).val + 1 < chainLength :=
  (Finset.mem_filter.mp hi).2

/-- Lower message digit `j` and raise message digit `i`. -/
def messageTransfer (encoding : Encoding) (j i : Fin messageDigits) (hj : j ∈ lowerable encoding)
    (hi : i ∈ raisable encoding) (hne : i ≠ j) : DigitTransfer encoding :=
  ⟨⟨messageChain j, (Finset.mem_filter.mp hj).2⟩,
    ⟨messageChain i, raisable_room encoding hi, messageChain_injective.ne hne⟩⟩

/-- Lower message digit `j` and raise the last checksum digit. -/
def lowerTransfer (encoding : Encoding) (j : Fin messageDigits) (hj : j ∈ lowerable encoding)
    (hc : (encoding lastChecksumChain).val + 1 < chainLength) : DigitTransfer encoding :=
  ⟨⟨messageChain j, (Finset.mem_filter.mp hj).2⟩,
    ⟨lastChecksumChain, hc, lastChecksumChain_ne_messageChain j⟩⟩

/-- Raise message digit `i` and lower the last checksum digit. -/
def raiseTransfer (encoding : Encoding) (i : Fin messageDigits) (hi : i ∈ raisable encoding)
    (hc : 0 < (encoding lastChecksumChain).val) : DigitTransfer encoding :=
  ⟨⟨lastChecksumChain, hc⟩,
    ⟨messageChain i, raisable_room encoding hi, (lastChecksumChain_ne_messageChain i).symm⟩⟩

theorem checksumChain_cases (j : Fin checksumDigits) :
    j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ ∨ j = ⟨2, by decide⟩ := by
  rcases j with ⟨_ | _ | _ | k, hj⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exfalso
    simp only [checksumDigits] at hj
    omega

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

theorem lowerTransfer_valid (encoding : Encoding) (hvalid : Valid encoding)
    (j : Fin messageDigits) (hj : j ∈ lowerable encoding)
    (hc : (encoding lastChecksumChain).val + 1 < chainLength) :
    Valid (transferEncoding encoding (lowerTransfer encoding j hj hc)) := by
  let transfer := lowerTransfer encoding j hj hc
  apply transferEncoding_valid_of encoding hvalid transfer
  · intro k hk
    exact absurd hk (lastChecksumChain_ne_messageChain k)
  · intro c
    have hsum := checksum_transfer encoding transfer
    have hup : ¬∃ k, transfer.2.1 = messageChain k := fun ⟨k, hk⟩ =>
      lastChecksumChain_ne_messageChain k hk
    have hlow : ∃ k, transfer.1.1 = messageChain k := ⟨j, rfl⟩
    rw [if_neg hup, if_pos hlow] at hsum
    have hlast := lastChecksumDigit_eq encoding hvalid
    simp only [chainLength, winternitzBits] at hc hlast
    set csum := checksum (messagePart encoding)
    rw [Nat.add_zero] at hsum
    rw [hsum]
    rcases checksumChain_cases c with rfl | rfl | rfl
    · rw [transferEncoding_other encoding transfer _ (messageChain_ne_checksumChain j _).symm
        (fun h => by have := checksumChain_injective h; simp at this), hvalid]
      ext
      simp only [checksumDigit, checksumDigits, chainLength, winternitzBits]
      omega
    · rw [transferEncoding_other encoding transfer _ (messageChain_ne_checksumChain j _).symm
        (fun h => by have := checksumChain_injective h; simp at this), hvalid]
      ext
      simp only [checksumDigit, checksumDigits, chainLength, winternitzBits]
      omega
    · ext
      have hupper : (transferEncoding encoding transfer lastChecksumChain).val =
          (encoding lastChecksumChain).val + 1 := transferEncoding_upper encoding transfer
      change (transferEncoding encoding transfer lastChecksumChain).val = _
      rw [hupper]
      simp only [checksumDigit, checksumDigits, chainLength, winternitzBits]
      omega

theorem raiseTransfer_valid (encoding : Encoding) (hvalid : Valid encoding)
    (i : Fin messageDigits) (hi : i ∈ raisable encoding)
    (hc : 0 < (encoding lastChecksumChain).val) :
    Valid (transferEncoding encoding (raiseTransfer encoding i hi hc)) := by
  let transfer := raiseTransfer encoding i hi hc
  apply transferEncoding_valid_of encoding hvalid transfer
  · intro k hk
    have : i = k := messageChain_injective hk
    subst this
    exact (Finset.mem_filter.mp hi).2
  · intro c
    have hsum := checksum_transfer encoding transfer
    have hup : ∃ k, transfer.2.1 = messageChain k := ⟨i, rfl⟩
    have hlow : ¬∃ k, transfer.1.1 = messageChain k := fun ⟨k, hk⟩ =>
      lastChecksumChain_ne_messageChain k hk
    rw [if_pos hup, if_neg hlow] at hsum
    have hlast := lastChecksumDigit_eq encoding hvalid
    simp only [chainLength, winternitzBits] at hc hlast
    set csum := checksum (messagePart encoding)
    rw [Nat.add_zero] at hsum
    have hcsum : checksum (messagePart (transferEncoding encoding transfer)) = csum - 1 := by
      omega
    rw [hcsum]
    rcases checksumChain_cases c with rfl | rfl | rfl
    · rw [transferEncoding_other encoding transfer _
        (fun h => by have := checksumChain_injective h; simp at this)
        (messageChain_ne_checksumChain i _).symm, hvalid]
      ext
      simp only [checksumDigit, checksumDigits, chainLength, winternitzBits]
      omega
    · rw [transferEncoding_other encoding transfer _
        (fun h => by have := checksumChain_injective h; simp at this)
        (messageChain_ne_checksumChain i _).symm, hvalid]
      ext
      simp only [checksumDigit, checksumDigits, chainLength, winternitzBits]
      omega
    · ext
      have hlower : (transferEncoding encoding transfer lastChecksumChain).val =
          (encoding lastChecksumChain).val - 1 := transferEncoding_lower encoding transfer
      change (transferEncoding encoding transfer lastChecksumChain).val = _
      rw [hlower]
      simp only [checksumDigit, checksumDigits, chainLength, winternitzBits]
      omega

/-! ### Counting the neighbors -/

/-- The transfers that keep the code. -/
abbrev ValidTransfer (encoding : Encoding) :=
  {transfer : DigitTransfer encoding // Valid (transferEncoding encoding transfer)}

theorem mem_lowerable_or_raisable (encoding : Encoding) (i : Fin messageDigits) :
    i ∈ lowerable encoding ∨ i ∈ raisable encoding := by
  by_cases h : 0 < (encoding (messageChain i)).val
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  · refine Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    have hbound : 16 ≤ chainLength := by decide
    omega

theorem card_lowerable_add_raisable (encoding : Encoding) :
    messageDigits ≤ (lowerable encoding).card + (raisable encoding).card := by
  have hunion : lowerable encoding ∪ raisable encoding = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    exact mem_lowerable_or_raisable encoding i
  calc
    messageDigits = (lowerable encoding ∪ raisable encoding).card := by simp [hunion]
    _ ≤ _ := Finset.card_union_le _ _

/-- The neighbor attack is analyzed on words with both a lowerable and a raisable message digit.
The excluded message parts are exactly the all-zero and all-fifteen words. -/
def GoodEncoding (encoding : Encoding) : Prop :=
  (lowerable encoding).Nonempty ∧ (raisable encoding).Nonempty

instance : DecidablePred GoodEncoding := fun _ => by unfold GoodEncoding; infer_instance

/-- Every codeword with a lowerable and a raisable message digit has at least `31` neighbors. -/
theorem validTransfer_card_lower (encoding : Encoding) (hvalid : Valid encoding)
    (hgood : GoodEncoding encoding) :
    31 ≤ Fintype.card (ValidTransfer encoding) := by
  have hsize := card_lowerable_add_raisable encoding
  simp only [messageDigits] at hsize
  let c := (encoding lastChecksumChain).val
  have hcle : c < 16 := (encoding lastChecksumChain).isLt
  -- Lowering transfers, available when the last checksum digit can be raised.
  have hlowerInj : ∀ hc : c + 1 < chainLength,
      Function.Injective (fun j : {j // j ∈ lowerable encoding} =>
        (⟨lowerTransfer encoding j.1 j.2 hc, lowerTransfer_valid encoding hvalid j.1 j.2 hc⟩ :
          ValidTransfer encoding)) := by
    intro hc left right h
    have := congrArg (fun t : ValidTransfer encoding => t.1.1.1) h
    exact Subtype.ext (messageChain_injective this)
  have hraiseInj : ∀ hc : 0 < c,
      Function.Injective (fun i : {i // i ∈ raisable encoding} =>
        (⟨raiseTransfer encoding i.1 i.2 hc, raiseTransfer_valid encoding hvalid i.1 i.2 hc⟩ :
          ValidTransfer encoding)) := by
    intro hc left right h
    have := congrArg (fun t : ValidTransfer encoding => t.1.2.1) h
    exact Subtype.ext (messageChain_injective this)
  by_cases hmid : 0 < c ∧ c + 1 < chainLength
  · -- Both kinds are available: at least `|lowerable| + |raisable| ≥ 32` transfers.
    let f := fun j : {j // j ∈ lowerable encoding} =>
      (⟨lowerTransfer encoding j.1 j.2 hmid.2, lowerTransfer_valid encoding hvalid j.1 j.2 hmid.2⟩ :
        ValidTransfer encoding)
    let g := fun i : {i // i ∈ raisable encoding} =>
      (⟨raiseTransfer encoding i.1 i.2 hmid.1, raiseTransfer_valid encoding hvalid i.1 i.2 hmid.1⟩ :
        ValidTransfer encoding)
    have hinj : Function.Injective (Sum.elim f g) := by
      refine (hlowerInj hmid.2).sumElim (hraiseInj hmid.1) ?_
      intro j i h
      have := congrArg (fun t : ValidTransfer encoding => t.1.2.1) h
      exact lastChecksumChain_ne_messageChain i this
    have hcard := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe] at hcard
    have hcard' : _ ≤ Fintype.card (ValidTransfer encoding) :=
      hcard.trans (le_of_eq (Fintype.card_congr (Equiv.refl _)))
    omega
  · have hedge : c = 0 ∨ c = 15 := by
      simp only [chainLength, winternitzBits, not_and_or, not_lt] at hmid
      omega
    have hlowerNonempty := hgood.1
    have hraiseNonempty := hgood.2
    rcases hedge with hzero | hfifteen
    · -- Lower any message digit and raise the checksum, or move a unit to a fixed lowerable digit's
      -- partners: at least `|lowerable| + |raisable| - 1` transfers.
      have hc : c + 1 < chainLength := by simp [chainLength, winternitzBits]; omega
      obtain ⟨j0, hj0⟩ := hlowerNonempty
      let f := fun j : {j // j ∈ lowerable encoding} =>
        (⟨lowerTransfer encoding j.1 j.2 hc, lowerTransfer_valid encoding hvalid j.1 j.2 hc⟩ :
          ValidTransfer encoding)
      let g := fun i : {i // i ∈ (raisable encoding).erase j0} =>
        (⟨messageTransfer encoding j0 i.1 hj0 (Finset.mem_of_mem_erase i.2)
            (Finset.ne_of_mem_erase i.2),
          messageTransfer_valid encoding hvalid j0 i.1 hj0 (Finset.mem_of_mem_erase i.2)
            (Finset.ne_of_mem_erase i.2)⟩ : ValidTransfer encoding)
      have hginj : Function.Injective g := by
        intro left right h
        have := congrArg (fun t : ValidTransfer encoding => t.1.2.1) h
        exact Subtype.ext (messageChain_injective this)
      have hinj : Function.Injective (Sum.elim f g) := by
        refine (hlowerInj hc).sumElim hginj ?_
        intro j i h
        have := congrArg (fun t : ValidTransfer encoding => t.1.2.1) h
        exact lastChecksumChain_ne_messageChain i.1 this
      have hcard := Fintype.card_le_of_injective _ hinj
      rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe] at hcard
      have hcard' : _ ≤ Fintype.card (ValidTransfer encoding) :=
        hcard.trans (le_of_eq (Fintype.card_congr (Equiv.refl _)))
      have herase := Finset.pred_card_le_card_erase (s := raisable encoding) (a := j0)
      omega
    · have hc : 0 < c := by omega
      obtain ⟨i0, hi0⟩ := hraiseNonempty
      let f := fun i : {i // i ∈ raisable encoding} =>
        (⟨raiseTransfer encoding i.1 i.2 hc, raiseTransfer_valid encoding hvalid i.1 i.2 hc⟩ :
          ValidTransfer encoding)
      let g := fun j : {j // j ∈ (lowerable encoding).erase i0} =>
        (⟨messageTransfer encoding j.1 i0 (Finset.mem_of_mem_erase j.2) hi0
            (Finset.ne_of_mem_erase j.2).symm,
          messageTransfer_valid encoding hvalid j.1 i0 (Finset.mem_of_mem_erase j.2) hi0
            (Finset.ne_of_mem_erase j.2).symm⟩ : ValidTransfer encoding)
      have hginj : Function.Injective g := by
        intro left right h
        have := congrArg (fun t : ValidTransfer encoding => t.1.1.1) h
        exact Subtype.ext (messageChain_injective this)
      have hinj : Function.Injective (Sum.elim f g) := by
        refine (hraiseInj hc).sumElim hginj ?_
        intro i j h
        have := congrArg (fun t : ValidTransfer encoding => t.1.1.1) h
        exact lastChecksumChain_ne_messageChain j.1 this
      have hcard := Fintype.card_le_of_injective _ hinj
      rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe] at hcard
      have hcard' : _ ≤ Fintype.card (ValidTransfer encoding) :=
        hcard.trans (le_of_eq (Fintype.card_congr (Equiv.refl _)))
      have herase := Finset.pred_card_le_card_erase (s := lowerable encoding) (a := i0)
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
    31 ≤ (neighborDigests encoding).card := by
  rw [neighborDigests_card, neighborTransfers_card]
  exact validTransfer_card_lower encoding hvalid hgood

/-- info: 'XmssSecurity.Checksum.Attack.neighborDigests_card_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neighborDigests_card_lower

end Attack

end XmssSecurity.Checksum
