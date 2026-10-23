import Xmss.Proof.Checksum.Attack.EncodingNeighbors
import Xmss.Proof.Checksum.SigningSuccess

/-! The neighbor attack needs a codeword with at least `220` neighbors, i.e. one with
`189 ≤ (|L| - 1) · (|R| - 1)` lowerable and raisable message digits. At most `2^63` of the
`2^128` digests fail this, so a fresh signature is good except with probability below `2^-65`;
downstream only the weaker bound `127/128` is used. -/

open OracleComp OracleSpec ENNReal
open scoped BigOperators
open Xmss.Generic

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 40000

namespace Xmss.Checksum.Attack

open Checksum

/-- The digit `0`, which cannot be lowered. -/
def zeroDigit : Digit := ⟨0, by norm_num [chainLength, winternitzBits]⟩

/-- The digit `2^w - 1`, which cannot be raised. -/
def topDigit : Digit := ⟨chainLength - 1, by norm_num [chainLength, winternitzBits]⟩

theorem zeroDigit_ne_topDigit : zeroDigit ≠ topDigit := by
  simp [zeroDigit, topDigit, Fin.ext_iff, chainLength, winternitzBits]

/-- The message positions carrying a given digit value. -/
def valuePositions (digits : Fin messageDigits → Digit) (value : Digit) :
    Finset (Fin messageDigits) :=
  Finset.univ.filter fun i => digits i = value

theorem mem_valuePositions {digits : Fin messageDigits → Digit} {value : Digit}
    {i : Fin messageDigits} : i ∈ valuePositions digits value ↔ digits i = value := by
  simp [valuePositions]

/-! ### Counting the words with many extreme digits

A word is pinned down by the positions of its extreme digits together with its values elsewhere.
Bounding the number of position sets by `2^32` is crude but enough. -/

/-- Words whose digits on `positions` are fixed to `value`: at most `16^(32 - |positions|)`. -/
theorem card_fixed_le (positions : Finset (Fin messageDigits)) (value : Digit) :
    (Finset.univ.filter fun digits : Fin messageDigits → Digit =>
        ∀ i ∈ positions, digits i = value).card
      ≤ chainLength ^ (messageDigits - positions.card) := by
  have hsub : (Finset.univ.filter fun digits : Fin messageDigits → Digit =>
        ∀ i ∈ positions, digits i = value) ⊆
      Fintype.piFinset fun i => if i ∈ positions then {value} else Finset.univ := by
    intro digits hdigits
    refine Fintype.mem_piFinset.mpr fun i => ?_
    by_cases hi : i ∈ positions
    · rw [if_pos hi]
      exact Finset.mem_singleton.mpr ((Finset.mem_filter.mp hdigits).2 i hi)
    · rw [if_neg hi]
      exact Finset.mem_univ _
  refine le_trans (Finset.card_le_card hsub) (le_of_eq ?_)
  rw [Fintype.card_piFinset,
    Finset.prod_congr rfl (fun i _ => show (if i ∈ positions then {value}
        else (Finset.univ : Finset Digit)).card = if i ∈ positions then 1 else chainLength by
      split <;> simp),
    Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter, Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.card_univ_sdiff, Fintype.card_fin, one_pow, one_mul]

/-- Words whose digits on `first` are fixed to `value` and on `second` to `other`:
at most `16^(32 - |first| - |second|)` when the two position sets are disjoint. -/
theorem card_fixed_pair_le (first second : Finset (Fin messageDigits)) (value other : Digit)
    (hdisjoint : Disjoint first second) :
    (Finset.univ.filter fun digits : Fin messageDigits → Digit =>
        (∀ i ∈ first, digits i = value) ∧ ∀ i ∈ second, digits i = other).card
      ≤ chainLength ^ (messageDigits - (first.card + second.card)) := by
  have hsub : (Finset.univ.filter fun digits : Fin messageDigits → Digit =>
        (∀ i ∈ first, digits i = value) ∧ ∀ i ∈ second, digits i = other) ⊆
      Fintype.piFinset fun i => if i ∈ first ∪ second
        then {if i ∈ first then value else other} else Finset.univ := by
    intro digits hdigits
    obtain ⟨hfirst, hsecond⟩ := (Finset.mem_filter.mp hdigits).2
    refine Fintype.mem_piFinset.mpr fun i => ?_
    by_cases hi : i ∈ first ∪ second
    · rw [if_pos hi]
      refine Finset.mem_singleton.mpr ?_
      by_cases hfirstMem : i ∈ first
      · rw [if_pos hfirstMem]
        exact hfirst i hfirstMem
      · rw [if_neg hfirstMem]
        exact hsecond i ((Finset.mem_union.mp hi).resolve_left hfirstMem)
    · rw [if_neg hi]
      exact Finset.mem_univ _
  refine le_trans (Finset.card_le_card hsub) (le_of_eq ?_)
  rw [Fintype.card_piFinset,
    Finset.prod_congr rfl (fun i _ => show (if i ∈ first ∪ second
        then {if i ∈ first then value else other} else (Finset.univ : Finset Digit)).card
        = if i ∈ first ∪ second then 1 else chainLength by split <;> simp),
    Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter, Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.card_univ_sdiff, Fintype.card_fin, one_pow, one_mul,
    Finset.card_union_of_disjoint hdisjoint]

/-- At most `2^32 · 16^(32 - threshold)` words carry `value` on `threshold` or more positions. -/
theorem card_many_le (value : Digit) (threshold : ℕ) :
    (Finset.univ.filter fun digits : Fin messageDigits → Digit =>
        threshold ≤ (valuePositions digits value).card).card
      ≤ 2 ^ 32 * chainLength ^ (messageDigits - threshold) := by
  set source := Finset.univ.filter fun digits : Fin messageDigits → Digit =>
    threshold ≤ (valuePositions digits value).card with hsource
  have hmaps : ∀ digits ∈ source, valuePositions digits value ∈
      (Finset.univ : Finset (Finset (Fin messageDigits))) := fun _ _ => Finset.mem_univ _
  have hfiber : ∀ positions ∈ (Finset.univ : Finset (Finset (Fin messageDigits))),
      (source.filter fun digits => valuePositions digits value = positions).card
        ≤ chainLength ^ (messageDigits - threshold) := by
    intro positions _
    rcases Finset.eq_empty_or_nonempty
      (source.filter fun digits => valuePositions digits value = positions) with hempty | hwitness
    · simp [hempty]
    · obtain ⟨witness, hmem⟩ := hwitness
      have hpositions : threshold ≤ positions.card := by
        have hmany := (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
        rwa [(Finset.mem_filter.mp hmem).2] at hmany
      refine le_trans (Finset.card_le_card ?_) (le_trans (card_fixed_le positions value)
        (Nat.pow_le_pow_right (by norm_num [chainLength, winternitzBits]) (by omega)))
      intro digits hdigits
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => ?_⟩
      exact mem_valuePositions.mp ((Finset.mem_filter.mp hdigits).2 ▸ hi)
  refine le_trans (Finset.card_le_mul_card_image_of_maps_to hmaps _ hfiber) (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin, Nat.mul_comm]
  norm_num [messageDigits]

/-- At most `2^57` words carry `value` on `23` or more positions and `other` on `5` or more:
there are at most `2^32` position sets for `value`, at most `2^9` subsets of the remaining `9`
positions for `other`, and at most `16^4` ways to fill the rest. -/
theorem card_many_pair_le (value other : Digit) (hne : value ≠ other) :
    (Finset.univ.filter fun digits : Fin messageDigits → Digit =>
        23 ≤ (valuePositions digits value).card ∧
          5 ≤ (valuePositions digits other).card).card ≤ 2 ^ 57 := by
  set source := Finset.univ.filter fun digits : Fin messageDigits → Digit =>
    23 ≤ (valuePositions digits value).card ∧
      5 ≤ (valuePositions digits other).card with hsource
  -- For a fixed set of `value` positions, the `other` positions range over its complement.
  have hinner : ∀ first : Finset (Fin messageDigits),
      (source.filter fun digits => valuePositions digits value = first).card ≤ 2 ^ 25 := by
    intro first
    set inner := source.filter fun digits => valuePositions digits value = first with hinnerDef
    rcases Finset.eq_empty_or_nonempty inner with hempty | hwitness
    · rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    · obtain ⟨witness, hmem⟩ := hwitness
      have hfirstCard : 23 ≤ first.card := by
        have hvalue : 23 ≤ (valuePositions witness value).card :=
          ((Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2).1
        rwa [(Finset.mem_filter.mp hmem).2] at hvalue
      have hmaps : ∀ digits ∈ inner, valuePositions digits other ∈ firstᶜ.powerset := by
        intro digits hdigits
        refine Finset.mem_powerset.mpr fun i hi => ?_
        refine Finset.mem_compl.mpr fun hmem' => hne ?_
        have hvalues : valuePositions digits value = first := (Finset.mem_filter.mp hdigits).2
        rw [← mem_valuePositions.mp (hvalues ▸ hmem' : i ∈ valuePositions digits value),
          mem_valuePositions.mp hi]
      have hfiber : ∀ second ∈ firstᶜ.powerset,
          (inner.filter fun digits => valuePositions digits other = second).card
            ≤ chainLength ^ 4 := by
        intro second hsecond
        rcases Finset.eq_empty_or_nonempty
          (inner.filter fun digits => valuePositions digits other = second) with hempty | hwit
        · rw [hempty, Finset.card_empty]
          exact Nat.zero_le _
        · obtain ⟨inhabitant, hinhabitant⟩ := hwit
          have hsecondCard : 5 ≤ second.card := by
            have hother : 5 ≤ (valuePositions inhabitant other).card :=
              ((Finset.mem_filter.mp (Finset.mem_filter.mp
                (Finset.mem_filter.mp hinhabitant).1).1).2).2
            rwa [(Finset.mem_filter.mp hinhabitant).2] at hother
          have hdisjoint : Disjoint first second :=
            Finset.disjoint_left.mpr fun i hi hj =>
              (Finset.mem_compl.mp (Finset.mem_powerset.mp hsecond hj)) hi
          refine le_trans (Finset.card_le_card ?_)
            (le_trans (card_fixed_pair_le first second value other hdisjoint)
              (Nat.pow_le_pow_right (by norm_num [chainLength, winternitzBits])
                (by simp only [messageDigits]; omega)))
          intro digits hdigits
          have hvalues : valuePositions digits value = first :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp hdigits).1).2
          have hothers : valuePositions digits other = second := (Finset.mem_filter.mp hdigits).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            fun i hi => mem_valuePositions.mp (hvalues ▸ hi),
            fun i hi => mem_valuePositions.mp (hothers ▸ hi)⟩
      refine le_trans (Finset.card_le_mul_card_image_of_maps_to hmaps _ hfiber) ?_
      rw [Finset.card_powerset, Finset.card_compl, Fintype.card_fin]
      calc
        chainLength ^ 4 * 2 ^ (messageDigits - first.card)
            ≤ chainLength ^ 4 * 2 ^ 9 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
            (by simp only [messageDigits]; omega))
        _ = 2 ^ 25 := by norm_num [chainLength, winternitzBits]
  have hmaps : ∀ digits ∈ source, valuePositions digits value ∈
      (Finset.univ : Finset (Finset (Fin messageDigits))) := fun _ _ => Finset.mem_univ _
  refine le_trans (Finset.card_le_mul_card_image_of_maps_to hmaps (2 ^ 25)
    (fun first _ => hinner first)) (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  norm_num [messageDigits]

/-- The arithmetic behind the four bad regions: a word with few zeros and few top digits has
`189 ≤ (|L| - 1) · (|R| - 1)`, i.e. at least `220` neighbors. -/
theorem good_of_digit_counts {lows highs zeros tops : ℕ} (hlows : lows + zeros = 32)
    (hhighs : highs + tops = 32) (hboth : zeros + tops ≤ 32) (hzeros : zeros ≤ 24)
    (htops : tops ≤ 24) (hmixed : zeros ≤ 22 ∨ tops ≤ 4) (hmixed' : tops ≤ 22 ∨ zeros ≤ 4) :
    189 ≤ (lows - 1) * (highs - 1) := by
  obtain ⟨lowered, hlowered⟩ : ∃ lowered, lows = lowered + 1 := ⟨lows - 1, by omega⟩
  obtain ⟨raised, hraised⟩ : ∃ raised, highs = raised + 1 := ⟨highs - 1, by omega⟩
  subst hlowered
  subst hraised
  simp only [Nat.add_sub_cancel]
  rcases hmixed with hmixed | hmixed <;> rcases hmixed' with hmixed' | hmixed'
  · -- Both sets are large: `lowered + raised ≥ 30` with both at least `9`.
    obtain ⟨extra, hextra⟩ : ∃ extra, lowered = 9 + extra := ⟨lowered - 9, by omega⟩
    obtain ⟨extra', hextra'⟩ : ∃ extra', raised = 9 + extra' := ⟨raised - 9, by omega⟩
    subst hextra
    subst hextra'
    have hsum : 12 ≤ extra + extra' := by omega
    have hexpand : (9 + extra) * (9 + extra')
        = 81 + 9 * extra + 9 * extra' + extra * extra' := by ring
    rw [hexpand]
    generalize extra * extra' = product
    omega
  · have hlowered : 27 ≤ lowered := by omega
    have hraised : 7 ≤ raised := by omega
    calc (189 : ℕ) = 27 * 7 := by norm_num
      _ ≤ lowered * raised := Nat.mul_le_mul hlowered hraised
  · have hlowered : 7 ≤ lowered := by omega
    have hraised : 27 ≤ raised := by omega
    calc (189 : ℕ) = 7 * 27 := by norm_num
      _ ≤ lowered * raised := Nat.mul_le_mul hlowered hraised
  · have hlowered : 27 ≤ lowered := by omega
    have hraised : 7 ≤ raised := by omega
    calc (189 : ℕ) = 27 * 7 := by norm_num
      _ ≤ lowered * raised := Nat.mul_le_mul hlowered hraised

/-- A bad digest has `25` zero digits, `25` top digits, or `23` of one and `5` of the other, so
at most `2 · 2^60 + 2 · 2^57 ≤ 2^63` digests are bad: a `2^-65` fraction, as in the paper. -/
theorem badEncoding_card_le :
    (Finset.univ.filter fun digest : Digest => ¬GoodEncoding (encode digest)).card ≤ 2 ^ 63 := by
  set zeroMany := Finset.univ.filter fun digits : Fin messageDigits → Digit =>
    25 ≤ (valuePositions digits zeroDigit).card with hzeroMany
  set topMany := Finset.univ.filter fun digits : Fin messageDigits → Digit =>
    25 ≤ (valuePositions digits topDigit).card with htopMany
  set zeroHeavy := Finset.univ.filter fun digits : Fin messageDigits → Digit =>
    23 ≤ (valuePositions digits zeroDigit).card ∧
      5 ≤ (valuePositions digits topDigit).card with hzeroHeavy
  set topHeavy := Finset.univ.filter fun digits : Fin messageDigits → Digit =>
    23 ≤ (valuePositions digits topDigit).card ∧
      5 ≤ (valuePositions digits zeroDigit).card with htopHeavy
  have hbad : ∀ digest ∈ (Finset.univ.filter fun digest : Digest => ¬GoodEncoding (encode digest)),
      messageDigit digest ∈ (zeroMany ∪ topMany) ∪ (zeroHeavy ∪ topHeavy) := by
    intro digest hdigest
    have hnot : ¬GoodEncoding (encode digest) := (Finset.mem_filter.mp hdigest).2
    unfold GoodEncoding at hnot
    -- The zero positions are the non-lowerable ones, the top positions the non-raisable ones.
    have hzeroSplit : (lowerable (encode digest)).card +
        (valuePositions (messageDigit digest) zeroDigit).card = 32 := by
      have hneg : (Finset.univ.filter fun i : Fin messageDigits =>
          ¬0 < (encode digest (messageChain i)).val)
          = valuePositions (messageDigit digest) zeroDigit := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_valuePositions,
          encode_messageChain, zeroDigit, Fin.ext_iff]
        omega
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin messageDigits)))
        (p := fun i => 0 < (encode digest (messageChain i)).val)
      rw [hneg] at hsplit
      simpa [lowerable, messageDigits] using hsplit
    have htopSplit : (raisable (encode digest)).card +
        (valuePositions (messageDigit digest) topDigit).card = 32 := by
      have hneg : (Finset.univ.filter fun i : Fin messageDigits =>
          ¬(encode digest (messageChain i)).val + 1 < chainLength)
          = valuePositions (messageDigit digest) topDigit := by
        ext i
        have hlt := (encode digest (messageChain i)).isLt
        simp only [chainLength, winternitzBits] at hlt
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_valuePositions,
          encode_messageChain, topDigit, Fin.ext_iff, chainLength, winternitzBits]
        omega
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin messageDigits)))
        (p := fun i => (encode digest (messageChain i)).val + 1 < chainLength)
      rw [hneg] at hsplit
      simpa [raisable, messageDigits] using hsplit
    have hdisjoint : (valuePositions (messageDigit digest) zeroDigit).card +
        (valuePositions (messageDigit digest) topDigit).card ≤ 32 := by
      have hdisj : Disjoint (valuePositions (messageDigit digest) zeroDigit)
          (valuePositions (messageDigit digest) topDigit) :=
        Finset.disjoint_left.mpr fun i hi hj => zeroDigit_ne_topDigit
          (by rw [← mem_valuePositions.mp hi, mem_valuePositions.mp hj])
      have hunion := Finset.card_union_of_disjoint hdisj
      have hle := Finset.card_le_univ (valuePositions (messageDigit digest) zeroDigit ∪
        valuePositions (messageDigit digest) topDigit)
      rw [hunion, Fintype.card_fin] at hle
      simpa [messageDigits] using hle
    by_contra hmem
    simp only [Finset.mem_union, hzeroMany, htopMany, hzeroHeavy, htopHeavy, Finset.mem_filter,
      Finset.mem_univ, true_and, not_or, not_le, not_and_or] at hmem
    obtain ⟨⟨hzero, htop⟩, hleft, hright⟩ := hmem
    exact hnot (good_of_digit_counts hzeroSplit htopSplit hdisjoint (by omega) (by omega)
      (by rcases hleft with h | h <;> omega) (by rcases hright with h | h <;> omega))
  refine le_trans (Finset.card_le_card_of_injOn messageDigit hbad
    (fun left _ right _ heq => messageDigit_injective heq)) ?_
  have h1 : zeroMany.card ≤ 2 ^ 60 := by
    refine le_trans (card_many_le zeroDigit 25) (le_of_eq ?_)
    norm_num [chainLength, winternitzBits, messageDigits]
  have h2 : topMany.card ≤ 2 ^ 60 := by
    refine le_trans (card_many_le topDigit 25) (le_of_eq ?_)
    norm_num [chainLength, winternitzBits, messageDigits]
  have h3 : zeroHeavy.card ≤ 2 ^ 57 := card_many_pair_le zeroDigit topDigit zeroDigit_ne_topDigit
  have h4 : topHeavy.card ≤ 2 ^ 57 :=
    card_many_pair_le topDigit zeroDigit zeroDigit_ne_topDigit.symm
  have hfirst := Finset.card_union_le zeroMany topMany
  have hsecond := Finset.card_union_le zeroHeavy topHeavy
  have houter := Finset.card_union_le (zeroMany ∪ topMany) (zeroHeavy ∪ topHeavy)
  omega

/-- The bad digests are a `2^-65` fraction; `127/128` is all the rest of the proof needs. -/
theorem goodEncoding_uniform_lower :
    (127 / 128 : ℝ≥0∞) ≤ Pr[fun digest : Digest => GoodEncoding (encode digest) | $ᵗ Digest] := by
  classical
  have hbad : Pr[fun digest : Digest => ¬GoodEncoding (encode digest) | $ᵗ Digest] ≤
      2 ^ 63 / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
    rw [probEvent_uniformSample]
    simp only [card_bitVec]
    apply ENNReal.div_le_div_right
    exact_mod_cast badEncoding_card_le
  have hsum := probEvent_compl ($ᵗ Digest) (fun digest : Digest => GoodEncoding (encode digest))
  simp only [probFailure_uniformSample, tsub_zero] at hsum
  have hsmall : (2 ^ 63 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) ≤ 1 / 128 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [digestBits, ENNReal.toReal_div]
  apply ENNReal.le_of_add_le_add_right
    (a := Pr[fun digest : Digest => ¬GoodEncoding (encode digest) | $ᵗ Digest]) probEvent_ne_top
  calc
    (127 / 128 : ℝ≥0∞) + Pr[fun digest : Digest => ¬GoodEncoding (encode digest) | $ᵗ Digest] ≤
        127 / 128 + 1 / 128 := add_le_add le_rfl (hbad.trans hsmall)
    _ = 1 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num [ENNReal.toReal_div]
    _ = _ := hsum.symm

noncomputable def GoodSigningResult (parameter : PublicParameter) (request : SignRequest)
    (result : Option Generic.Signature × QueryCache HashSpec) : Prop :=
  match result.1 with
  | none => False
  | some original => ∃ encoding,
      CacheView.decodedEncoding result.2 parameter request.epoch
        (request.message, original.randomness) = some encoding ∧ GoodEncoding encoding

theorem goodSigningResult_lower
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅))
    (request : SignRequest) :
    (127 / 128 : ℝ≥0∞) ≤ Pr[GoodSigningResult keyResult.1.2.parameter request |
      (simulateQ romImpl (Signing.precomputedCappedSign keyResult.1.2
        request.epoch request.message)).run keyResult.2] := by
  classical
  rw [Signing.precomputedCappedSign, code_signingAttemptLimit]
  change _ ≤ Pr[_ | (simulateQ romImpl (Signing.precomputedSignBoundedAttempts (0 + 1)
    keyResult.1.2 request.epoch request.message)).run keyResult.2]
  rw [Signing.precomputedSignBoundedAttempts_run_succ_eq, probEvent_bind_eq_tsum]
  have hmass : ∑' randomness : Randomness, Pr[= randomness | $ᵗ Randomness] = 1 :=
    tsum_probOutput_eq_one' (by simp)
  calc
    _ = ∑' randomness : Randomness, Pr[= randomness | $ᵗ Randomness] * (127 / 128) := by
      rw [ENNReal.tsum_mul_right, hmass, one_mul]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro randomness
      apply mul_le_mul' le_rfl
      rw [Signing.precomputedSignAttempt_run_fresh _ _ _ _ _
        (Keygen.precomputedKeygen_cache_none_encodingInput keyResult hkey request.epoch _), bind_map_left]
      have hdecode : ∀ digest : Digest, Code.decodeDigest digest = some (encode digest) := fun _ => rfl
      simp only [hdecode, Option.map_some, Signing.precomputedSignBoundedAttemptsContinuation,
        bind_pure_comp, probEvent_map, Function.comp_def]
      refine goodEncoding_uniform_lower.trans (le_of_eq ?_)
      apply probEvent_congr' _ rfl
      intro digest _
      unfold GoodSigningResult
      have hcached := QueryCache.cacheQuery_self keyResult.2
        (CacheView.encodingInput keyResult.1.2.parameter request.epoch
          (request.message, randomness)) digest
      simp only [Generic.Signing.precomputedSignWithEncoding]
      rw [CacheView.decodedEncoding_eq_of_cache_eq_some hcached,
        CacheView.encodingHash, CacheView.digestAt_eq_of_cache_eq_some hcached, hdecode]
      simp

end Xmss.Checksum.Attack
