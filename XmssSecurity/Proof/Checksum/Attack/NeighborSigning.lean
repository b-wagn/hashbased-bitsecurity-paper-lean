import XmssSecurity.Proof.Checksum.Attack.EncodingNeighbors
import XmssSecurity.Proof.Checksum.SigningSuccess

/-! The neighbor attack excludes the two constant message words. A fresh signature lands
outside these words with probability at least `127/128`. -/

open OracleComp OracleSpec ENNReal
open scoped BigOperators
open XmssSecurity.Generic

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000

namespace XmssSecurity.Checksum.Attack

open Checksum

private theorem messagePart_zero_of_not_lowerable (encoding : Encoding)
    (h : ¬(lowerable encoding).Nonempty) (i : Fin messageDigits) :
    (messagePart encoding i).val = 0 := by
  have hnot : ¬0 < (messagePart encoding i).val := by
    intro hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  omega

private theorem messagePart_max_of_not_raisable (encoding : Encoding)
    (h : ¬(raisable encoding).Nonempty) (i : Fin messageDigits) :
    (messagePart encoding i).val = 15 := by
  have hnot : ¬(messagePart encoding i).val + 1 < chainLength := by
    intro hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hbound := (messagePart encoding i).isLt
  simp [chainLength, winternitzBits] at hnot hbound
  omega

theorem badEncoding_card_le_two :
    (Finset.univ.filter fun digest : Digest => ¬GoodEncoding (encode digest)).card ≤ 2 := by
  classical
  let lows := Finset.univ.filter fun digest : Digest => ¬(lowerable (encode digest)).Nonempty
  let highs := Finset.univ.filter fun digest : Digest => ¬(raisable (encode digest)).Nonempty
  have hlows : lows.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro left hl right hr
    apply messageDigit_injective
    funext i
    apply Fin.ext
    rw [← messagePart_encode left, ← messagePart_encode right,
      messagePart_zero_of_not_lowerable _ (Finset.mem_filter.mp hl).2,
      messagePart_zero_of_not_lowerable _ (Finset.mem_filter.mp hr).2]
  have hhighs : highs.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro left hl right hr
    apply messageDigit_injective
    funext i
    apply Fin.ext
    rw [← messagePart_encode left, ← messagePart_encode right,
      messagePart_max_of_not_raisable _ (Finset.mem_filter.mp hl).2,
      messagePart_max_of_not_raisable _ (Finset.mem_filter.mp hr).2]
  have hsub : (Finset.univ.filter fun digest : Digest => ¬GoodEncoding (encode digest)) ⊆
      lows ∪ highs := by
    intro digest hdigest
    have h := (Finset.mem_filter.mp hdigest).2
    by_cases hl : (lowerable (encode digest)).Nonempty
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        fun hr => h ⟨hl, hr⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

theorem goodEncoding_uniform_lower :
    (127 / 128 : ℝ≥0∞) ≤ Pr[fun digest : Digest => GoodEncoding (encode digest) | $ᵗ Digest] := by
  classical
  have hbad : Pr[fun digest : Digest => ¬GoodEncoding (encode digest) | $ᵗ Digest] ≤
      2 / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
    rw [probEvent_uniformSample]
    simp only [card_bitVec]
    apply ENNReal.div_le_div_right
    exact_mod_cast badEncoding_card_le_two
  have hsum := probEvent_compl ($ᵗ Digest) (fun digest : Digest => GoodEncoding (encode digest))
  simp only [probFailure_uniformSample, tsub_zero] at hsum
  have hsmall : (2 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) ≤ 1 / 128 := by
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
      Concrete.CacheView.decodedEncoding result.2 parameter request.epoch
        (request.message, original.randomness) = some encoding ∧ GoodEncoding encoding

theorem goodSigningResult_lower
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) :
    (127 / 128 : ℝ≥0∞) ≤ Pr[GoodSigningResult keyResult.1.2.parameter request |
      (simulateQ romImpl (Concrete.precomputedCappedSign keyResult.1.2
        request.epoch request.message)).run keyResult.2] := by
  classical
  rw [Concrete.precomputedCappedSign, code_signingAttemptLimit]
  change _ ≤ Pr[_ | (simulateQ romImpl (Concrete.precomputedSignBoundedAttempts (0 + 1)
    keyResult.1.2 request.epoch request.message)).run keyResult.2]
  rw [Concrete.precomputedSignBoundedAttempts_run_succ_eq, probEvent_bind_eq_tsum]
  have hmass : ∑' randomness : Randomness, Pr[= randomness | $ᵗ Randomness] = 1 :=
    tsum_probOutput_eq_one' (by simp)
  calc
    _ = ∑' randomness : Randomness, Pr[= randomness | $ᵗ Randomness] * (127 / 128) := by
      rw [ENNReal.tsum_mul_right, hmass, one_mul]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro randomness
      apply mul_le_mul' le_rfl
      rw [Concrete.precomputedSignAttempt_run_fresh _ _ _ _ _
        (Concrete.precomputedKeygen_cache_none_encodingInput keyResult hkey request.epoch _), bind_map_left]
      have hdecode : ∀ digest : Digest, Code.decodeDigest digest = some (encode digest) := fun _ => rfl
      simp only [hdecode, Option.map_some, Concrete.precomputedSignBoundedAttemptsContinuation,
        bind_pure_comp, probEvent_map, Function.comp_def]
      refine goodEncoding_uniform_lower.trans (le_of_eq ?_)
      apply probEvent_congr' _ rfl
      intro digest _
      unfold GoodSigningResult
      have hcached := QueryCache.cacheQuery_self keyResult.2
        (Concrete.CacheView.encodingInput keyResult.1.2.parameter request.epoch
          (request.message, randomness)) digest
      simp only [Generic.Concrete.precomputedSignWithEncoding]
      rw [Concrete.CacheView.decodedEncoding_eq_of_cache_eq_some hcached,
        Concrete.CacheView.encodingHash, Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached, hdecode]
      simp

end XmssSecurity.Checksum.Attack
