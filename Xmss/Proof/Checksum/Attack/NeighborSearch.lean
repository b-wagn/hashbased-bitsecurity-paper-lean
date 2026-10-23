import Xmss.Proof.Generic.Attack.HashSearch
import Xmss.Proof.Checksum.Attack.EncodingNeighbors
import Xmss.Proof.Generic.Attack.MutationSigningCache
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Checksum.EncodingProbability
/-! Searching fresh encoding inputs for one of the valid neighboring encodings. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open Xmss.Generic

namespace Xmss.Checksum.Attack

open Hashing Wots Merkle Verify Keygen Signing

def neighborSearchSteps : ℕ := 2 ^ 122

def neighborSearchInput (parameter : PublicParameter) (leafIndex : LeafIndex) (message : Message)
    (position : ℕ) : HashInput :=
  CacheView.encodingInput parameter leafIndex (message, BitVec.ofNat digestBits position)

noncomputable def findEncodingNeighbor (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (encoding : Encoding) : OracleComp HashSpec (Option (ℕ × Digest)) := by
  classical
  exact Attack.findHash (neighborSearchInput parameter leafIndex message)
    (fun output => output ∈ neighborDigests encoding) 0 neighborSearchSteps

theorem neighborSearchInput_separate (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (i j : ℕ) (hi : i < neighborSearchSteps) (hj : j < neighborSearchSteps)
    (hne : i ≠ j) : neighborSearchInput parameter leafIndex message i ≠
      neighborSearchInput parameter leafIndex message j := by
  intro heq
  have hrandomness := congrArg Prod.snd (CacheView.encodingInput_injective parameter leafIndex heq)
  have hnat := congrArg BitVec.toNat hrandomness
  have hbound : neighborSearchSteps ≤ 2 ^ digestBits := by norm_num [neighborSearchSteps, digestBits]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hi.trans_le hbound),
    Nat.mod_eq_of_lt (hj.trans_le hbound)] at hnat
  exact hne hnat

noncomputable def neighborAcceptanceProbability (encoding : Encoding) : ℝ≥0∞ :=
  (neighborDigests encoding).card / ((2 ^ digestBits : ℕ) : ℝ≥0∞)

theorem neighborAcceptanceProbability_lower (encoding : Encoding) (hvalid : Code.Valid encoding)
    (hgood : GoodEncoding encoding) :
    220 / ((2 ^ digestBits : ℕ) : ℝ≥0∞) ≤ neighborAcceptanceProbability encoding := by
  apply ENNReal.div_le_div_right
  exact_mod_cast neighborDigests_card_lower encoding hvalid hgood

theorem neighborAcceptanceProbability_le_one (encoding : Encoding) : neighborAcceptanceProbability encoding ≤ 1 := by
  rw [neighborAcceptanceProbability, ← RandomOracle.uniform_mem_probability]
  exact probEvent_le_one

/-- `(1 - p)^n ≤ e^(-n p) ≤ 1 / (1 + n p + (n p)^2 / 2 + (n p)^3 / 6)`, here with
`n p ≥ 220 · 2^122 / 2^128`. -/
theorem neighbor_rejection_power_lt_sixth (encoding : Encoding) (hvalid : Code.Valid encoding)
    (hgood : GoodEncoding encoding) :
    (1 - neighborAcceptanceProbability encoding) ^ neighborSearchSteps < 1 / 6 := by
  set a := neighborAcceptanceProbability encoding
  have ha1 : a ≤ 1 := neighborAcceptanceProbability_le_one encoding
  have hlow := neighborAcceptanceProbability_lower encoding hvalid hgood
  have hafinite : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha1
  have hlowReal : (220 : ℝ) / 2 ^ 128 ≤ a.toReal := by
    have h := (ENNReal.toReal_le_toReal (by finiteness) hafinite).mpr hlow
    rw [ENNReal.toReal_div] at h
    norm_num [digestBits] at h ⊢
    exact h
  have haReal : a.toReal ≤ 1 := by
    simpa using (ENNReal.toReal_le_toReal hafinite ENNReal.one_ne_top).mpr ha1
  set y : ℝ := (neighborSearchSteps : ℝ) * a.toReal
  have hexp : ((1 - a) ^ neighborSearchSteps).toReal ≤ Real.exp (-y) := by
    rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le ha1 ENNReal.one_ne_top, ENNReal.toReal_one]
    calc
      (1 - a.toReal) ^ neighborSearchSteps ≤ (Real.exp (-a.toReal)) ^ neighborSearchSteps :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-a.toReal)]) _
      _ = _ := by rw [← Real.exp_nat_mul]; ring_nf; rfl
  have hy : (55 : ℝ) / 16 ≤ y := by
    have : (neighborSearchSteps : ℝ) = 2 ^ 122 := by norm_num [neighborSearchSteps]
    change (55 : ℝ) / 16 ≤ (neighborSearchSteps : ℝ) * a.toReal
    rw [this]
    calc
      (55 : ℝ) / 16 = 2 ^ 122 * (220 / 2 ^ 128) := by norm_num
      _ ≤ _ := by gcongr
  have hcubic := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ y by linarith) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hcubic
  have hy2 : (55 / 16 : ℝ) ^ 2 ≤ y ^ 2 := by gcongr
  have hy3 : (55 / 16 : ℝ) ^ 3 ≤ y ^ 3 := by gcongr
  have hsixth : Real.exp (-y) < 1 / 6 := by
    rw [Real.exp_neg]
    have hpos : 0 < Real.exp y := Real.exp_pos y
    rw [inv_lt_comm₀ hpos (by norm_num)]
    nlinarith
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  calc
    _ ≤ _ := hexp
    _ < _ := by simpa using hsixth

theorem uniform_reject_neighbors (encoding : Encoding) :
    Pr[fun output : Digest => output ∉ neighborDigests encoding | $ᵗ Digest] =
      1 - neighborAcceptanceProbability encoding := by
  classical
  apply ENNReal.eq_sub_of_add_eq (by unfold neighborAcceptanceProbability; finiteness)
  simpa only [RandomOracle.uniform_mem_probability, probFailure_uniformSample, tsub_zero,
    neighborAcceptanceProbability, add_comm] using
      probEvent_compl ($ᵗ Digest) (fun output => output ∈ neighborDigests encoding)

theorem findEncodingNeighbor_failure_fresh (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (encoding : Encoding) (cache : QueryCache HashSpec)
    (hfresh : ∀ i, i < neighborSearchSteps → cache (neighborSearchInput parameter leafIndex message i) = none) :
    Pr[fun result => result.1 = none |
      (simulateQ randomOracle (findEncodingNeighbor parameter leafIndex message encoding)).run cache] =
      (1 - neighborAcceptanceProbability encoding) ^ neighborSearchSteps := by
  classical
  unfold findEncodingNeighbor
  rw [Attack.findHash_failure_fresh]
  · rw [uniform_reject_neighbors]
  · intro i _ hi j _ hj hne
    exact neighborSearchInput_separate parameter leafIndex message i j (by omega) (by omega) hne
  · intro i _ hi
    exact hfresh i (by omega)

theorem neighborSearchInput_fresh_after_signing
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅))
    (request : SignRequest) (answer : Option Generic.Signature) (signCache : QueryCache HashSpec)
    (hsign : (answer, signCache) ∈ support ((simulateQ romImpl
      (Signing.precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2))
    (message : Message) (hne : message ≠ request.message) (position : ℕ) :
    signCache (neighborSearchInput keyResult.1.2.parameter request.epoch message position) = none := by
  rw [Signing.precomputedCappedSign] at hsign
  have hagree := Signing.precomputedSignBoundedAttempts_preserves_unqueriedInput signingAttemptLimit
    keyResult.1.2 request.epoch request.message
    (neighborSearchInput keyResult.1.2.parameter request.epoch message position) (by
      intro randomness heq
      have hpair := CacheView.encodingInput_injective keyResult.1.2.parameter request.epoch heq
      exact hne (congrArg Prod.fst hpair).symm)
    keyResult.2 signCache answer hsign
  rw [hagree]
  exact Keygen.keygen_cache_none_encodingInput _ (Keygen.precomputedKeygen_support_oldKeygen keyResult hkey)
    request.epoch _

theorem findEncodingNeighbor_success_after_signing
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅))
    (request : SignRequest) (answer : Option Generic.Signature) (signCache : QueryCache HashSpec)
    (hsign : (answer, signCache) ∈ support ((simulateQ romImpl
      (Signing.precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2))
    (message : Message) (hne : message ≠ request.message)
    (encoding : Encoding) (hvalid : Code.Valid encoding)
    (hgood : GoodEncoding encoding) :
    5 / 6 < Pr[fun result => result.1 ≠ none |
      (simulateQ randomOracle (findEncodingNeighbor keyResult.1.2.parameter request.epoch message encoding)).run signCache] := by
  let computation := (simulateQ randomOracle
    (findEncodingNeighbor keyResult.1.2.parameter request.epoch message encoding)).run signCache
  have hfailure : Pr[fun result => result.1 = none | computation] < 1 / 6 := by
    rw [findEncodingNeighbor_failure_fresh _ _ _ _ _ (fun i _ =>
      neighborSearchInput_fresh_after_signing keyResult hkey request answer signCache hsign message hne i)]
    exact neighbor_rejection_power_lt_sixth encoding hvalid hgood
  have hsum : Pr[fun result => result.1 = none | computation] +
      Pr[fun result => result.1 ≠ none | computation] = 1 := by
    simpa only [probFailure_of_liftM_PMF, tsub_zero] using
      probEvent_compl computation (fun result => result.1 = none)
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top, ENNReal.toReal_one] at hr
  have hf := (ENNReal.toReal_lt_toReal probEvent_ne_top (by finiteness)).mpr hfailure
  apply (ENNReal.toReal_lt_toReal (by finiteness) probEvent_ne_top).mp
  norm_num [ENNReal.toReal_div] at hf ⊢
  change 5 / 6 < (Pr[fun result => result.1 ≠ none | computation]).toReal
  linarith

theorem findEncodingNeighbor_queryBound (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (encoding : Encoding) :
    (findEncodingNeighbor parameter leafIndex message encoding).IsQueryBoundP (fun _ => True) neighborSearchSteps := by
  unfold findEncodingNeighbor
  exact Attack.findHash_queryBound _ _ _ _

/-- info: 'Xmss.Checksum.Attack.findEncodingNeighbor_success_after_signing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms findEncodingNeighbor_success_after_signing

/-- info: 'Xmss.Checksum.Attack.findEncodingNeighbor_queryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms findEncodingNeighbor_queryBound

end Xmss.Checksum.Attack
