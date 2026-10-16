import XmssSecurity.Proof.Attack.HashSearch
import XmssSecurity.Proof.Attack.EncodingNeighbors
import XmssSecurity.Proof.Attack.MutationSigningCache

/-! Searching fresh encoding inputs for one of the valid neighboring encodings. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Attack

open Concrete

def neighborSearchSteps : ℕ := 2 ^ 121

def neighborSearchInput (parameter : PublicParameter) (leafIndex : LeafIndex) (message : Message)
    (position : ℕ) : HashInput :=
  CacheView.encodingInput parameter leafIndex (message, BitVec.ofNat randomnessBits position)

noncomputable def findEncodingNeighbor (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (encoding : Encoding) : OracleComp HashSpec (Option (ℕ × HashOutput)) := by
  classical
  exact findHash (neighborSearchInput parameter leafIndex message)
    (fun output => truncateHash output ∈ neighborDigests encoding) 0 neighborSearchSteps

theorem neighborSearchInput_separate (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (i j : ℕ) (hi : i < neighborSearchSteps) (hj : j < neighborSearchSteps)
    (hne : i ≠ j) : neighborSearchInput parameter leafIndex message i ≠
      neighborSearchInput parameter leafIndex message j := by
  intro heq
  have hrandomness := congrArg Prod.snd (CacheView.encodingInput_injective parameter leafIndex heq)
  have hnat := congrArg BitVec.toNat hrandomness
  have hbound : neighborSearchSteps ≤ 2 ^ randomnessBits := by norm_num [neighborSearchSteps, randomnessBits]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hi.trans_le hbound),
    Nat.mod_eq_of_lt (hj.trans_le hbound)] at hnat
  exact hne hnat

theorem uniform_truncate_mem_probability (targets : Finset Digest) :
    Pr[fun output : HashOutput => truncateHash output ∈ targets | $ᵗ HashOutput] =
      targets.card / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  classical
  change Pr[(fun value : Digest => value ∈ targets) ∘ truncateHash | $ᵗ HashOutput] = _
  rw [← probEvent_map, probEvent_def, Rom.evalDist_truncate_uniformHashOutput, ← probEvent_def,
    probEvent_uniformSample]
  simp

noncomputable def neighborAcceptanceProbability (encoding : Encoding) : ℝ≥0∞ :=
  (neighborDigests encoding).card / ((2 ^ digestBits : ℕ) : ℝ≥0∞)

theorem neighborAcceptanceProbability_lower (encoding : Encoding) (hvalid : Checksum.Valid encoding) :
    392 / ((2 ^ digestBits : ℕ) : ℝ≥0∞) ≤ neighborAcceptanceProbability encoding := by
  apply ENNReal.div_le_div_right
  exact_mod_cast neighborDigests_card_lower encoding hvalid

theorem neighborAcceptanceProbability_le_one (encoding : Encoding) : neighborAcceptanceProbability encoding ≤ 1 := by
  rw [neighborAcceptanceProbability, ← uniform_truncate_mem_probability]
  exact probEvent_le_one

theorem neighbor_rejection_power_lt_quarter (encoding : Encoding) (hvalid : Checksum.Valid encoding) :
    (1 - neighborAcceptanceProbability encoding) ^ neighborSearchSteps < 1 / 4 := by
  have hp := neighborAcceptanceProbability_lower encoding hvalid
  calc
    _ ≤ 1 / (1 + neighborSearchSteps * neighborAcceptanceProbability encoding) :=
      Checksum.rejection_power_le _ (neighborAcceptanceProbability_le_one encoding) _
    _ ≤ 1 / (1 + neighborSearchSteps * (392 / ((2 ^ digestBits : ℕ) : ℝ≥0∞))) := by gcongr
    _ < 1 / 4 := by
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_div, ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num [neighborSearchSteps, digestBits, ENNReal.toReal_div, ENNReal.toReal_mul]

theorem uniform_truncate_reject_neighbors (encoding : Encoding) :
    Pr[fun output : HashOutput => truncateHash output ∉ neighborDigests encoding | $ᵗ HashOutput] =
      1 - neighborAcceptanceProbability encoding := by
  classical
  apply ENNReal.eq_sub_of_add_eq (by unfold neighborAcceptanceProbability; finiteness)
  simpa only [uniform_truncate_mem_probability, probFailure_uniformSample, tsub_zero,
    neighborAcceptanceProbability, add_comm] using
      probEvent_compl ($ᵗ HashOutput) (fun output => truncateHash output ∈ neighborDigests encoding)

theorem findEncodingNeighbor_failure_fresh (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (encoding : Encoding) (cache : QueryCache HashSpec)
    (hfresh : ∀ i, i < neighborSearchSteps → cache (neighborSearchInput parameter leafIndex message i) = none) :
    Pr[fun result => result.1 = none |
      (simulateQ randomOracle (findEncodingNeighbor parameter leafIndex message encoding)).run cache] =
      (1 - neighborAcceptanceProbability encoding) ^ neighborSearchSteps := by
  classical
  unfold findEncodingNeighbor
  rw [findHash_failure_fresh]
  · rw [uniform_truncate_reject_neighbors]
  · intro i _ hi j _ hj hne
    exact neighborSearchInput_separate parameter leafIndex message i j (by omega) (by omega) hne
  · intro i _ hi
    exact hfresh i (by omega)

theorem neighborSearchInput_fresh_after_signing
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) (answer : Option Signature) (signCache : QueryCache HashSpec)
    (hsign : (answer, signCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2))
    (message : Message) (hne : message ≠ request.message) (position : ℕ) :
    signCache (neighborSearchInput keyResult.1.2.parameter request.epoch message position) = none := by
  rw [precomputedCappedSign] at hsign
  have hagree := precomputedSignBoundedAttempts_preserves_unqueriedInput signingAttemptLimit
    keyResult.1.2 request.epoch request.message
    (neighborSearchInput keyResult.1.2.parameter request.epoch message position) (by
      intro randomness heq
      have hpair := CacheView.encodingInput_injective keyResult.1.2.parameter request.epoch heq
      exact hne (congrArg Prod.fst hpair).symm)
    keyResult.2 signCache answer hsign
  rw [hagree]
  exact keygen_cache_none_encodingInput _ (precomputedKeygen_support_oldKeygen keyResult hkey)
    request.epoch _

theorem findEncodingNeighbor_success_after_signing
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) (answer : Option Signature) (signCache : QueryCache HashSpec)
    (hsign : (answer, signCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2))
    (message : Message) (hne : message ≠ request.message)
    (encoding : Encoding) (hvalid : Checksum.Valid encoding) :
    3 / 4 < Pr[fun result => result.1 ≠ none |
      (simulateQ randomOracle (findEncodingNeighbor keyResult.1.2.parameter request.epoch message encoding)).run signCache] := by
  let computation := (simulateQ randomOracle
    (findEncodingNeighbor keyResult.1.2.parameter request.epoch message encoding)).run signCache
  have hfailure : Pr[fun result => result.1 = none | computation] < 1 / 4 := by
    rw [findEncodingNeighbor_failure_fresh _ _ _ _ _ (fun i _ =>
      neighborSearchInput_fresh_after_signing keyResult hkey request answer signCache hsign message hne i)]
    exact neighbor_rejection_power_lt_quarter encoding hvalid
  have hsum : Pr[fun result => result.1 = none | computation] +
      Pr[fun result => result.1 ≠ none | computation] = 1 := by
    simpa only [probFailure_of_liftM_PMF, tsub_zero] using
      probEvent_compl computation (fun result => result.1 = none)
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top, ENNReal.toReal_one] at hr
  have hf := (ENNReal.toReal_lt_toReal probEvent_ne_top (by finiteness)).mpr hfailure
  apply (ENNReal.toReal_lt_toReal (by finiteness) probEvent_ne_top).mp
  norm_num [ENNReal.toReal_div] at hf ⊢
  change 3 / 4 < (Pr[fun result => result.1 ≠ none | computation]).toReal
  linarith

theorem findEncodingNeighbor_queryBound (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (encoding : Encoding) :
    (findEncodingNeighbor parameter leafIndex message encoding).IsQueryBoundP (fun _ => True) neighborSearchSteps := by
  unfold findEncodingNeighbor
  exact findHash_queryBound _ _ _ _

/-- info: 'XmssSecurity.Attack.findEncodingNeighbor_success_after_signing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms findEncodingNeighbor_success_after_signing

/-- info: 'XmssSecurity.Attack.findEncodingNeighbor_queryBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms findEncodingNeighbor_queryBound

end XmssSecurity.Attack
