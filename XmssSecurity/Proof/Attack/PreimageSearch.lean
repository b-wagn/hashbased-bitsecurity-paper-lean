import XmssSecurity.Proof.Attack.HashSearch
import XmssSecurity.Proof.EncodingRejectionProbability

/-! A bounded predecessor search that includes the genuine cached predecessor with
probability `1/16`, and otherwise searches distinct fresh inputs. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Attack

abbrev PreimagePrefix := BitVec 4

def preimageSearchSteps : ℕ := 2 ^ 124

def preimageCandidate (block : PreimagePrefix) (position : ℕ) : Digest :=
  block ++ BitVec.ofNat 124 position

def preimagePrefix (value : Digest) : PreimagePrefix := value.extractLsb' 124 4

def preimagePosition (value : Digest) : ℕ := (value.extractLsb' 0 124).toNat

@[simp] theorem preimageCandidate_prefix (block : PreimagePrefix) (position : ℕ) :
    preimagePrefix (preimageCandidate block position) = block :=
  BitVec.extractLsb'_append_eq_left

theorem preimagePosition_lt (value : Digest) : preimagePosition value < preimageSearchSteps :=
  (value.extractLsb' 0 124).isLt

@[simp] theorem preimageCandidate_reconstruct (value : Digest) :
    preimageCandidate (preimagePrefix value) (preimagePosition value) = value := by
  simp only [preimageCandidate, preimagePrefix, preimagePosition, BitVec.ofNat_toNat]
  exact BitVec.extractLsb'_append_extractLsb'

theorem preimageCandidate_separate (block : PreimagePrefix) (i j : ℕ)
    (hi : i < preimageSearchSteps) (hj : j < preimageSearchSteps) (hne : i ≠ j) :
    preimageCandidate block i ≠ preimageCandidate block j := by
  intro heq
  have hlow := congrArg (fun value : Digest => value.extractLsb' 0 124) heq
  simp only [preimageCandidate, BitVec.extractLsb'_append_eq_right] at hlow
  have hnat := congrArg BitVec.toNat hlow
  change i < 2 ^ 124 at hi
  change j < 2 ^ 124 at hj
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hnat
  exact hne hnat

theorem preimageCandidate_ne_of_prefix_ne (block : PreimagePrefix) (value : Digest)
    (hne : block ≠ preimagePrefix value) (position : ℕ) :
    preimageCandidate block position ≠ value := by
  intro heq
  exact hne (by simpa only [preimageCandidate_prefix] using congrArg preimagePrefix heq)

noncomputable def findDigestPreimage (input : Digest → HashInput) (target : Digest)
    (block : PreimagePrefix) : OracleComp HashSpec (Option (ℕ × HashOutput)) := by
  classical
  exact findHash (fun position => input (preimageCandidate block position))
    (fun output => truncateHash output = target) 0 preimageSearchSteps

theorem findDigestPreimage_queryBound (input : Digest → HashInput) (target : Digest)
    (block : PreimagePrefix) :
    (findDigestPreimage input target block).IsQueryBoundP (fun _ => True) preimageSearchSteps := by
  unfold findDigestPreimage
  exact findHash_queryBound _ _ _ _

theorem findDigestPreimage_success_cached (input : Digest → HashInput) (target : Digest)
    (block : PreimagePrefix) (initialCache finalCache : QueryCache HashSpec)
    (position : ℕ) (output : HashOutput)
    (hmem : (some (position, output), finalCache) ∈ support
      ((simulateQ randomOracle (findDigestPreimage input target block)).run initialCache)) :
    position < preimageSearchSteps ∧ truncateHash output = target ∧
      finalCache (input (preimageCandidate block position)) = some output := by
  obtain ⟨_, hposition, htarget, hcached⟩ := findHash_success_cached _ _ _ _ _ _ _ _ hmem
  exact ⟨hposition, htarget, hcached⟩

theorem findDigestPreimage_failure (input : Digest → HashInput) (hinj : Function.Injective input)
    (target genuine : Digest) (cache : QueryCache HashSpec)
    (hhit : ∃ output, cache (input genuine) = some output ∧ truncateHash output = target)
    (hfresh : ∀ value, value ≠ genuine → cache (input value) = none)
    (block : PreimagePrefix) :
    Pr[fun result => result.1 = none |
      (simulateQ randomOracle (findDigestPreimage input target block)).run cache] =
      if block = preimagePrefix genuine then 0
      else (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ preimageSearchSteps := by
  classical
  unfold findDigestPreimage
  by_cases hprefix : block = preimagePrefix genuine
  · rw [if_pos hprefix]
    obtain ⟨output, hcached, htarget⟩ := hhit
    apply findHash_failure_zero_of_cached_hit _ _ _ _ _ (preimagePosition genuine)
      (Nat.zero_le _) (preimagePosition_lt genuine) output _ htarget
    rw [hprefix, preimageCandidate_reconstruct]
    exact hcached
  · rw [if_neg hprefix, findHash_failure_fresh]
    · rw [Rom.uniform_truncate_miss_probability]
    · intro i _ hi j _ hj hne heq
      exact preimageCandidate_separate block i j (by omega) (by omega) hne (hinj heq)
    · intro i _ _
      exact hfresh _ (preimageCandidate_ne_of_prefix_ne block genuine hprefix i)

/-- Pick one of sixteen disjoint blocks and search its `2^124` candidate predecessors. -/
noncomputable def randomDigestPreimage (input : Digest → HashInput) (target : Digest)
    (cache : QueryCache HashSpec) :
    ProbComp (PreimagePrefix × (Option (ℕ × HashOutput) × QueryCache HashSpec)) := do
  let block ← $ᵗ PreimagePrefix
  let result ← (simulateQ randomOracle (findDigestPreimage input target block)).run cache
  return (block, result)

theorem uniform_preimagePrefix_ne_probability (block : PreimagePrefix) :
    Pr[fun other => other ≠ block | $ᵗ PreimagePrefix] = 15 / 16 := by
  classical
  rw [probEvent_uniformSample]
  simp only [ne_eq, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ block),
    Finset.card_univ]
  norm_num [PreimagePrefix]

theorem randomDigestPreimage_failure (input : Digest → HashInput) (hinj : Function.Injective input)
    (target genuine : Digest) (cache : QueryCache HashSpec)
    (hhit : ∃ output, cache (input genuine) = some output ∧ truncateHash output = target)
    (hfresh : ∀ value, value ≠ genuine → cache (input value) = none) :
    Pr[fun result => result.2.1 = none | randomDigestPreimage input target cache] =
      (15 / 16) * (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ preimageSearchSteps := by
  classical
  unfold randomDigestPreimage
  rw [probEvent_bind_eq_tsum]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def,
    findDigestPreimage_failure input hinj target genuine cache hhit hfresh]
  calc
    _ = Pr[fun block => block ≠ preimagePrefix genuine | $ᵗ PreimagePrefix] *
        (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ preimageSearchSteps := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro block
      by_cases hprefix : block = preimagePrefix genuine <;> simp [hprefix]
    _ = _ := by rw [uniform_preimagePrefix_ne_probability]

theorem preimage_rejection_power_le :
    (1 - ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ^ preimageSearchSteps ≤ 16 / 17 := by
  calc
    _ ≤ 1 / (1 + preimageSearchSteps * ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) :=
      TargetSum.rejection_power_le _ (by norm_num [digestBits]) _
    _ = 16 / 17 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_div, ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num [preimageSearchSteps, digestBits, ENNReal.toReal_mul, ENNReal.toReal_inv]

theorem randomDigestPreimage_success (input : Digest → HashInput) (hinj : Function.Injective input)
    (target genuine : Digest) (cache : QueryCache HashSpec)
    (hhit : ∃ output, cache (input genuine) = some output ∧ truncateHash output = target)
    (hfresh : ∀ value, value ≠ genuine → cache (input value) = none) :
    2 / 17 ≤ Pr[fun result => result.2.1 ≠ none | randomDigestPreimage input target cache] := by
  have hfailure : Pr[fun result => result.2.1 = none | randomDigestPreimage input target cache] ≤ 15 / 17 := by
    rw [randomDigestPreimage_failure input hinj target genuine cache hhit hfresh]
    calc
      _ ≤ (15 / 16) * (16 / 17) := mul_le_mul_right preimage_rejection_power_le _
      _ = 15 / 17 := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  have hsum := probEvent_compl (randomDigestPreimage input target cache) (fun result => result.2.1 = none)
  rw [probFailure_of_liftM_PMF, tsub_zero] at hsum
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top, ENNReal.toReal_one] at hr
  have hf := (ENNReal.toReal_le_toReal probEvent_ne_top (by finiteness)).mpr hfailure
  apply (ENNReal.toReal_le_toReal (by finiteness) probEvent_ne_top).mp
  norm_num [ENNReal.toReal_div] at hf ⊢
  linarith

/-- info: 'XmssSecurity.Attack.randomDigestPreimage_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms randomDigestPreimage_failure

/-- info: 'XmssSecurity.Attack.randomDigestPreimage_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms randomDigestPreimage_success

end XmssSecurity.Attack
