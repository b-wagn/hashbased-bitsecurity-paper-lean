import XmssSecurity.Proof.Generic.Attack.MutationVerification
import XmssSecurity.Proof.Generic.Attack.ChainMutation
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability
import XmssSecurity.Proof.Checksum.SigningSuccess
/-! Averaging over chains and signing outcomes in the reference mutation experiment. -/

open OracleComp OracleSpec ENNReal
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open XmssSecurity.Generic

namespace XmssSecurity.Checksum.Attack


theorem sum_mutatedChainWork_sub_one (encoding : Encoding) (hvalid : Code.Valid encoding) :
    1493 ≤ (∑ chain, (40 - (encoding chain).val - 1)) := by
  have heq : ∀ chain, 40 - (encoding chain).val - 1 = 39 - (encoding chain).val := by
    intro chain
    omega
  simp_rw [heq]
  rw [Finset.sum_tsub_distrib Finset.univ]
  · have hsum := Checksum.sum_digits_le encoding hvalid
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    norm_num [numChains, messageDigits, chainLength, winternitzBits] at hsum ⊢
    omega
  · intro chain _
    have hbound := (encoding chain).isLt
    norm_num [chainLength, winternitzBits] at hbound
    omega

/-- The chain is chosen uniformly, without a hash query to learn the encoding. -/
theorem sum_pathMutationProbability_lower (encoding : Encoding) (hvalid : Code.Valid encoding) :
    1493 / ((2 ^ digestBits : ℕ) : ℝ≥0∞) ≤
      ∑ chain, Attack.pathMutationProbability (40 - (encoding chain).val) := by
  calc
    _ ≤ (∑ chain, ((40 - (encoding chain).val - 1 : ℕ) : ℝ≥0∞)) /
        ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
      rw [← Nat.cast_sum]
      gcongr
      exact_mod_cast sum_mutatedChainWork_sub_one encoding hvalid
    _ = ∑ chain, ((40 - (encoding chain).val - 1 : ℕ) : ℝ≥0∞) /
        ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum fun chain _ => Attack.pathMutationProbability_lower _ (Nat.sub_le _ _)

open Concrete

local instance : Nonempty Generic.ChainIndex := ⟨⟨0, Code.numChains_pos⟩⟩
noncomputable local instance : SampleableType Generic.ChainIndex :=
  SampleableType.ofFintype Generic.ChainIndex

noncomputable def uniformChainVerification (publicKey : PublicKey) (request : SignRequest)
    (signature : Generic.Signature) (cache : QueryCache HashSpec) : ProbComp Bool := do
  let chain ← $ᵗ Generic.ChainIndex
  let result ← Attack.randomMutationVerification publicKey request.epoch request.message signature chain cache
  return decide (result.1 ≠ signature.chainValue chain ∧ result.2.1 = true)

theorem uniformChainVerification_probability
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) (signature : Generic.Signature) (finalCache : QueryCache HashSpec)
    (hsign : (some signature, finalCache) ∈ support ((simulateQ romImpl
      (Concrete.precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2)) :
    ∃ encoding, Code.Valid encoding ∧
      Pr[= true | uniformChainVerification keyResult.1.1 request signature finalCache] =
        (∑ chain, Attack.pathMutationProbability (40 - (encoding chain).val)) / numChains := by
  obtain ⟨encoding, hdecode, hprob⟩ := Attack.mutationVerification_probability_after_successful_signing
    keyResult hkey request signature finalCache hsign
  refine ⟨encoding, (Concrete.CacheView.decodedEncoding_valid hdecode), ?_⟩
  unfold uniformChainVerification
  rw [← probEvent_eq_eq_probOutput, probEvent_bind_eq_tsum]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, decide_eq_true_eq,
    hprob, probOutput_uniformSample, Fintype.card_fin, code_numChains]
  rw [tsum_fintype, ← Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_comm]
  rfl

theorem uniformChainVerification_lower
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) (signature : Generic.Signature) (finalCache : QueryCache HashSpec)
    (hsign : (some signature, finalCache) ∈ support ((simulateQ romImpl
      (Concrete.precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2)) :
    (1493 / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) / numChains ≤
      Pr[= true | uniformChainVerification keyResult.1.1 request signature finalCache] := by
  obtain ⟨encoding, hvalid, heq⟩ := uniformChainVerification_probability keyResult hkey
    request signature finalCache hsign
  rw [heq]
  exact ENNReal.div_le_div_right (sum_pathMutationProbability_lower encoding hvalid) _

/-- Choose and replace a chain uniformly after a successful signing attempt (signing always
succeeds; the failed branch only makes the definition total). -/
noncomputable def signedMutationExperiment
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec) (request : SignRequest) : ProbComp Bool := do
  let result ← (simulateQ romImpl
    (Concrete.precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2
  match result.1 with
  | none => pure false
  | some signature => uniformChainVerification keyResult.1.1 request signature result.2

theorem signedMutationExperiment_probability_lower
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) :
    (127 / 128 : ℝ≥0∞) * ((1493 / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) / numChains) ≤
      Pr[= true | signedMutationExperiment keyResult request] := by
  classical
  let lower : ℝ≥0∞ := (1493 / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) / numChains
  let signing := (simulateQ romImpl
    (Concrete.precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2
  calc
    _ ≤ Pr[fun result => result.1 ≠ none | signing] * lower := by
      exact mul_le_mul_left (le_of_lt (Concrete.precomputedCappedSign_success_after_keygen keyResult hkey
        request.epoch request.message)) lower
    _ ≤ _ := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      unfold signedMutationExperiment
      rw [probOutput_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      rintro ⟨answer, finalCache⟩
      by_cases hmem : (answer, finalCache) ∈ support signing
      · cases answer with
        | none => simp
        | some signature =>
            simp only [ne_eq, Option.some_ne_none, not_false_eq_true, if_true]
            exact mul_le_mul_right (uniformChainVerification_lower keyResult hkey request signature finalCache hmem) _
      · have hzero := probOutput_eq_zero_of_not_mem_support hmem
        change _ ≤ Pr[= (answer, finalCache) | signing] * _
        rw [hzero]
        simp

end XmssSecurity.Checksum.Attack
