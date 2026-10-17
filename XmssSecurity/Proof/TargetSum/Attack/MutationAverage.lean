import XmssSecurity.Proof.TargetSum.Attack.MutationVerification
import XmssSecurity.Proof.TargetSum.Attack.ChainMutation

/-! Averaging over chains and signing outcomes in the reference mutation experiment. -/

open OracleComp OracleSpec ENNReal
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum.Attack

open Concrete

local instance : Nonempty ChainIndex := ⟨⟨0, by decide⟩⟩
noncomputable local instance : SampleableType ChainIndex := SampleableType.ofFintype ChainIndex

noncomputable def uniformChainVerification (publicKey : PublicKey) (request : SignRequest)
    (signature : Signature) (cache : QueryCache HashSpec) : ProbComp Bool := do
  let chain ← $ᵗ ChainIndex
  let result ← randomMutationVerification publicKey request.epoch request.message signature chain cache
  return decide (result.1 ≠ signature.chainValue chain ∧ result.2.1 = true)

theorem uniformChainVerification_probability
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) (signature : Signature) (finalCache : QueryCache HashSpec)
    (hsign : (some signature, finalCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2)) :
    ∃ encoding, TargetSum.Valid encoding ∧
      Pr[= true | uniformChainVerification keyResult.1.1 request signature finalCache] =
        (∑ chain, pathMutationProbability (40 - (encoding chain).val)) / numChains := by
  obtain ⟨encoding, hdecode, hprob⟩ := mutationVerification_probability_after_successful_signing
    keyResult hkey request signature finalCache hsign
  refine ⟨encoding, (TargetSum.decodeDigest_eq_some_iff.mp hdecode).2, ?_⟩
  unfold uniformChainVerification
  rw [← probEvent_eq_eq_probOutput, probEvent_bind_eq_tsum]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, decide_eq_true_eq,
    hprob, probOutput_uniformSample, Fintype.card_fin]
  rw [tsum_fintype, ← Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_comm]

theorem uniformChainVerification_lower
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) (signature : Signature) (finalCache : QueryCache HashSpec)
    (hsign : (some signature, finalCache) ∈ support ((simulateQ romImpl
      (precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2)) :
    (1443 / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) / numChains ≤
      Pr[= true | uniformChainVerification keyResult.1.1 request signature finalCache] := by
  obtain ⟨encoding, hvalid, heq⟩ := uniformChainVerification_probability keyResult hkey
    request signature finalCache hsign
  rw [heq]
  exact ENNReal.div_le_div_right (sum_pathMutationProbability_lower encoding hvalid) _

/-- Reject a failed signing attempt; on success choose and replace a chain uniformly. -/
noncomputable def signedMutationExperiment
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) (request : SignRequest) : ProbComp Bool := do
  let result ← (simulateQ romImpl
    (precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2
  match result.1 with
  | none => pure false
  | some signature => uniformChainVerification keyResult.1.1 request signature result.2

theorem signedMutationExperiment_probability_lower
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) :
    (31 / 32 : ℝ≥0∞) * ((1443 / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) / numChains) ≤
      Pr[= true | signedMutationExperiment keyResult request] := by
  classical
  let lower : ℝ≥0∞ := (1443 / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) / numChains
  let signing := (simulateQ romImpl
    (precomputedCappedSign keyResult.1.2 request.epoch request.message)).run keyResult.2
  calc
    _ ≤ Pr[fun result => result.1 ≠ none | signing] * lower := by
      exact mul_le_mul_left (le_of_lt (precomputedCappedSign_success_after_keygen keyResult hkey
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

theorem signedMutationExperiment_exceeds_123
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (request : SignRequest) :
    (1 : ℝ≥0∞) / ((2 ^ 123 : ℕ) : ℝ≥0∞) <
      Pr[= true | signedMutationExperiment keyResult request] := by
  apply lt_of_lt_of_le _ (signedMutationExperiment_probability_lower keyResult hkey request)
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by
    apply ENNReal.mul_ne_top
    · finiteness
    · exact ENNReal.div_ne_top (by finiteness) (by norm_num [numChains]))).mp
  norm_num [digestBits, numChains, ENNReal.toReal_mul, ENNReal.toReal_div]

/-- info: 'XmssSecurity.TargetSum.Attack.signedMutationExperiment_exceeds_123' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signedMutationExperiment_exceeds_123

end XmssSecurity.TargetSum.Attack
