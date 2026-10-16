import XmssSecurity.Proof.EncodingAcceptanceBudget

/-! Sample the final hash output conditioned on an accepted encoding. Any event
that rejects invalid encodings factors by the exact ordinary acceptance probability. -/

open OracleComp OracleSpec ENNReal
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum

abbrev AcceptedHashOutput := {output : HashOutput // ValidDigest (truncateHash output)}

noncomputable instance acceptedHashOutputFintype : Fintype AcceptedHashOutput := by
  infer_instance

instance acceptedHashOutputNonempty : Nonempty AcceptedHashOutput := by
  have hpositive : 0 < Pr[fun output : HashOutput => ValidDigest (truncateHash output) | $ᵗ HashOutput] := by
    rw [probEvent_validDigest_uniformHashOutput]
    exact acceptanceProbability_pos
  obtain ⟨output, _hsupport, hvalid⟩ := probEvent_pos_iff.mp hpositive
  exact ⟨⟨output, hvalid⟩⟩

noncomputable instance acceptedHashOutputSampleable : SampleableType AcceptedHashOutput :=
  SampleableType.ofFintype AcceptedHashOutput

noncomputable def acceptedHashEncoding (output : AcceptedHashOutput) : Encoding :=
  Classical.choose output.2

theorem acceptedHashEncoding_decode (output : AcceptedHashOutput) :
    decodeDigest (truncateHash output.1) = some (acceptedHashEncoding output) :=
  Classical.choose_spec output.2

theorem acceptedHashEncoding_valid (output : AcceptedHashOutput) :
    Valid (acceptedHashEncoding output) :=
  (decodeDigest_eq_some_iff.mp (acceptedHashEncoding_decode output)).2

theorem acceptanceProbability_eq_card_ratio :
    acceptanceProbability = (Fintype.card AcceptedHashOutput : ℝ≥0∞) / Fintype.card HashOutput := by
  have hcard : Fintype.card AcceptedHashOutput =
      (Finset.univ.filter (fun output : HashOutput => ValidDigest (truncateHash output))).card :=
    Fintype.card_subtype (fun output : HashOutput => ValidDigest (truncateHash output))
  rw [hcard, ← probEvent_validDigest_uniformHashOutput, probEvent_uniformSample]

theorem acceptanceProbability_mul_acceptedHashOutput_weight :
    acceptanceProbability * (Fintype.card AcceptedHashOutput : ℝ≥0∞)⁻¹ =
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  rw [acceptanceProbability_eq_card_ratio, div_eq_mul_inv]
  calc
    _ = ((Fintype.card AcceptedHashOutput : ℝ≥0∞) *
          (Fintype.card AcceptedHashOutput : ℝ≥0∞)⁻¹) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ :=
      mul_right_comm _ _ _
    _ = _ := by rw [ENNReal.mul_inv_cancel
      (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card AcceptedHashOutput ≠ 0))
      (ENNReal.natCast_ne_top _), one_mul]

theorem uniformHashOutput_bind_probability_eq_acceptance_mul {α : Type}
    (continuation : HashOutput → ProbComp α) (event : α → Prop)
    (hinvalid : ∀ output, ¬ValidDigest (truncateHash output) → Pr[event | continuation output] = 0) :
    Pr[event | ($ᵗ HashOutput) >>= continuation] =
      acceptanceProbability * Pr[event | ($ᵗ AcceptedHashOutput) >>= fun output => continuation output.1] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_left]
  simp_rw [probOutput_uniformSample, ← mul_assoc, acceptanceProbability_mul_acceptedHashOutput_weight]
  let weight : HashOutput → ℝ≥0∞ := fun output =>
    (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * Pr[event | continuation output]
  change (∑' output : HashOutput, weight output) = ∑' output : AcceptedHashOutput, weight output.1
  exact (tsum_subtype_eq_of_support_subset (s := {output : HashOutput | ValidDigest (truncateHash output)})
    (f := weight) (by
      intro output houtput
      by_contra hinvalidOutput
      apply houtput
      dsimp only [weight]
      rw [hinvalid output hinvalidOutput, mul_zero])).symm

/-- info: 'XmssSecurity.Checksum.uniformHashOutput_bind_probability_eq_acceptance_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformHashOutput_bind_probability_eq_acceptance_mul

end XmssSecurity.Checksum
