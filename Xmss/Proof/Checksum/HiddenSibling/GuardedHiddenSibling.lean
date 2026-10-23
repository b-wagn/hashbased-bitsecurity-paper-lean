import Xmss.Proof.Checksum.HiddenSibling.Signed

/-! Keep the probability of continuing without a signature in the hidden-sibling bound. -/

open OracleComp OracleSpec ENNReal
open Xmss.Generic

set_option backward.isDefEq.respectTransparency false

namespace Xmss.Checksum.HiddenSibling

noncomputable def idealProgram (body : PublicKey → OracleComp OracleWorld α)
    (publicKey : PublicKey) : ProbComp (α × QueryCache HashSpec) :=
  (simulateQ romImpl (body publicKey)).run ∅

noncomputable def idealProgramSize (body : PublicKey → OracleComp OracleWorld α)
    (publicKey : PublicKey) : ℝ≥0∞ :=
  ∑' result, Pr[= result | idealProgram body publicKey] * cacheSize result.2

open Classical in
theorem probEvent_subtrees_guarded_le_size (parameter : PublicParameter) (output : Digest)
    (forgery : Generic.Forgery) (finalCache : QueryCache HashSpec) (guard : Prop) :
    Pr[fun sample =>
        (HiddenSiblingGuessed (splitCache parameter sample output)
          (Generic.SecretKey.withoutPrecomputation parameter sample.1) forgery ∧ guard) ∨
        HitsCache (splitCache parameter sample output) finalCache | subtrees parameter] ≤
      digestInverse * ((if guard then 1 else 0) + cacheSize finalCache) := by
  by_cases hguard : guard
  · simpa only [hguard, and_true, if_true] using
      probEvent_subtrees_ideal_le_size parameter output forgery finalCache
  · simp only [hguard, and_false, false_or, if_false, zero_add]
    calc
      _ ≤ ∑' input, if finalCache input ≠ none then digestInverse else 0 := by
        refine (probEvent_exists_le_tsum _ _).trans (ENNReal.tsum_le_tsum fun input => ?_)
        split_ifs with hfinal
        · exact (probEvent_mono fun _ _ h => h.2).trans
            (probEvent_subtrees_cached_le parameter output input)
        · exact le_of_eq (probEvent_eq_zero fun _ _ h => hfinal h.1)
      _ = _ := by
        rw [cacheSize, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun input => by split_ifs <;> simp

open Classical in
theorem hiddenSibling_program_guard_le {α : Type}
    (body : PublicKey → OracleComp OracleWorld α) (extract : α → Generic.Forgery) (guard : α → Prop) :
    ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Keygen.keygen).run ∅] *
      Pr[fun result : α × QueryCache HashSpec =>
          (HiddenSiblingGuessed keyResult.2 keyResult.1.2 (extract result.1) ∧ guard result.1) |
        (simulateQ romImpl (body keyResult.1.1)).run keyResult.2] ≤
      digestInverse * publicKeyAverage fun publicKey => Pr[fun result => guard result.1 | idealProgram body publicKey] + idealProgramSize body publicKey := by
  let event : (PublicKey × Generic.SecretKey) × QueryCache HashSpec →
      α × QueryCache HashSpec → Prop := fun keyResult result =>
    (HiddenSiblingGuessed keyResult.2 keyResult.1.2 (extract result.1) ∧ guard result.1) ∨ HitsCache keyResult.2 result.2
  calc
    _ ≤ ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Keygen.keygen).run ∅] *
          Pr[event keyResult | idealProgram body keyResult.1.1] :=
      ENNReal.tsum_le_tsum fun keyResult => mul_le_mul' le_rfl
        (probEvent_run_le_empty (body keyResult.1.1) keyResult.2
          (fun result => HiddenSiblingGuessed keyResult.2 keyResult.1.2 (extract result) ∧ guard result))
    _ = Pr[fun joint => event joint.1 joint.2 |
          (simulateQ romImpl Keygen.keygen).run ∅ >>= fun keyResult =>
            (fun result => (keyResult, result)) <$> idealProgram body keyResult.1.1] := by
      rw [probEvent_bind_eq_tsum]
      refine tsum_congr fun keyResult => ?_
      rw [probEvent_map]
      rfl
    _ ≤ _ := by
      rw [keygen_run_eq]
      simp only [bind_assoc, pure_bind]
      rw [probEvent_bind_eq_tsum]
      unfold publicKeyAverage
      rw [← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun parameter => ?_
      rw [mul_left_comm]
      refine mul_le_mul' le_rfl ?_
      let keyOf : (LeafIndex → ChainIndex → Digest) → Digest × QueryCache HashSpec →
          (PublicKey × Generic.SecretKey) × QueryCache HashSpec := fun secret tree =>
        ((⟨tree.1, parameter⟩, Generic.SecretKey.withoutPrecomputation parameter secret), tree.2)
      let observed : ProbComp (Digest × (α × QueryCache HashSpec)) := do
        let output ← $ᵗ Digest
        let result ← idealProgram body ⟨output, parameter⟩
        pure (output, result)
      let finish : ((LeafIndex → ChainIndex → Digest) ×
          (Digest × QueryCache HashSpec) × (Digest × QueryCache HashSpec)) →
          Digest × (α × QueryCache HashSpec) →
          ((PublicKey × Generic.SecretKey) × QueryCache HashSpec) × (α × QueryCache HashSpec) :=
        fun sample seen =>
          (keyOf sample.1 (seen.1, splitCache parameter sample seen.1), seen.2)
      have hsplit :
          𝒟[Keygen.sampleSecret >>= fun secret =>
            (simulateQ randomOracle
              (Generic.Merkle.treeNode parameter secret treeHeight Generic.Merkle.rootNode :
                OracleComp HashSpec Digest)).run ∅ >>= fun tree =>
              (fun result => (keyOf secret tree, result)) <$>
                idealProgram body (keyOf secret tree).1.1] =
          𝒟[subtrees parameter >>= fun sample => observed >>= fun seen =>
            pure (finish sample seen)] := by
        have hkeygen : (Keygen.sampleSecret >>= fun secret =>
            (simulateQ randomOracle
              (Generic.Merkle.treeNode parameter secret treeHeight Generic.Merkle.rootNode :
                OracleComp HashSpec Digest)).run ∅ >>= fun tree =>
              (fun result => (keyOf secret tree, result)) <$>
                idealProgram body (keyOf secret tree).1.1) =
            keygenTree parameter >>= fun sampled =>
              (fun result => (keyOf sampled.1 sampled.2, result)) <$>
                idealProgram body ⟨sampled.2.1, parameter⟩ := by
          simp only [keygenTree, bind_assoc, pure_bind]
          rfl
        rw [hkeygen, evalDist_bind, evalDist_keygenTree_split, ← evalDist_bind]
        simp only [observed, finish, keyOf, bind_assoc, map_eq_bind_pure_comp, pure_bind,
          Function.comp_apply]
        rfl
      rw [probEvent_congr' (fun _ _ => Iff.rfl) hsplit, probEvent_bind_bind_swap,
        probEvent_bind_eq_tsum]
      calc
        _ ≤ ∑' seen, Pr[= seen | observed] * (digestInverse * ((if guard seen.2.1 then 1 else 0) + cacheSize seen.2.2)) := by
          refine ENNReal.tsum_le_tsum fun seen => mul_le_mul' le_rfl ?_
          rw [bind_pure_comp, probEvent_map]
          exact probEvent_subtrees_guarded_le_size parameter seen.1 (extract seen.2.1) seen.2.2 (guard seen.2.1)
        _ = digestInverse * ∑' output, Pr[= output | ($ᵗ Digest : ProbComp Digest)] *
            ∑' result, Pr[= result | idealProgram body ⟨output, parameter⟩] *
              ((if guard result.1 then 1 else 0) + cacheSize result.2) := by
          simp only [observed]
          simp_rw [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
          simp_rw [mul_left_comm _ digestInverse, ENNReal.tsum_mul_left]
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun output => mul_left_comm _ _ _
        _ ≤ _ := by
          refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl ?_)
          simp only [mul_add, ENNReal.tsum_add, idealProgramSize]
          apply add_le_add _ le_rfl
          rw [probEvent_eq_tsum_ite]
          apply ENNReal.tsum_le_tsum
          intro result
          split_ifs <;> simp


end Xmss.Checksum.HiddenSibling
