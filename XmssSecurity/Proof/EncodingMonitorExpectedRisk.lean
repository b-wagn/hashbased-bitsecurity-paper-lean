import XmssSecurity.Proof.CappedEncodingMonitor
import XmssSecurity.Proof.ExpectedStateEvent

/-! Expected one-step risk in the encoding monitor, before charging a fixed future budget. -/

open OracleComp ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity

theorem Rom.expected_truncate_uniformHashOutput (weight : Digest → ℝ≥0∞) :
    (∑' output, Pr[= output | $ᵗ HashOutput] * weight (truncateHash output)) =
      ∑' digest, Pr[= digest | $ᵗ Digest] * weight digest := by
  rw [← tsum_probOutput_map_mul]
  apply tsum_congr
  intro digest
  congr 1
  exact congrArg (fun distribution => distribution digest) evalDist_truncate_uniformHashOutput

namespace CappedEncodingMonitor

noncomputable def observedRisk : Option (EncodingMonitor.State × Bool) → ℝ≥0∞
  | none => 0
  | some (state, hit) => if hit then 1 else State.pendingRisk state

noncomputable def queryDigestRisk (state : EncodingMonitor.State) (leafIndex : LeafIndex)
    (digest : Digest) : ℝ≥0∞ :=
  match state.signed leafIndex with
  | some target => if digest = target then 1 else State.pendingRisk state
  | none => if Checksum.ValidDigest digest then State.pendingRisk (state.addPending leafIndex digest)
      else State.pendingRisk state

noncomputable def signDigestRisk (state : EncodingMonitor.State) (leafIndex : LeafIndex)
    (digest : Digest) : ℝ≥0∞ :=
  if Checksum.ValidDigest digest then
    match state.signed leafIndex with
    | some _ => 0
    | none => if digest ∈ state.pending leafIndex then 1
        else State.pendingRisk (state.install leafIndex digest)
  else State.pendingRisk state

theorem observedRisk_query (state : EncodingMonitor.State) (leafIndex : LeafIndex)
    (output : HashOutput) : observedRisk (State.applyObserved state (.query leafIndex output)) =
      queryDigestRisk state leafIndex (truncateHash output) := by
  cases hsigned : state.signed leafIndex with
  | some target => simp [State.applyObserved, queryDigestRisk, observedRisk, hsigned]
  | none =>
      by_cases hvalid : Checksum.ValidDigest (truncateHash output) <;>
        simp [State.applyObserved, queryDigestRisk, observedRisk, hsigned, hvalid]

theorem observedRisk_sign (state : EncodingMonitor.State) (leafIndex : LeafIndex)
    (output : HashOutput) : observedRisk (State.applyObserved state (.sign leafIndex output)) =
      signDigestRisk state leafIndex (truncateHash output) := by
  by_cases hvalid : Checksum.ValidDigest (truncateHash output)
  · cases hsigned : state.signed leafIndex <;>
      simp [State.applyObserved, signDigestRisk, observedRisk, hsigned, hvalid]
  · simp [State.applyObserved, signDigestRisk, observedRisk, hvalid]

theorem expected_queryDigestRisk_le (state : EncodingMonitor.State) (leafIndex : LeafIndex) :
    (∑' digest, Pr[= digest | $ᵗ Digest] * queryDigestRisk state leafIndex digest) ≤
      State.pendingRisk state + (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  classical
  cases hsigned : state.signed leafIndex with
  | some target =>
      calc
        _ ≤ ∑' digest, Pr[= digest | $ᵗ Digest] *
            (State.pendingRisk state + if digest = target then 1 else 0) := by
          apply ENNReal.tsum_le_tsum
          intro digest
          apply mul_le_mul' le_rfl
          by_cases heq : digest = target <;> simp [queryDigestRisk, hsigned, heq]
        _ = _ := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
            tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]
          congr 1
          simp only [mul_ite, mul_one, mul_zero, tsum_ite_eq, probOutput_uniformSample]
  | none =>
      calc
        _ ≤ ∑' digest, Pr[= digest | $ᵗ Digest] *
            (State.pendingRisk state + if Checksum.ValidDigest digest then
              (Checksum.validDigests.card : ℝ≥0∞)⁻¹ else 0) := by
          apply ENNReal.tsum_le_tsum
          intro digest
          apply mul_le_mul' le_rfl
          by_cases hvalid : Checksum.ValidDigest digest
          · simpa only [queryDigestRisk, hsigned, if_pos hvalid] using
              State.pendingRisk_addPending_le state leafIndex digest
          · simp [queryDigestRisk, hsigned, hvalid]
        _ = _ := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
            tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul, tsum_fintype,
            uniformDigest_valid_bonus_sum_eq]

theorem expected_signDigestRisk_le (state : EncodingMonitor.State) (leafIndex : LeafIndex) :
    (∑' digest, Pr[= digest | $ᵗ Digest] * signDigestRisk state leafIndex digest) ≤
      State.pendingRisk state := by
  classical
  cases hsigned : state.signed leafIndex with
  | some target =>
      calc
        _ ≤ ∑' digest, Pr[= digest | $ᵗ Digest] * State.pendingRisk state := by
          apply ENNReal.tsum_le_tsum
          intro digest
          apply mul_le_mul' le_rfl
          by_cases hvalid : Checksum.ValidDigest digest <;>
            simp [signDigestRisk, hsigned, hvalid]
        _ = _ := by
          rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]
  | none =>
      let remaining := State.pendingRisk (state.install leafIndex 0)
      let removed := ((state.pending leafIndex).card : ℝ≥0∞) *
        (Checksum.validDigests.card : ℝ≥0∞)⁻¹
      have hrisk : remaining + removed = State.pendingRisk state := State.pendingRisk_install_add _ _ _
      have hremaining : ∀ digest, State.pendingRisk (state.install leafIndex digest) = remaining := by
        intro digest
        unfold remaining State.pendingRisk
        rw [EncodingMonitor.State.pendingCount_install_eq state leafIndex digest 0]
      calc
        _ ≤ ∑' digest, Pr[= digest | $ᵗ Digest] *
            (remaining + if Checksum.ValidDigest digest then
              if digest ∈ state.pending leafIndex then 1 else 0 else removed) := by
          apply ENNReal.tsum_le_tsum
          intro digest
          apply mul_le_mul' le_rfl
          by_cases hvalid : Checksum.ValidDigest digest
          · by_cases hmem : digest ∈ state.pending leafIndex <;>
              simp [signDigestRisk, hsigned, hvalid, hmem, hremaining]
          · simp only [signDigestRisk, if_neg hvalid]
            exact hrisk.ge
        _ = remaining + ∑' digest, Pr[= digest | $ᵗ Digest] *
            (if Checksum.ValidDigest digest then
              if digest ∈ state.pending leafIndex then 1 else 0 else removed) := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right,
            tsum_probOutput_eq_one' (probFailure_of_liftM_PMF _), one_mul]
        _ ≤ remaining + removed := by
          apply add_le_add le_rfl
          rw [tsum_fintype]
          exact uniformDigest_sign_bonus_sum_le (state.pending leafIndex)
        _ = _ := hrisk

theorem expected_observedRisk_query_le (state : EncodingMonitor.State) (leafIndex : LeafIndex) :
    (∑' output, Pr[= output | $ᵗ HashOutput] *
      observedRisk (State.applyObserved state (.query leafIndex output))) ≤
      State.pendingRisk state + ((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹ := by
  simp_rw [observedRisk_query]
  rw [Rom.expected_truncate_uniformHashOutput]
  have hcard : Fintype.card Digest = 2 ^ digestBits := by simp
  simpa only [hcard] using expected_queryDigestRisk_le state leafIndex

theorem expected_observedRisk_sign_le (state : EncodingMonitor.State) (leafIndex : LeafIndex) :
    (∑' output, Pr[= output | $ᵗ HashOutput] *
      observedRisk (State.applyObserved state (.sign leafIndex output))) ≤ State.pendingRisk state := by
  simp_rw [observedRisk_sign]
  rw [Rom.expected_truncate_uniformHashOutput]
  exact expected_signDigestRisk_le state leafIndex

end CappedEncodingMonitor
end XmssSecurity
