import XmssSecurity.Proof.TargetSum.EUFCMA.FreshFirstLane
import XmssSecurity.Proof.TargetSum.EUFCMA.PhaseAcceptance
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The fresh-prefix acceptance bound retains the expected encoding-query count,
so structural queries and signing requests do not consume this allowance. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete CappedChain Deciding

theorem sourcePrefix_freshAccepted_probability_le_expected (adversary : Adversary)
    (key : CappedChain.ProgrammedGlobalChainKeygenView)
    (hkey : key ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen) :
    Pr[SourcePrefixFreshAccepted key | Deciding.sourcePrefixExecution adversary key] ≤
      TargetSum.acceptanceProbability * expectedSimulatedQueryCount
        (cappedUnloggedMappedAdversaryImpl key.publicKey (Concrete.materializePrecomputation key.cache key.secretKey))
        (Direct.IsDirectEncodingQuery key.secretKey.parameter) (adversary.main key.publicKey) key.cache := by
  have hbound := probEvent_freshAccepted_le_expected_directEncoding key.publicKey
    (Concrete.materializePrecomputation key.cache key.secretKey) (adversary.main key.publicKey) (key.cache, [])
    (by
      rw [Concrete.materializePrecomputation_parameter]
      exact no_freshAcceptedEncoding_of_no_encodingInputs _ _ _
        (Concrete.keygen_cache_none_encodingInput key.keyResult
          (CappedChain.trajectoryProgrammedGlobalChainKeygen_support_keyResult key hkey)))
  rw [expected_directEncoding_forget_trace, Concrete.materializePrecomputation_parameter] at hbound
  rw [← CappedChain.cappedBothTracedMappedAdversaryImpl_actionProjection key.publicKey
    (Concrete.materializePrecomputation key.cache key.secretKey)
    (adversary.main key.publicKey) ((key.cache, []), []) [], probEvent_map] at hbound
  apply le_trans _ hbound
  apply probEvent_mono''
  rintro result ⟨hfresh, encoding, hdecode⟩
  exact hasFreshAcceptedEncoding_of_decode key.secretKey.parameter
    (result.2.1.1.1, result.2.2) result.1 encoding hfresh hdecode

theorem sourcePrefixProgram_freshAccepted_probability_le_expected (adversary : Adversary) :
    Pr[fun result => SourcePrefixFreshAccepted result.1 result.2 | Deciding.sourcePrefixProgram adversary] ≤
      TargetSum.acceptanceProbability * Direct.expectedDirectEncodingQueries adversary := by
  let credit := fun keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec =>
    expectedSimulatedQueryCount (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      (Direct.IsDirectEncodingQuery keyResult.1.2.parameter) (adversary.main keyResult.1.1) keyResult.2
  have hmean : (∑' key, Pr[= key | CappedChain.trajectoryProgrammedGlobalChainKeygen] *
      credit (Concrete.materializeCachedKeyResult key.keyResult)) = Direct.expectedDirectEncodingQueries adversary := by
    calc
      _ = ∑' keyResult, Pr[= keyResult | (fun key : CappedChain.ProgrammedGlobalChainKeygenView =>
          Concrete.materializeCachedKeyResult key.keyResult) <$> CappedChain.trajectoryProgrammedGlobalChainKeygen] * credit keyResult := by
        rw [tsum_probOutput_map_mul]
      _ = _ := by
        unfold Direct.expectedDirectEncodingQueries
        apply tsum_congr
        intro keyResult
        rw [probOutput_congr rfl CappedChain.evalDist_materializedTrajectoryGlobalChainKeygen_eq_cappedKeygen]
  unfold Deciding.sourcePrefixProgram
  rw [probEvent_bind_eq_tsum, ← hmean, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro key
  by_cases hkey : key ∈ support CappedChain.trajectoryProgrammedGlobalChainKeygen
  · simp only [bind_pure_comp, probEvent_map, Function.comp_def]
    simpa only [credit, Concrete.materializeCachedKeyResult_publicKey,
      Concrete.materializeCachedKeyResult_secretKey, Concrete.materializeCachedKeyResult_cache,
      CappedChain.ProgrammedGlobalChainKeygenView.keyResult, Concrete.materializePrecomputation_parameter,
      mul_comm, mul_left_comm, mul_assoc] using mul_le_mul'
      (le_refl (Pr[= key | CappedChain.trajectoryProgrammedGlobalChainKeygen]))
      (sourcePrefix_freshAccepted_probability_le_expected adversary key hkey)
  · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul, mul_zero]

theorem freshPrefixFirstLane_probability_le_expected (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) :
    Pr[fun result => FreshPrefixFirstLaneEvent result.1 result.2 | Deciding.sourcePrefixProgram adversary] ≤
      (D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (TargetSum.acceptanceProbability * Direct.expectedDirectEncodingQueries adversary) /
          ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  apply (accepted_event_probability_le_of_relTriple
    (source := Deciding.sourcePrefixProgram adversary)
    (target := Deciding.coupledFirstLaneProgram (Deciding.publicPrefixExecution adversary))
    (fun result => FreshPrefixFirstLaneEvent result.1 result.2)
    (fun result => SourcePrefixFreshAccepted result.1 result.2)
    CoupledPrefixFreshAccepted (CoupledFreshProbedHit D)
    (((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹) ((D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))
    (by norm_num [digestBits])
    (freshPrefix_acceptance_coupling adversary D hD) (coupledFreshProbedHit_probability_le adversary D)).trans
  apply add_le_add le_rfl
  simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul'
    (le_refl (((2 ^ digestBits : ℕ) : ℝ≥0∞)⁻¹))
    (sourcePrefixProgram_freshAccepted_probability_le_expected adversary)

/-- info: 'XmssSecurity.TargetSum.EUFCMA.freshPrefixFirstLane_probability_le_expected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms freshPrefixFirstLane_probability_le_expected

end XmssSecurity.TargetSum.EUFCMA
