import XmssSecurity.Proof.Direct.DecidingSecondLaneExpected
import XmssSecurity.Proof.Direct.DecidingPrefix
import XmssSecurity.Proof.EncodingAcceptanceBudget

/-! The free deciding verification path is needed only after an encoding has been accepted. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Deciding

open Concrete

theorem winning_verification_hasAcceptedEncoding_at_prefix (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec)
    (hprefix : prefixResult ∈ support ((simulateQ romImpl
      (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (hcached : prefixResult.2 (CacheView.encodingInput keyResult.1.2.parameter
      prefixResult.1.1.epoch (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none)
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support ((simulateQ romImpl
      (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2))
    (hwin : execution.1.won = true) :
    HasAcceptedEncoding keyResult.1.2.parameter prefixResult.2 := by
  have hfull := afterKeygen_of_phases adversary keyResult.1.1 keyResult.1.2 keyResult.2
    prefixResult hprefix execution hafter
  have hgame := CappedLeaf.afterKeygen_execution_mem_detailedGame adversary keyResult hkey
    execution hfull
  obtain ⟨event, hevent⟩ := winning_outcome_has_badEvent execution.2 execution.1
    (capped_detailed_execution_consistent adversary execution hgame) hwin
  obtain ⟨encoding, hdecode⟩ := WinningOutcomeBadEventOccurs.forgery_decode ⟨hwin, hevent⟩
  have hfields := verificationPhase_support _ _ _ _ _ hafter
  rw [hfields.2.1, hfields.2.2.1] at hdecode
  rw [← encodingHash_eq_of_cached prefixResult.2 execution.2
    (xmssRom_cache_le _ prefixResult.2 execution hafter) _ _ _ hcached] at hdecode
  exact hasAcceptedEncoding_of_decode _ _ _ _ _ _ hdecode

theorem decidingSecondLane_afterKeygen_le_expected_accepted (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (hcached : ∀ prefixResult ∈ support ((simulateQ romImpl
        (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2),
      prefixResult.2 (CacheView.encodingInput keyResult.1.2.parameter prefixResult.1.1.epoch
        (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ DecidingChainValueRevealed execution.2 execution.1 |
      (simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
        verificationPhase keyResult.1.1 keyResult.1.2)).run keyResult.2] ≤
      expectedSimulatedQueryCount romImpl
        (Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input)
        (adversaryPhase adversary keyResult.1.1 keyResult.1.2) keyResult.2 /
          ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        Pr[fun result => HasAcceptedEncoding keyResult.1.2.parameter result.2 |
          (simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2] *
            ((40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) := by
  classical
  let event : GameOutcome × QueryCache HashSpec → Prop := fun execution =>
    execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
      ¬ DecidingChainValueRevealed execution.2 execution.1
  let collision : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec → Prop :=
    fun result => Rom.AdaptiveFreshDigestCollisionWith keyResult.2 result.2
      (keygenStructuralTargetInput keyResult.1.2 keyResult.2)
  let accepted : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec → Prop :=
    fun result => HasAcceptedEncoding keyResult.1.2.parameter result.2
  let adversaryRun := (simulateQ romImpl
    (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2
  let rate := (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)
  have hpointwise : ∀ result ∈ support adversaryRun,
      Pr[event | (simulateQ romImpl
        (verificationPhase keyResult.1.1 keyResult.1.2 result.1)).run result.2] ≤
          (if collision result then 1 else 0) + (if accepted result then rate else 0) := by
    intro result hresult
    by_cases haccepted : accepted result
    · rw [if_pos haccepted]
      by_cases hcollision : collision result
      · rw [if_pos hcollision]
        exact le_add_right probEvent_le_one
      · rw [if_neg hcollision, zero_add]
        calc
          _ ≤ expectedSimulatedQueryCount romImpl
                (Rom.IsRelevantHashQuery fun input =>
                  decidingTargetInput keyResult.1.2 keyResult.2 result.1.1.epoch
                    (outcomeDecidingChain result.2
                      ⟨keyResult.1.1, keyResult.1.2, result.1.1, result.1.2, false⟩)
                    input ≠ input)
                (verificationPhase keyResult.1.1 keyResult.1.2 result.1) result.2 /
                ((2 ^ digestBits : ℕ) : ℝ≥0∞) :=
            Rom.mixed_adaptiveFreshDigestCollisionWith_le_expected_moved _ _ _ event
              (fun execution hexecution hwin => deciding_afterKeygen_orientation adversary
                keyResult hkey result hresult (hcached result hresult) execution hexecution
                hwin.1 hwin.2.1 hwin.2.2 hcollision)
          _ ≤ rate := by
            apply ENNReal.div_le_div _ le_rfl
            rw [expectedQueries_verificationPhase_eq]
            simpa only [decidingQueryBound_eq, Nat.cast_ofNat] using
              expectedSimulatedQueryCount_verify_deciding_le keyResult.1.2 keyResult.2
                keyResult.1.1 (keygen_publicKey_parameter_eq keyResult hkey)
                result.1.1.epoch result.1.1.message result.1.1.signature _ result.2
    · have hzero : Pr[event | (simulateQ romImpl
          (verificationPhase keyResult.1.1 keyResult.1.2 result.1)).run result.2] = 0 := by
        apply probEvent_eq_zero
        intro execution hexecution hwin
        exact haccepted (winning_verification_hasAcceptedEncoding_at_prefix adversary keyResult
          hkey result hresult (hcached result hresult) execution hexecution hwin.1)
      rw [hzero]
      exact zero_le
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' result, Pr[= result | adversaryRun] *
        ((if collision result then 1 else 0) + (if accepted result then rate else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support adversaryRun
      · exact mul_le_mul' le_rfl (hpointwise result hresult)
      · change Pr[= result | adversaryRun] * _ ≤ _
        rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ = Pr[collision | adversaryRun] + Pr[accepted | adversaryRun] * rate := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite,
        ← ENNReal.tsum_mul_right]
      congr 1 <;> apply tsum_congr <;> intro result <;> split_ifs <;> simp
    _ ≤ _ := add_le_add
      (Rom.mixed_adaptiveFreshDigestCollisionWith_le_expected_moved _ _ _ collision
        (fun _ _ h => h)) le_rfl

noncomputable def expectedPrefixEncodingQueries (adversary : Adversary) : ℝ≥0∞ :=
  ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
    expectedSimulatedQueryCount romImpl
      (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
      (adversaryPhase adversary keyResult.1.1 keyResult.1.2) keyResult.2

/-- The deciding-path allowance is amortized over encoding queries in the adversary phase,
including the honest signer's attempts. It is no longer an unconditional additive constant. -/
theorem decidingSecondLane_probability_le_expectedEncoding (adversary : Adversary)
    (hcached : ∀ keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅),
      ∀ result ∈ support ((simulateQ romImpl
        (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2),
        result.2 (CacheView.encodingInput keyResult.1.2.parameter result.1.1.epoch
          (result.1.1.message, result.1.1.signature.randomness)) ≠ none) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ DecidingChainValueRevealed execution.2 execution.1 |
      detailedGameWithCache Concrete.scheme adversary] ≤
      Direct.expectedDirectStructuralQueries adversary / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        expectedPrefixEncodingQueries adversary *
          (TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))) := by
  unfold detailedGameWithCache detailedGameCore
  simp only [detailedGameAfterKeygen_eq_phases]
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  let structural := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    expectedSimulatedQueryCount
      (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      (Direct.IsDirectStructuralQuery keyResult.1.2 keyResult.2)
      (adversary.main keyResult.1.1) keyResult.2
  let encoding := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    expectedSimulatedQueryCount romImpl
      (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
      (adversaryPhase adversary keyResult.1.1 keyResult.1.2) keyResult.2
  let rate := TargetSum.acceptanceProbability *
    ((40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))
  calc
    _ ≤ ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
        (structural keyResult / ((2 ^ digestBits : ℕ) : ℝ≥0∞) + encoding keyResult * rate) := by
      apply ENNReal.tsum_le_tsum
      intro keyResult
      by_cases hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)
      · apply mul_le_mul' le_rfl
        have hsecond := decidingSecondLane_afterKeygen_le_expected_accepted adversary keyResult
          hkey (hcached keyResult hkey)
        rw [Direct.expectedStructuralQueries_adversaryPhase_eq] at hsecond
        apply hsecond.trans
        apply add_le_add le_rfl
        have haccepted := probEvent_hasAcceptedEncoding_le_expectedQueries
          keyResult.1.2.parameter (adversaryPhase adversary keyResult.1.1 keyResult.1.2)
          keyResult.2 (precomputedKeygen_no_acceptedEncoding keyResult hkey)
        calc
          _ ≤ (TargetSum.acceptanceProbability * encoding keyResult) *
              ((40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) := mul_le_mul' haccepted le_rfl
          _ = encoding keyResult * rate := by dsimp only [rate]; ac_rfl
      · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]
    _ = _ := by
      simp_rw [mul_add, div_eq_mul_inv, ← mul_assoc]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
      change Direct.expectedDirectStructuralQueries adversary * _ +
        expectedPrefixEncodingQueries adversary * rate = _
      simp only [rate, div_eq_mul_inv, mul_assoc]

/-- info: 'XmssSecurity.Deciding.decidingSecondLane_probability_le_expectedEncoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decidingSecondLane_probability_le_expectedEncoding

end XmssSecurity.Deciding
