import XmssSecurity.Proof.Checksum.Direct.DecidingSecondLaneExpected

/-! The deciding-path collision on the executions with a signing request: the forty
verification queries along the deciding path are charged with the probability that the
adversary signs. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.Deciding

open Concrete

theorem decidingSecondLane_signed_afterKeygen_le_expected (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hcached : ∀ prefixResult ∈ support
        ((simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2),
        prefixResult.2 (Concrete.CacheView.encodingInput keyResult.1.2.parameter
          prefixResult.1.1.epoch
          (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none)
    (horient : ∀ prefixResult ∈ support
        ((simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2),
        prefixResult.2 (Concrete.CacheView.encodingInput keyResult.1.2.parameter
          prefixResult.1.1.epoch
          (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none →
        ∀ execution ∈ support ((simulateQ romImpl
          (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2),
          execution.1.won = true →
          ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding →
          ¬ DecidingChainValueRevealed execution.2 execution.1 →
          ¬ Rom.AdaptiveFreshDigestCollisionWith keyResult.2 prefixResult.2
            (keygenStructuralTargetInput keyResult.1.2 keyResult.2) →
          Rom.AdaptiveFreshDigestCollisionWith prefixResult.2 execution.2
            (decidingTargetInput keyResult.1.2 keyResult.2 prefixResult.1.1.epoch
              (outcomeDecidingChain prefixResult.2
                ⟨keyResult.1.1, keyResult.1.2, prefixResult.1.1, prefixResult.1.2, false⟩)))
    (hcount : ∀ (leafIndex : LeafIndex) (message : Message) (signature : Signature)
        (chain : ChainIndex) (initialCache : QueryCache HashSpec),
        expectedSimulatedQueryCount romImpl
          (Rom.IsRelevantHashQuery fun input =>
            decidingTargetInput keyResult.1.2 keyResult.2 leafIndex chain input ≠ input)
          (Concrete.scheme.verify keyResult.1.1 leafIndex message signature) initialCache ≤ 40) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ DecidingChainValueRevealed execution.2 execution.1 ∧ execution.1.signingLog ≠ [] |
      (simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
        verificationPhase keyResult.1.1 keyResult.1.2)).run keyResult.2] ≤
      expectedSimulatedQueryCount romImpl
        (Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input)
        (adversaryPhase adversary keyResult.1.1 keyResult.1.2) keyResult.2 /
          ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) *
          Pr[fun prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
              prefixResult.1.2 ≠ [] |
            (simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
              keyResult.2] := by
  classical
  let event : GameOutcome × QueryCache HashSpec → Prop := fun execution =>
    execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
      ¬ DecidingChainValueRevealed execution.2 execution.1 ∧ execution.1.signingLog ≠ []
  let collision : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec → Prop :=
    fun prefixResult => Rom.AdaptiveFreshDigestCollisionWith keyResult.2 prefixResult.2
      (keygenStructuralTargetInput keyResult.1.2 keyResult.2)
  let adversaryRun := (simulateQ romImpl
    (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2
  have hpointwise : ∀ prefixResult ∈ support adversaryRun,
      Pr[event | (simulateQ romImpl
          (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2] ≤
        (if collision prefixResult then 1 else 0) +
          (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) *
            (if prefixResult.1.2 ≠ [] then 1 else 0) := by
    intro prefixResult hprefix
    by_cases hsigned : prefixResult.1.2 ≠ []
    swap
    · rw [probEvent_eq_zero fun execution hexecution hevent => hsigned (by
        rw [← (verificationPhase_support _ _ _ _ _ hexecution).2.2.2.1]
        exact hevent.2.2.2)]
      exact zero_le
    rw [if_pos hsigned, mul_one]
    by_cases hcollision : collision prefixResult
    · rw [if_pos hcollision]
      exact le_add_right probEvent_le_one
    · rw [if_neg hcollision, zero_add]
      calc
        _ ≤ expectedSimulatedQueryCount romImpl
              (Rom.IsRelevantHashQuery fun input =>
                decidingTargetInput keyResult.1.2 keyResult.2 prefixResult.1.1.epoch
                  (outcomeDecidingChain prefixResult.2
                    ⟨keyResult.1.1, keyResult.1.2, prefixResult.1.1, prefixResult.1.2, false⟩)
                  input ≠ input)
              (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1) prefixResult.2 /
              ((2 ^ digestBits : ℕ) : ℝ≥0∞) :=
          Rom.mixed_adaptiveFreshDigestCollisionWith_le_expected_moved _ _ _ event
            (fun execution hexecution hwin =>
              horient prefixResult hprefix (hcached prefixResult hprefix) execution hexecution
                hwin.1 hwin.2.1 hwin.2.2.1 hcollision)
        _ ≤ _ := by
          gcongr
          rw [expectedQueries_verificationPhase_eq]
          exact hcount _ _ _ _ _
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  have hsigned : ∑' prefixResult, Pr[= prefixResult | adversaryRun] *
      (if prefixResult.1.2 ≠ [] then 1 else 0) =
      Pr[fun prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
        prefixResult.1.2 ≠ [] | adversaryRun] := by
    rw [probEvent_eq_tsum_ite]
    apply tsum_congr
    intro prefixResult
    split_ifs <;> simp
  calc
    ∑' prefixResult, Pr[= prefixResult | adversaryRun] *
        Pr[event | (simulateQ romImpl
          (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2] ≤
      ∑' prefixResult, Pr[= prefixResult | adversaryRun] *
        ((if collision prefixResult then 1 else 0) +
          (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) *
            (if prefixResult.1.2 ≠ [] then 1 else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro prefixResult
      by_cases hprefix : prefixResult ∈ support adversaryRun
      · gcongr
        exact hpointwise prefixResult hprefix
      · rw [probOutput_eq_zero_of_not_mem_support hprefix, zero_mul, zero_mul]
    _ = (∑' prefixResult, Pr[= prefixResult | adversaryRun] *
          (if collision prefixResult then 1 else 0)) +
        (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) *
          ∑' prefixResult, Pr[= prefixResult | adversaryRun] *
            (if prefixResult.1.2 ≠ [] then 1 else 0) := by
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
      apply tsum_congr
      intro prefixResult
      ring
    _ ≤ _ := by
      rw [hsigned]
      gcongr
      have hind : (∑' prefixResult, Pr[= prefixResult | adversaryRun] *
          (if collision prefixResult then 1 else 0)) = Pr[collision | adversaryRun] := by
        rw [probEvent_eq_tsum_ite]
        apply tsum_congr
        intro prefixResult
        split_ifs <;> simp
      rw [hind]
      exact Rom.mixed_adaptiveFreshDigestCollisionWith_le_expected_moved _ _ _ collision
        (fun _ _ h => h)

/-- The probability that the adversary signs, averaged over key generation. -/
noncomputable def signedProbability (adversary : Adversary) : ℝ≥0∞ :=
  ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
    Pr[fun prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
        prefixResult.1.2 ≠ [] |
      (simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
        keyResult.2]

/-- The second lane on the executions with a request: the forty queries along the deciding path
are charged only with the probability of signing. -/
theorem decidingSecondLane_signed_probability_le_expected (adversary : Adversary)
    (hcached : ∀ keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅),
      ∀ prefixResult ∈ support
        ((simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2),
        prefixResult.2 (Concrete.CacheView.encodingInput keyResult.1.2.parameter
          prefixResult.1.1.epoch
          (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ DecidingChainValueRevealed execution.2 execution.1 ∧ execution.1.signingLog ≠ [] |
      detailedGameWithCache Concrete.scheme adversary] ≤
      Direct.expectedDirectStructuralQueries adversary / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) * signedProbability adversary := by
  unfold detailedGameWithCache detailedGameCore
  simp only [detailedGameAfterKeygen_eq_phases]
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  let count := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    expectedSimulatedQueryCount
      (cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      (Direct.IsDirectStructuralQuery keyResult.1.2 keyResult.2)
      (adversary.main keyResult.1.1) keyResult.2
  let signed := fun keyResult : (PublicKey × SecretKey) × QueryCache HashSpec =>
    Pr[fun prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec =>
        prefixResult.1.2 ≠ [] |
      (simulateQ romImpl (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
        keyResult.2]
  calc
    _ ≤ ∑' keyResult, Pr[= keyResult | (simulateQ romImpl Concrete.scheme.keygen).run ∅] *
        (count keyResult / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
          (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) * signed keyResult) := by
      apply ENNReal.tsum_le_tsum
      intro keyResult
      by_cases hkeygen : keyResult ∈ support
          ((simulateQ romImpl Concrete.scheme.keygen).run ∅)
      · apply mul_le_mul' le_rfl
        have hbound := decidingSecondLane_signed_afterKeygen_le_expected adversary keyResult
          (hcached keyResult hkeygen)
          (by
            intro prefixResult hprefix hcache execution hafter hwin hencoding hrevealed hcollision
            exact deciding_afterKeygen_orientation adversary keyResult hkeygen prefixResult hprefix
              hcache execution hafter hwin hencoding hrevealed hcollision)
          (by
            intro leafIndex message signature chain initialCache
            simpa only [decidingQueryBound_eq, Nat.cast_ofNat] using
              expectedSimulatedQueryCount_verify_deciding_le keyResult.1.2 keyResult.2
                keyResult.1.1 (keygen_publicKey_parameter_eq keyResult hkeygen)
                leafIndex message signature chain initialCache)
        rw [Direct.expectedStructuralQueries_adversaryPhase_eq] at hbound
        exact hbound
      · simp [probOutput_eq_zero_of_not_mem_support hkeygen]
    _ = Direct.expectedDirectStructuralQueries adversary / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) * signedProbability adversary := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add]
      congr 1
      · simp_rw [div_eq_mul_inv, ← mul_assoc]
        rw [ENNReal.tsum_mul_right]
        rfl
      · unfold signedProbability
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun keyResult => by ring

end XmssSecurity.Checksum.Deciding
