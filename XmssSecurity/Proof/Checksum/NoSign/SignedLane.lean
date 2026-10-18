import XmssSecurity.Proof.Generic.Direct.DecidingSecondLaneExpected
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability
/-! The deciding-path collision on the executions with a signing request: the forty
verification queries along the deciding path are charged with the probability that the
adversary signs. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.Checksum.Deciding

open Concrete

theorem decidingSecondLane_signed_afterKeygen_le_expected (adversary : Generic.Adversary)
    (keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec)
    (hcached : ∀ prefixResult ∈ support
        ((simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2),
        prefixResult.2 (Generic.Concrete.CacheView.encodingInput keyResult.1.2.parameter
          prefixResult.1.1.epoch
          (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none)
    (horient : ∀ prefixResult ∈ support
        ((simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2),
        prefixResult.2 (Generic.Concrete.CacheView.encodingInput keyResult.1.2.parameter
          prefixResult.1.1.epoch
          (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none →
        ∀ execution ∈ support ((simulateQ Generic.romImpl
          (Generic.Deciding.verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2),
          execution.1.won = true →
          ¬ Generic.OutcomeBadEventOccurs execution.2 execution.1 .encoding →
          ¬ Generic.Deciding.DecidingChainValueRevealed execution.2 execution.1 →
          ¬ Generic.Rom.AdaptiveFreshDigestCollisionWith keyResult.2 prefixResult.2
            (Generic.keygenStructuralTargetInput keyResult.1.2 keyResult.2) →
          Generic.Rom.AdaptiveFreshDigestCollisionWith prefixResult.2 execution.2
            (Generic.Deciding.decidingTargetInput keyResult.1.2 keyResult.2 prefixResult.1.1.epoch
              (Generic.Deciding.outcomeDecidingChain prefixResult.2
                ⟨keyResult.1.1, keyResult.1.2, prefixResult.1.1, prefixResult.1.2, false⟩)))
    (hcount : ∀ (leafIndex : LeafIndex) (message : Message) (signature : Generic.Signature)
        (chain : ChainIndex) (initialCache : QueryCache HashSpec),
        expectedSimulatedQueryCount Generic.romImpl
          (Generic.Rom.IsRelevantHashQuery fun input =>
            Generic.Deciding.decidingTargetInput keyResult.1.2 keyResult.2 leafIndex chain input ≠ input)
          (Generic.Concrete.scheme.verify keyResult.1.1 leafIndex message signature) initialCache ≤ 40) :
    Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ Generic.OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ Generic.Deciding.DecidingChainValueRevealed execution.2 execution.1 ∧ execution.1.signingLog ≠ [] |
      (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2 >>=
        Generic.Deciding.verificationPhase keyResult.1.1 keyResult.1.2)).run keyResult.2] ≤
      expectedSimulatedQueryCount Generic.romImpl
        (Generic.Rom.IsRelevantHashQuery fun input =>
          Generic.keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input)
        (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2) keyResult.2 /
          ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) *
          Pr[fun prefixResult : (Generic.Forgery × QueryLog Generic.SigningSpec) × QueryCache HashSpec =>
              prefixResult.1.2 ≠ [] |
            (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
              keyResult.2] := by
  classical
  let event : Generic.GameOutcome × QueryCache HashSpec → Prop := fun execution =>
    execution.1.won = true ∧ ¬ Generic.OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
      ¬ Generic.Deciding.DecidingChainValueRevealed execution.2 execution.1 ∧ execution.1.signingLog ≠ []
  let collision : (Generic.Forgery × QueryLog Generic.SigningSpec) × QueryCache HashSpec → Prop :=
    fun prefixResult => Generic.Rom.AdaptiveFreshDigestCollisionWith keyResult.2 prefixResult.2
      (Generic.keygenStructuralTargetInput keyResult.1.2 keyResult.2)
  let adversaryRun := (simulateQ Generic.romImpl
    (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2
  have hpointwise : ∀ prefixResult ∈ support adversaryRun,
      Pr[event | (simulateQ Generic.romImpl
          (Generic.Deciding.verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2] ≤
        (if collision prefixResult then 1 else 0) +
          (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) *
            (if prefixResult.1.2 ≠ [] then 1 else 0) := by
    intro prefixResult hprefix
    by_cases hsigned : prefixResult.1.2 ≠ []
    swap
    · rw [probEvent_eq_zero fun execution hexecution hevent => hsigned (by
        rw [← (Generic.Deciding.verificationPhase_support _ _ _ _ _ hexecution).2.2.2.1]
        exact hevent.2.2.2)]
      exact zero_le
    rw [if_pos hsigned, mul_one]
    by_cases hcollision : collision prefixResult
    · rw [if_pos hcollision]
      exact le_add_right probEvent_le_one
    · rw [if_neg hcollision, zero_add]
      calc
        _ ≤ expectedSimulatedQueryCount Generic.romImpl
              (Generic.Rom.IsRelevantHashQuery fun input =>
                Generic.Deciding.decidingTargetInput keyResult.1.2 keyResult.2 prefixResult.1.1.epoch
                  (Generic.Deciding.outcomeDecidingChain prefixResult.2
                    ⟨keyResult.1.1, keyResult.1.2, prefixResult.1.1, prefixResult.1.2, false⟩)
                  input ≠ input)
              (Generic.Deciding.verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1) prefixResult.2 /
              ((2 ^ digestBits : ℕ) : ℝ≥0∞) :=
          Generic.Rom.mixed_adaptiveFreshDigestCollisionWith_le_expected_moved _ _ _ event
            (fun execution hexecution hwin =>
              horient prefixResult hprefix (hcached prefixResult hprefix) execution hexecution
                hwin.1 hwin.2.1 hwin.2.2.1 hcollision)
        _ ≤ _ := by
          gcongr
          rw [Generic.Deciding.expectedQueries_verificationPhase_eq]
          exact hcount _ _ _ _ _
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  have hsigned : ∑' prefixResult, Pr[= prefixResult | adversaryRun] *
      (if prefixResult.1.2 ≠ [] then 1 else 0) =
      Pr[fun prefixResult : (Generic.Forgery × QueryLog Generic.SigningSpec) × QueryCache HashSpec =>
        prefixResult.1.2 ≠ [] | adversaryRun] := by
    rw [probEvent_eq_tsum_ite]
    apply tsum_congr
    intro prefixResult
    split_ifs <;> simp
  calc
    ∑' prefixResult, Pr[= prefixResult | adversaryRun] *
        Pr[event | (simulateQ Generic.romImpl
          (Generic.Deciding.verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2] ≤
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
      exact Generic.Rom.mixed_adaptiveFreshDigestCollisionWith_le_expected_moved _ _ _ collision
        (fun _ _ h => h)

/-- The probability that the adversary signs, averaged over key generation. -/
noncomputable def signedProbability (adversary : Generic.Adversary) : ℝ≥0∞ :=
  ∑' keyResult, Pr[= keyResult | (simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅] *
    Pr[fun prefixResult : (Generic.Forgery × QueryLog Generic.SigningSpec) × QueryCache HashSpec =>
        prefixResult.1.2 ≠ [] |
      (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
        keyResult.2]

/-- The second lane on the executions with a request: the forty queries along the deciding path
are charged only with the probability of signing. -/
theorem decidingSecondLane_signed_probability_le_expected (adversary : Generic.Adversary)
    (hcached : ∀ keyResult ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅),
      ∀ prefixResult ∈ support
        ((simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2),
        prefixResult.2 (Generic.Concrete.CacheView.encodingInput keyResult.1.2.parameter
          prefixResult.1.1.epoch
          (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none) :
    Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec =>
        execution.1.won = true ∧ ¬ Generic.OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
          ¬ Generic.Deciding.DecidingChainValueRevealed execution.2 execution.1 ∧ execution.1.signingLog ≠ [] |
      Generic.detailedGameWithCache Generic.Concrete.scheme adversary] ≤
      Generic.Direct.expectedDirectStructuralQueries adversary / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) * signedProbability adversary := by
  unfold Generic.detailedGameWithCache Generic.detailedGameCore
  simp only [Generic.Deciding.detailedGameAfterKeygen_eq_phases]
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  let count := fun keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec =>
    expectedSimulatedQueryCount
      (Generic.cappedUnloggedMappedAdversaryImpl keyResult.1.1 keyResult.1.2)
      (Generic.Direct.IsDirectStructuralQuery keyResult.1.2 keyResult.2)
      (adversary.main keyResult.1.1) keyResult.2
  let signed := fun keyResult : (PublicKey × Generic.SecretKey) × QueryCache HashSpec =>
    Pr[fun prefixResult : (Generic.Forgery × QueryLog Generic.SigningSpec) × QueryCache HashSpec =>
        prefixResult.1.2 ≠ [] |
      (simulateQ Generic.romImpl (Generic.Deciding.adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run
        keyResult.2]
  calc
    _ ≤ ∑' keyResult, Pr[= keyResult | (simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅] *
        (count keyResult / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
          (40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) * signed keyResult) := by
      apply ENNReal.tsum_le_tsum
      intro keyResult
      by_cases hkeygen : keyResult ∈ support
          ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅)
      · apply mul_le_mul' le_rfl
        have hbound := decidingSecondLane_signed_afterKeygen_le_expected adversary keyResult
          (hcached keyResult hkeygen)
          (by
            intro prefixResult hprefix hcache execution hafter hwin hencoding hrevealed hcollision
            exact Generic.Deciding.deciding_afterKeygen_orientation adversary keyResult hkeygen prefixResult hprefix
              hcache execution hafter hwin hencoding hrevealed hcollision)
          (by
            intro leafIndex message signature chain initialCache
            simpa only [Generic.Deciding.decidingQueryBound_eq, Nat.cast_ofNat] using
              Generic.Deciding.expectedSimulatedQueryCount_verify_deciding_le keyResult.1.2 keyResult.2
                keyResult.1.1 (Generic.Deciding.keygen_publicKey_parameter_eq keyResult hkeygen)
                leafIndex message signature chain initialCache)
        rw [Generic.Direct.expectedStructuralQueries_adversaryPhase_eq] at hbound
        exact hbound
      · simp [probOutput_eq_zero_of_not_mem_support hkeygen]
    _ = Generic.Direct.expectedDirectStructuralQueries adversary / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
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
