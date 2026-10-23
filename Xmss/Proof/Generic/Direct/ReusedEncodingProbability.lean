import Xmss.Proof.Generic.Direct.ReusedEncoding
import Xmss.Proof.Generic.Direct.DecidingSecondLaneExpected

/-! The conditional verification bound when a forgery reuses a returned encoding input. -/

open OracleComp OracleSpec ENNReal

namespace Xmss.Generic.Deciding

variable [Code]

theorem reused_verification_probability_le (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅))
    (prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec)
    (hprefix : prefixResult ∈ support ((simulateQ romImpl
      (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (hreuses : ReusesEncodingInput prefixResult.1.2 prefixResult.1.1)
    (hreturned : returnedAt prefixResult.1.2 prefixResult.1.1.epoch ≠ none)
    (hcached : prefixResult.2 (CacheView.encodingInput keyResult.1.2.parameter
      prefixResult.1.1.epoch (prefixResult.1.1.message, prefixResult.1.1.signature.randomness)) ≠ none)
    (hcollision : ¬ RandomOracle.AdaptiveFreshDigestCollisionWith keyResult.2 prefixResult.2
      (keygenStructuralTargetInput keyResult.1.2 keyResult.2)) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec => execution.1.won = true |
      (simulateQ romImpl
        (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2] ≤
      (48 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  classical
  calc
    _ ≤ expectedSimulatedQueryCount romImpl
          (RandomOracle.IsRelevantHashQuery fun input =>
            decidingTargetInput keyResult.1.2 keyResult.2 prefixResult.1.1.epoch
              (outcomeDecidingChain prefixResult.2
                ⟨keyResult.1.1, keyResult.1.2, prefixResult.1.1, prefixResult.1.2, false⟩)
              input ≠ input)
          (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1) prefixResult.2 /
          ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
      apply RandomOracle.mixed_adaptiveFreshDigestCollisionWith_le_expected_moved
      intro execution hexecution hwin
      have hfields := verificationPhase_support _ _ _ _ _ hexecution
      have hreuses' : ReusesEncodingInput execution.1.signingLog execution.1.forgery := by
        simpa only [hfields.2.2.1, hfields.2.2.2.1] using hreuses
      have hreturned' : returnedAt execution.1.signingLog execution.1.forgery.epoch ≠ none := by
        simpa only [hfields.2.2.1, hfields.2.2.2.1] using hreturned
      exact deciding_afterKeygen_orientation adversary keyResult hkeygen prefixResult hprefix
        hcached execution hexecution hwin
        (not_encoding_event_of_reuses _ _ hreuses')
        (not_deciding_revealed_of_reuses _ _ hreuses' hreturned') hcollision
    _ ≤ _ := by
      apply ENNReal.div_le_div _ le_rfl
      rw [expectedQueries_verificationPhase_eq]
      simpa only [decidingQueryBound_eq, Nat.cast_ofNat] using
        expectedSimulatedQueryCount_verify_deciding_le keyResult.1.2 keyResult.2 keyResult.1.1
          (keygen_publicKey_parameter_eq keyResult hkeygen) prefixResult.1.1.epoch
          prefixResult.1.1.message prefixResult.1.1.signature _ prefixResult.2

end Xmss.Generic.Deciding
