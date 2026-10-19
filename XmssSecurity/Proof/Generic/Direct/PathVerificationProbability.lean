import XmssSecurity.Proof.Generic.Direct.DecidingVerifierRemaining
import XmssSecurity.Proof.Generic.Direct.DecidingSecondLaneExpected

/-! Conditional success on an arbitrarily selected, unrevealed chain. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Generic.Deciding

variable [Code]

theorem path_verification_probability_le (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (prefixResult : (Forgery × QueryLog SigningSpec) × QueryCache HashSpec)
    (hprefix : prefixResult ∈ support ((simulateQ romImpl
      (adversaryPhase adversary keyResult.1.1 keyResult.1.2)).run keyResult.2))
    (encoding : Encoding) (chain : ChainIndex)
    (hdecode : forgedEncoding prefixResult.2 keyResult.1.2.parameter prefixResult.1.1 = some encoding)
    (hvalue : prefixResult.1.1.signature.chainValue chain ≠
      honestChainValue prefixResult.2 keyResult.1.2 prefixResult.1.1.epoch chain (encoding chain))
    (hcollision : ¬ Rom.AdaptiveFreshDigestCollisionWith keyResult.2 prefixResult.2
      (keygenStructuralTargetInput keyResult.1.2 keyResult.2)) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec => execution.1.verified = true |
      (simulateQ romImpl
        (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1)).run prefixResult.2] ≤
      ((decidingQueryBound - (encoding chain).val : ℕ) : ℝ≥0∞) /
        ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
  classical
  calc
    _ ≤ expectedSimulatedQueryCount romImpl
          (Rom.IsRelevantHashQuery fun input =>
            decidingTargetInput keyResult.1.2 keyResult.2 prefixResult.1.1.epoch chain input ≠ input)
          (verificationPhase keyResult.1.1 keyResult.1.2 prefixResult.1) prefixResult.2 /
          ((2 ^ digestBits : ℕ) : ℝ≥0∞) := by
      apply Rom.mixed_adaptiveFreshDigestCollisionWith_le_expected_moved
      intro execution hexecution hverified
      exact path_afterKeygen_orientation adversary keyResult hkeygen prefixResult hprefix
        encoding chain hdecode hvalue execution hexecution hverified hcollision
    _ ≤ _ := by
      apply ENNReal.div_le_div _ le_rfl
      rw [expectedQueries_verificationPhase_eq]
      apply expectedSimulatedQueryCount_verify_remaining_le keyResult.1.2 keyResult.2
        keyResult.1.1 (keygen_publicKey_parameter_eq keyResult hkeygen)
        prefixResult.1.1.epoch prefixResult.1.1.message prefixResult.1.1.signature chain
        prefixResult.2 encoding
      simpa only [forgedEncoding, keygen_publicKey_parameter_eq keyResult hkeygen] using hdecode

end XmssSecurity.Generic.Deciding
