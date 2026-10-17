import XmssSecurity.Proof.TargetSum.Direct.Bridge
import XmssSecurity.Proof.TargetSum.Direct.SeedGuessing
import XmssSecurity.Proof.TargetSum.Direct.VerifierBound
import XmssSecurity.Proof.TargetSum.Direct.FirstLane
import XmssSecurity.Proof.TargetSum.Direct.Structural
import XmssSecurity.Proof.TargetSum.Direct.Prehit
import XmssSecurity.Proof.TargetSum.CappedExactFirstLane

/-!
# Direct-count security of XMSS

Assembly of the direct-count bound. For an adversary with at most `D` direct hash queries on every
branch (`IsDirectQueryBound`), the idealized scheme loses at most
`(D + 133 + 42)/2^128` on the first lane, `(D + 133)/2^128` on the structural part of the second
lane, `D · 2^32 / 2^192` on the encoding-prehit part, and the real scheme adds the seed-guessing
term `D / 2^256`. Altogether at most `312 · D / 2^128 ≤ D / 2^119`.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.Direct

/-- The idealized scheme against a syntactically bounded adversary. -/
theorem concrete_forgeAdvantage_le_direct (adversary : Adversary) (D : ℕ)
    (hD : IsDirectQueryBound adversary D) :
    forgeAdvantage Concrete.scheme adversary ≤
      ((D + verifierQueryBound + numChains : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
      ((signingAttemptLimit : ℝ≥0∞) * D * ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹ +
        ((D + verifierQueryBound : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) := by
  have hverify := fun publicKey leafIndex message signature cache =>
    scheme_verify_hashQueryBound publicKey leafIndex message signature cache
  calc
    forgeAdvantage Concrete.scheme adversary ≤
        Pr[WinningExactFirstLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] +
        Pr[WinningSecondLaneBadEventOccurs | cappedDetailedGameWithEncodingTrace adversary] :=
      capped_forgeAdvantage_le_exactFirstLane_add_secondLane adversary
    _ ≤ ((D + verifierQueryBound + numChains : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
        (Pr[WinningEncodingPrehitOccurs | cappedDetailedGameWithEncodingTrace adversary] +
          Pr[fun execution : CappedEncodingTraceExecution =>
              WinningStructuralCollisionOccurs execution.2.1.1 execution.1 |
            cappedDetailedGameWithEncodingTrace adversary]) := by
      refine add_le_add (CappedChain.hasExactFirstLaneBound_direct adversary D hD hverify) ?_
      unfold WinningSecondLaneBadEventOccurs
      exact probEvent_or_le _ _ _
    _ ≤ _ := by
      refine add_le_add le_rfl (add_le_add ?_ ?_)
      · exact winningEncodingPrehit_probability_le_direct adversary D hD
      · exact winningStructuralCollision_probability_le_direct adversary D hD hverify

/-- The real scheme against a syntactically bounded adversary. -/
theorem seeded_forgeAdvantage_le_direct (adversary : Adversary) (D : ℕ)
    (hD : IsDirectQueryBound adversary D) :
    forgeAdvantage Seeded.scheme adversary ≤
      (((D + verifierQueryBound + numChains : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
      ((signingAttemptLimit : ℝ≥0∞) * D * ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹ +
        ((D + verifierQueryBound : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))) +
      D / ((2 ^ 256 : ℕ) : ℝ≥0∞) :=
  (Seeded.forgeAdvantage_deterministic_le_reference_direct adversary D hD).trans
    (add_le_add (concrete_forgeAdvantage_le_direct (Seeded.memoAdversary adversary) D
      (Seeded.memoAdversary_isDirectQueryBound adversary D hD)) le_rfl)

/-- The arithmetic: the four loss terms are at most `D / 2^119` for every `D ≥ 1`. -/
theorem direct_loss_le_119 (D : ℕ) (hD : 1 ≤ D) :
    (((D + verifierQueryBound + numChains : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
      ((signingAttemptLimit : ℝ≥0∞) * D * ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹ +
        ((D + verifierQueryBound : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))) +
      D / ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤ (D : ℝ≥0∞) / ((2 ^ 119 : ℕ) : ℝ≥0∞) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_add]
  simp only [verifierQueryBound_eq, numChains, digestBits, randomnessBits, signingAttemptLimit]
  push_cast
  linarith

/-- XMSS has 119 bits of classical SUF-CMA security counting only the adversary's own hash
queries. -/
theorem sufCmaDirect_119 : SUFCMA.notionDirect.HasClassicalSecurityBits xmss 119 :=
  Security.sufCmaDirect_of_isDirectQueryBound 119 fun adversary D hD hbound =>
    (seeded_forgeAdvantage_le_direct adversary D hbound).trans (direct_loss_le_119 D hD)

end XmssSecurity.TargetSum.Direct
