import XmssSecurity.Proof.TargetSum.Direct.DecidingFirstLane
import XmssSecurity.Proof.TargetSum.Direct.Bridge
import XmssSecurity.Proof.TargetSum.Direct.SeedGuessing

/-! Assemble the deciding-path estimates without changing the statement layer. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.Direct

noncomputable def decidingLoss (D firstLaneQueries : ℕ) : ℝ≥0∞ :=
  (firstLaneQueries : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
    ((signingAttemptLimit : ℝ≥0∞) * D * ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹ +
      ((D + 41 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) +
    D / ((2 ^ 256 : ℕ) : ℝ≥0∞)

theorem seeded_forgeAdvantage_le_decidingLoss (adversary : Adversary) (D firstLaneQueries : ℕ)
    (hD : IsDirectQueryBound adversary D)
    (hfirst : Pr[Deciding.WinningDecidingFirstLaneBadEventOccurs |
      cappedDetailedGameWithEncodingTrace (Seeded.memoAdversary adversary)] ≤
      (firstLaneQueries : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) :
    forgeAdvantage Seeded.scheme adversary ≤ decidingLoss D firstLaneQueries := by
  have hmemo := Seeded.memoAdversary_isDirectQueryBound adversary D hD
  apply (Seeded.forgeAdvantage_deterministic_le_reference_direct adversary D hD).trans
  unfold decidingLoss
  apply add_le_add _ le_rfl
  exact (Deciding.forgeAdvantage_le_deciding_lanes (Seeded.memoAdversary adversary)).trans
    (add_le_add hfirst (add_le_add
      (winningEncodingPrehit_probability_le_direct _ D hmemo)
      (Deciding.decidingSecondLane_probability_le_direct _ D hmemo)))

end XmssSecurity.TargetSum.Direct
