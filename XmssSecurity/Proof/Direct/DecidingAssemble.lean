import XmssSecurity.Proof.Direct.DecidingFirstLane
import XmssSecurity.Proof.Direct.Bridge
import XmssSecurity.Proof.Direct.SeedGuessing

/-! Assemble the deciding-path estimates without changing the statement layer. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Direct

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

theorem deciding_loss_le_122 (D : ℕ) (hD : 1 ≤ D) :
    decidingLoss D (D + 3) ≤ (D : ℝ≥0∞) / ((2 ^ 122 : ℕ) : ℝ≥0∞) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  unfold decidingLoss
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_add]
  simp only [digestBits, randomnessBits, signingAttemptLimit]
  push_cast
  linarith

/-- A conditional assembly for the original trace event. `DecidingSecurity.sufCmaDirect_122`
discharges the security claim unconditionally using the modified adversary's prefix bound. -/
theorem sufCmaDirect_122_of_decidingFirstLaneBounds
    (hfirst : ∀ (adversary : Adversary) (D : ℕ), 1 ≤ D → IsDirectQueryBound adversary D →
      Deciding.HasDecidingFirstLaneBound adversary D) :
    SUFCMA.notionDirect.HasClassicalSecurityBits xmss 122 := by
  apply Security.sufCmaDirect_of_isDirectQueryBound
  intro adversary D hD hbound
  apply (seeded_forgeAdvantage_le_decidingLoss adversary D (D + 3) hbound
    (hfirst _ D hD (Seeded.memoAdversary_isDirectQueryBound adversary D hbound))).trans
  exact deciding_loss_le_122 D hD

end XmssSecurity.Direct
