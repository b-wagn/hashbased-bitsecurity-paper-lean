import XmssSecurity.Proof.Generic.Direct.DecidingFirstLaneBridge
import XmssSecurity.Proof.Generic.Direct.DecidingFirstLane
import XmssSecurity.Proof.Generic.Direct.Bridge
import XmssSecurity.Proof.Generic.Direct.SeedGuessing
import XmssSecurity.Proof.Checksum.Code
import XmssSecurity.Proof.Checksum.EncodingProbability
/-! The completed 122-bit direct-query security proof. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Checksum.Direct

noncomputable def decidingPrefixLoss (D : ℕ) : ℝ≥0∞ :=
  ((D + 2 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
    ((signingAttemptLimit : ℝ≥0∞) * ((D + 1 : ℕ) : ℝ≥0∞) * ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹ +
      ((D + 42 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) +
    D / ((2 ^ 256 : ℕ) : ℝ≥0∞)

theorem seeded_forgeAdvantage_le_decidingPrefixLoss (adversary : Generic.Adversary) (D : ℕ)
    (hD : Generic.Direct.IsDirectQueryBound adversary D) :
    Generic.forgeAdvantage Generic.Seeded.scheme adversary ≤ decidingPrefixLoss D := by
  let memo := Generic.Seeded.memoAdversary adversary
  let queried := Generic.Direct.withForgedEncodingQuery memo
  have hmemo := Generic.Seeded.memoAdversary_isDirectQueryBound adversary D hD
  have hqueried := Generic.Direct.withForgedEncodingQuery_isDirectQueryBound memo D hmemo
  apply (Generic.Seeded.forgeAdvantage_deterministic_le_reference_direct adversary D hD).trans
  rw [← Generic.Direct.forgeAdvantage_withForgedEncodingQuery memo]
  unfold decidingPrefixLoss
  apply add_le_add _ le_rfl
  apply (Generic.Deciding.forgeAdvantage_le_deciding_lanes queried).trans
  apply add_le_add
    (Generic.Deciding.decidingFirstLane_withForgedEncodingQuery_probability_le memo D hmemo)
  apply add_le_add
  · exact Generic.winningEncodingPrehit_probability_le_direct queried (D + 1) hqueried
  · exact Generic.Deciding.decidingSecondLane_probability_le_direct queried (D + 1) hqueried

theorem decidingPrefixLoss_le_122 (D : ℕ) (hD : 1 ≤ D) :
    decidingPrefixLoss D ≤ (D : ℝ≥0∞) / ((2 ^ 122 : ℕ) : ℝ≥0∞) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  unfold decidingPrefixLoss
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_add]
  simp only [digestBits, randomnessBits, signingAttemptLimit]
  push_cast
  linarith

/-- XMSS has 122 bits of classical security when only direct hash queries are charged. -/
theorem sufCmaDirect_122 : SUFCMA.notionDirect.HasClassicalSecurityBits Generic.xmss 122 := by
  apply Generic.Security.sufCmaDirect_of_isDirectQueryBound
  intro adversary D hD hbound
  exact (seeded_forgeAdvantage_le_decidingPrefixLoss adversary D hbound).trans
    (decidingPrefixLoss_le_122 D hD)

end XmssSecurity.Checksum.Direct
