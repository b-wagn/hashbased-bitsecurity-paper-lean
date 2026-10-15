import XmssSecurity.Proof.Direct.Assemble

/-!
# Direct security for budgets of at least five queries

The existing loss estimate already proves the 122-bit bound at these budgets. Only the budgets
one through four require the sharper deciding-path argument.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Direct

theorem direct_loss_le_122_of_five_le (D : ℕ) (hD : 5 ≤ D) :
    (((D + verifierQueryBound + numChains : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
      ((signingAttemptLimit : ℝ≥0∞) * D * ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹ +
        ((D + verifierQueryBound : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))) +
      D / ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤ (D : ℝ≥0∞) / ((2 ^ 122 : ℕ) : ℝ≥0∞) := by
  have hD' : (5 : ℝ) ≤ D := by exact_mod_cast hD
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_add]
  simp only [verifierQueryBound_eq, numChains, digestBits, randomnessBits, signingAttemptLimit]
  push_cast
  linarith

theorem seeded_forgeAdvantage_le_122_of_five_le (adversary : Adversary) (D : ℕ)
    (hD : 5 ≤ D) (hbound : IsDirectQueryBound adversary D) :
    forgeAdvantage Seeded.scheme adversary ≤ (D : ℝ≥0∞) / ((2 ^ 122 : ℕ) : ℝ≥0∞) :=
  (seeded_forgeAdvantage_le_direct adversary D hbound).trans (direct_loss_le_122_of_five_le D hD)

theorem sufCmaDirect_advantage_le_122_of_five_le (adversary : Security.StatementAdversary)
    (D : ℕ) (hD : 5 ≤ D) (hbound : SUFCMA.notionDirect.HasQueryBound xmss adversary D) :
    SUFCMA.notionDirect.advantage xmss adversary ≤ (D : ℝ≥0∞) / ((2 ^ 122 : ℕ) : ℝ≥0∞) := by
  rw [Security.notionDirect_advantage_eq, Security.forgeAdvantage_prune_eq adversary D hbound]
  exact seeded_forgeAdvantage_le_122_of_five_le _ D hD
    (pruneAdversary_isDirectQueryBound D (Security.embed adversary))

/-- Completing the four small-budget estimates suffices for the full 122-bit claim. -/
theorem sufCmaDirect_122_of_small_budgets
    (hsmall : ∀ (adversary : Adversary) (D : ℕ), 1 ≤ D → D < 5 →
      IsDirectQueryBound adversary D →
      forgeAdvantage Seeded.scheme adversary ≤ (D : ℝ≥0∞) / ((2 ^ 122 : ℕ) : ℝ≥0∞)) :
    SUFCMA.notionDirect.HasClassicalSecurityBits xmss 122 := by
  apply Security.sufCmaDirect_of_isDirectQueryBound
  intro adversary D hD hbound
  by_cases hlarge : 5 ≤ D
  · exact seeded_forgeAdvantage_le_122_of_five_le adversary D hlarge hbound
  · exact hsmall adversary D hD (Nat.lt_of_not_ge hlarge) hbound

end XmssSecurity.Direct
