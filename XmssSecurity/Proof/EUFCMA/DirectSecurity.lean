import XmssSecurity.Proof.EUFCMA.DecidingAssembly
import XmssSecurity.Proof.EUFCMA.ReferenceHop
import XmssSecurity.Statement.EUFCMAClaims

/-! An intermediate direct-security bound. Standard freshness removes the free
forty-query second-lane allowance, improving the inherited 122-bit result to 125
bits. This does not settle the exact direct-query classification. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.EUFCMA

open Direct

noncomputable def directPrefixLoss (D : ℕ) : ℝ≥0∞ :=
  ((D + 2 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
    ((signingAttemptLimit : ℝ≥0∞) * ((D + 1 : ℕ) : ℝ≥0∞) * ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹ +
      ((D + 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞)) +
    D / ((2 ^ 256 : ℕ) : ℝ≥0∞)

theorem reference_advantage_add_seed_loss_le (adversary : XmssSecurity.Adversary) (D : ℕ)
    (hD : IsDirectQueryBound adversary D) :
    forgeAdvantage Concrete.scheme adversary + D / ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤ directPrefixLoss D := by
  let queried := withForgedEncodingQuery adversary
  have hqueried := withForgedEncodingQuery_isDirectQueryBound adversary D hD
  rw [← forgeAdvantage_withForgedEncodingQuery adversary]
  unfold directPrefixLoss
  apply add_le_add _ le_rfl
  apply (forgeAdvantage_le_deciding_lanes queried).trans
  apply add_le_add
    (Deciding.decidingFirstLane_withForgedEncodingQuery_probability_le adversary D hD)
  apply add_le_add
  · exact winningEncodingPrehit_probability_le_direct queried (D + 1) hqueried
  · apply decidingSecondLane_probability_le_direct queried (D + 1) hqueried
    intro keyResult hkey result hresult
    have hcached := adversaryPhase_withForgedEncodingQuery_cached adversary keyResult.1.1
      keyResult.1.2 keyResult.2 result hresult
    rw [Deciding.keygen_publicKey_parameter_eq keyResult hkey] at hcached
    exact hcached

theorem directPrefixLoss_le_125 (D : ℕ) (hD : 1 ≤ D) :
    directPrefixLoss D ≤ (D : ℝ≥0∞) / ((2 ^ 125 : ℕ) : ℝ≥0∞) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  unfold directPrefixLoss
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_add]
  simp only [digestBits, randomnessBits, signingAttemptLimit]
  push_cast
  linarith

theorem directPrefixLoss_le_126_of_two_le (D : ℕ) (hD : 2 ≤ D) :
    directPrefixLoss D ≤ (D : ℝ≥0∞) / ((2 ^ 126 : ℕ) : ℝ≥0∞) := by
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  unfold directPrefixLoss
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_add]
  simp only [digestBits, randomnessBits, signingAttemptLimit]
  push_cast
  linarith

theorem direct_125 : XmssEufCmaSecure SUFCMA.CountingMode.direct 125 := by
  apply direct_security_of_reference_bound
  intro adversary D hD hbound
  exact (reference_advantage_add_seed_loss_le adversary D hbound).trans (directPrefixLoss_le_125 D hD)

/-- info: 'XmssSecurity.EUFCMA.direct_125' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms direct_125

end XmssSecurity.EUFCMA
