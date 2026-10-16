import XmssSecurity.Proof.EUFCMA.FreshFirstLaneBridge
import XmssSecurity.Proof.EUFCMA.QueriedStructural
import XmssSecurity.Proof.EUFCMA.ReferenceHop
import XmssSecurity.Proof.EUFCMA.ReplayAccounting

/-! Exact 126-bit standard unforgeability when only direct queries are counted.
The fresh-encoding gate pays for the terminal probe, including the one-query case. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.EUFCMA

open Direct

noncomputable def directFreshLoss (D : ℕ) : ℝ≥0∞ :=
  ((2 * D + 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
    TargetSum.acceptanceProbability * ((41 * (D + 1) : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
    (signingAttemptLimit : ℝ≥0∞) * ((D + 1 : ℕ) : ℝ≥0∞) * ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹ +
    D / ((2 ^ 256 : ℕ) : ℝ≥0∞)

theorem reference_advantage_add_seed_loss_le_fresh (adversary : XmssSecurity.Adversary) (D : ℕ)
    (hD : IsDirectQueryBound adversary D) :
    forgeAdvantage Concrete.scheme adversary + D / ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤ directFreshLoss D := by
  have hqueried := withForgedEncodingQuery_isDirectQueryBound adversary D hD
  rw [← forgeAdvantage_withForgedEncodingQuery adversary]
  have hbound := (forgeAdvantage_le_fresh_deciding_lanes (withForgedEncodingQuery adversary)).trans
    (add_le_add (freshFirstLane_withForgedEncodingQuery_probability_le adversary D hD)
      (add_le_add (winningEncodingPrehit_probability_le_direct (withForgedEncodingQuery adversary) (D + 1) hqueried)
        (secondLane_withForgedEncodingQuery_le adversary D hD)))
  apply (add_le_add hbound le_rfl).trans_eq
  simp only [directFreshLoss, Nat.cast_add, Nat.cast_mul, Nat.cast_one, div_eq_mul_inv]
  ring

theorem directFreshLoss_le_126 (D : ℕ) (hD : 1 ≤ D) :
    directFreshLoss D ≤ (D : ℝ≥0∞) / ((2 ^ 126 : ℕ) : ℝ≥0∞) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hpfinite := TargetSum.acceptanceProbability_ne_top
  have hp : TargetSum.acceptanceProbability.toReal ≤ (1 : ℝ) / 2 ^ 14 := by
    have h := (ENNReal.toReal_le_toReal hpfinite (by finiteness)).mpr TargetSum.acceptanceProbability_upper.le
    norm_num [ENNReal.toReal_div] at h ⊢
    exact h
  have hmul := mul_le_mul_of_nonneg_right hp (show (0 : ℝ) ≤ (D : ℝ) + 1 by positivity)
  unfold directFreshLoss
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_one, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  simp only [digestBits, randomnessBits, signingAttemptLimit]
  push_cast
  nlinarith

theorem direct_126 : (EUFCMA.notion SUFCMA.CountingMode.direct).HasClassicalSecurityBits xmss 126 := by
  apply direct_security_of_reference_bound
  intro adversary D hD hbound
  exact (reference_advantage_add_seed_loss_le_fresh adversary D hbound).trans (directFreshLoss_le_126 D hD)

theorem direct_exact_126 : (notion SUFCMA.CountingMode.direct).HasExactClassicalSecurityBits xmss 126 :=
  ⟨direct_126, replay_direct_attack_126⟩

/-- info: 'XmssSecurity.EUFCMA.direct_exact_126' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms direct_exact_126

end XmssSecurity.EUFCMA
