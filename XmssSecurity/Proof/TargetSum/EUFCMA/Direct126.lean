import XmssSecurity.Proof.TargetSum.EUFCMA.FreshFirstLaneBridge
import XmssSecurity.Proof.TargetSum.EUFCMA.QueriedStructural
import XmssSecurity.Proof.TargetSum.EUFCMA.ReferenceHop
import XmssSecurity.Proof.TargetSum.EUFCMA.ReplayAccounting
import XmssSecurity.Proof.TargetSum.Direct.CollisionLoss
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! Exact 126-bit standard unforgeability when only direct queries are counted.
The fresh-encoding gate pays for the terminal probe, including the one-query case. -/

open OracleComp OracleSpec ENNReal

open XmssSecurity.Generic

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Direct

noncomputable def directFreshLoss (D : ℕ) : ℝ≥0∞ :=
  ((2 * D + 1 : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
    TargetSum.acceptanceProbability * ((49 * (D + 1) : ℕ) : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) +
    ((D + 1 + 2 ^ 86 : ℕ) : ℝ≥0∞) * ((D + 1 : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞) +
    D / ((2 ^ 256 : ℕ) : ℝ≥0∞)

theorem reference_advantage_add_seed_loss_le_fresh (adversary : Adversary) (D : ℕ)
    (hD : Direct.IsDirectQueryBound adversary D) (hsmall : D + 2 ≤ 2 ^ 127) :
    forgeAdvantage Concrete.scheme adversary + D / ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤ directFreshLoss D := by
  have hqueried := Direct.withForgedEncodingQuery_isDirectQueryBound adversary D hD
  rw [← forgeAdvantage_withForgedEncodingQuery adversary]
  have hbound := (forgeAdvantage_le_fresh_deciding_lanes (Direct.withForgedEncodingQuery adversary)).trans
    (add_le_add (freshFirstLane_withForgedEncodingQuery_probability_le adversary D hD)
      (add_le_add (winningEncodingPrehit_probability_le_direct_collision
          (Direct.withForgedEncodingQuery adversary) (D + 1) hqueried (by omega))
        (secondLane_withForgedEncodingQuery_le adversary D hD)))
  apply (add_le_add hbound le_rfl).trans_eq
  simp only [directFreshLoss, Nat.cast_add, Nat.cast_mul, Nat.cast_one, div_eq_mul_inv]
  ring

theorem directFreshLoss_le_126 (D : ℕ) (hD : 1 ≤ D) (hsmall : D + 2 ≤ 2 ^ 127) :
    directFreshLoss D ≤ (D : ℝ≥0∞) / ((2 ^ 126 : ℕ) : ℝ≥0∞) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hsmall' : (D : ℝ) + 2 ≤ 2 ^ 127 := by exact_mod_cast hsmall
  have hquad : 0 ≤ ((D : ℝ) - 1) * (2 ^ 127 - (D : ℝ) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hpfinite := TargetSum.acceptanceProbability_ne_top
  have hp : TargetSum.acceptanceProbability.toReal ≤ (1 : ℝ) / 2 ^ 14 := by
    have h := (ENNReal.toReal_le_toReal hpfinite (by finiteness)).mpr TargetSum.acceptanceProbability_upper.le
    norm_num [ENNReal.toReal_div] at h ⊢
    exact h
  have hmul := mul_le_mul_of_nonneg_right hp (show (0 : ℝ) ≤ (D : ℝ) + 1 by positivity)
  unfold directFreshLoss
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, Nat.cast_add, Nat.cast_mul]
  simp only [digestBits]
  push_cast
  nlinarith

theorem direct_126 : (EUFCMA.notion SUFCMA.CountingMode.direct).HasClassicalSecurityBits Generic.xmss 126 := by
  apply direct_security_of_reference_bound
  intro adversary D hD hbound
  by_cases hlarge : 2 ^ 127 ≤ D + 2
  · have hlarge' : (2 : ℝ) ^ 127 ≤ (D : ℝ) + 2 := by exact_mod_cast hlarge
    calc
      _ ≤ (1 : ℝ≥0∞) + (D : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞) := add_le_add probOutput_le_one le_rfl
      _ ≤ _ := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div,
          ENNReal.toReal_natCast, ENNReal.toReal_one]
        push_cast
        linarith
  · exact (reference_advantage_add_seed_loss_le_fresh adversary D hbound (by omega)).trans
      (directFreshLoss_le_126 D hD (by omega))

end XmssSecurity.TargetSum.EUFCMA
