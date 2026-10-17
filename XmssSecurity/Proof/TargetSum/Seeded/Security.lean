import XmssSecurity.Proof.TargetSum.Seeded.KeygenBudget
import XmssSecurity.Proof.TargetSum.CappedExactFirstLaneBound

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.Seeded

set_option backward.isDefEq.respectTransparency false

theorem seed_loss_absorbed (q : Nat) (hq : 1 ≤ q) (hsmall : q < 2 ^ 127) :
    ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) +
      ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤
        q / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  have hguess : ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤
      1 / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
    calc
      _ ≤ ((2 ^ 127 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
        ENNReal.div_le_div (by exact_mod_cast (Nat.sub_le q 1).trans hsmall.le) le_rfl
      _ ≤ ((2 ^ 127 : Nat) : ℝ≥0∞) /
          (((2 ^ 127 : Nat) : ℝ≥0∞) * ((2 ^ 127 : Nat) : ℝ≥0∞)) :=
        ENNReal.div_le_div le_rfl (by norm_num)
      _ = _ := by
        simpa only [mul_one] using ENNReal.mul_div_mul_left 1 ((2 ^ 127 : Nat) : ℝ≥0∞)
          (c := ((2 ^ 127 : Nat) : ℝ≥0∞)) (by norm_num) (ENNReal.natCast_ne_top _)
  calc
    _ ≤ ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) +
        1 / ((2 ^ 127 : Nat) : ℝ≥0∞) := add_le_add le_rfl hguess
    _ = _ := by
      rw [← ENNReal.add_div]
      congr 1
      exact_mod_cast Nat.sub_add_cancel hq

end XmssSecurity.TargetSum.Seeded
