import XmssSecurity.Proof.TargetSum.CappedEncodingPrehitExpectedBound
import XmssSecurity.Proof.TargetSum.CappedUnifiedExpectedDigest
import XmssSecurity.Proof.TargetSum.LossDecomposition

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum

def WinningSecondLaneBadEventOccurs
    (execution : CappedEncodingTraceExecution) : Prop :=
  WinningEncodingPrehitOccurs execution ∨
    WinningStructuralCollisionOccurs execution.2.1.1 execution.1

def HasSecondLaneBound
    (q : Nat) (adversary : Adversary) : Prop :=
  Pr[WinningSecondLaneBadEventOccurs |
      cappedDetailedGameWithEncodingTrace adversary] ≤
    (q - treeHashQueryCount treeHeight : Nat) /
      ((2 ^ digestBits : Nat) : ENNReal)

theorem capped_two_lane_loss_budget_le_127
    (q : Nat) (hkeygen : treeHashQueryCount treeHeight ≤ q) :
    ((q - treeHashQueryCount treeHeight : Nat) + numChains : Nat) /
          ((2 ^ digestBits : Nat) : ENNReal) +
        (q - treeHashQueryCount treeHeight : Nat) /
          ((2 ^ digestBits : Nat) : ENNReal) ≤
      (q : ENNReal) / ((2 ^ 127 : Nat) : ENNReal) := by
  simp only [div_eq_mul_inv]
  have hnumerator :
      (((q - treeHashQueryCount treeHeight : Nat) + numChains : Nat) :
          ENNReal) +
        (q - treeHashQueryCount treeHeight : Nat) ≤ 2 * (q : ENNReal) := by
    exact_mod_cast (show
      (q - treeHashQueryCount treeHeight + numChains) +
          (q - treeHashQueryCount treeHeight) ≤ 2 * q by
      have hconstant : numChains ≤ 2 * treeHashQueryCount treeHeight := by
        decide
      omega)
  calc
    (((q - treeHashQueryCount treeHeight : Nat) + numChains : Nat) :
        ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        (q - treeHashQueryCount treeHeight : Nat) *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ =
      ((((q - treeHashQueryCount treeHeight : Nat) + numChains : Nat) :
          ENNReal) +
        (q - treeHashQueryCount treeHeight : Nat)) *
          ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by ring
    _ ≤ (2 * (q : ENNReal)) *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by gcongr
    _ = (q : ENNReal) * ((2 ^ 127 : Nat) : ENNReal)⁻¹ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast]
      norm_num [digestBits]
      ring

end XmssSecurity.TargetSum
