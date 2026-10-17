import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsNumerics
import XmssSecurity.Proof.TargetSum.EUFCMA.RequestsBridge
import XmssSecurity.Proof.TargetSum.Scheme.Xmss
import XmssSecurity.Statement.Security.EUFCMA
import XmssSecurity.Proof.Common.Legacy.PerModeNotionsEUFCMA

/-! Standard unforgeability has 127-bit security when direct hashes and signing
requests share the query budget. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.EUFCMA.Requests
open XmssSecurity.EUFCMA

open Direct

theorem reference_add_seed_le_127 (adversary : XmssSecurity.TargetSum.Adversary) (q : ℕ)
    (hq : 1 ≤ q) (hsmall : q + 1 ≤ 2 ^ 127) (hbound : IsQueryBound adversary q) :
    forgeAdvantage Concrete.scheme adversary + expectedDirectSeedQueries adversary / ((2 ^ 256 : ℕ) : ℝ≥0∞) ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) := by
  have hbudget := expected_class_budget adversary q hbound
  by_cases hlarge : (1 : ℝ≥0∞) / 128 ≤ expectedDirectEncodingQueries adversary
  · exact (reference_add_seed_le_expectedLoss adversary q hsmall hbound).trans
      (expectedLoss_le_127 q _ _ _ _ hbudget hlarge)
  · exact (reference_add_seed_le_terminalLoss adversary q (by omega) hsmall hbound).trans
      (terminalLoss_le_127 q hq _ _ _ _ hbudget (le_of_not_ge hlarge))

theorem secure_127 : (EUFCMA.notion mode).HasClassicalSecurityBits xmss 127 := by
  apply security_of_isQueryBound
  intro adversary q hq hbound
  by_cases hlarge : 2 ^ 127 ≤ q
  · calc
      _ ≤ 1 := probOutput_le_one
      _ = ((2 ^ 127 : ℕ) : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) :=
        (ENNReal.div_self (by norm_num) (ENNReal.natCast_ne_top _)).symm
      _ ≤ _ := ENNReal.div_le_div (by exact_mod_cast hlarge) le_rfl
  exact (forgeAdvantage_deterministic_le_reference_expectedDirectSeed adversary).trans
    (reference_add_seed_le_127 (XmssSecurity.TargetSum.Seeded.memoAdversary adversary) q hq
      (by omega) hbound.memo)

/-- info: 'XmssSecurity.TargetSum.EUFCMA.Requests.secure_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms secure_127

end XmssSecurity.TargetSum.EUFCMA.Requests
