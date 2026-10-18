import XmssSecurity.Proof.TargetSum.EUFCMA.SecondLane
import XmssSecurity.Proof.TargetSum.Direct.QueriedEncodingAcceptance
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability

/-! The additional encoding query makes no structural query. Retain this fact
when bounding the standard second lane, instead of charging it twice. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.TargetSum.EUFCMA
open XmssSecurity.EUFCMA

open Concrete Deciding Direct

theorem expectedDirectStructuralQueries_withForgedEncodingQuery (adversary : Generic.Adversary) :
    Generic.Direct.expectedDirectStructuralQueries (Generic.Direct.withForgedEncodingQuery adversary) =
      Generic.Direct.expectedDirectStructuralQueries adversary := by
  unfold Generic.Direct.expectedDirectStructuralQueries
  apply tsum_congr
  intro key
  by_cases hkey : key ∈ support ((simulateQ Generic.romImpl Generic.Concrete.scheme.keygen).run ∅)
  · rw [← Generic.Direct.expectedStructuralQueries_adversaryPhase_eq, ← Generic.Direct.expectedStructuralQueries_adversaryPhase_eq,
      expectedStructuralQueries_withForgedEncodingQuery_eq adversary key.1.1 key.1.2
        (Generic.Deciding.keygen_publicKey_parameter_eq key hkey)]
  · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]

theorem secondLane_withForgedEncodingQuery_le (adversary : Generic.Adversary) (D : ℕ)
    (hD : Generic.Direct.IsDirectQueryBound adversary D) :
    Pr[fun execution : Generic.GameOutcome × QueryCache HashSpec => standardWon execution.1 = true ∧
        ¬ Generic.OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
        ¬ Generic.Deciding.DecidingChainValueRevealed execution.2 execution.1 |
      Generic.detailedGameWithCache Generic.Concrete.scheme (Generic.Direct.withForgedEncodingQuery adversary)] ≤
      (D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) + ((D + 1 : ℕ) : ℝ≥0∞) *
        (TargetSum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))) := by
  have hqueried := Generic.Direct.withForgedEncodingQuery_isDirectQueryBound adversary D hD
  have hsecond := decidingSecondLane_probability_le_expectedEncoding (Generic.Direct.withForgedEncodingQuery adversary) (by
    intro key hkey result hresult
    have hcached := Generic.Direct.adversaryPhase_withForgedEncodingQuery_cached adversary key.1.1 key.1.2 key.2 result hresult
    rw [Generic.Deciding.keygen_publicKey_parameter_eq key hkey] at hcached
    exact hcached)
  rw [expectedDirectStructuralQueries_withForgedEncodingQuery] at hsecond
  apply hsecond.trans
  apply add_le_add
  · apply ENNReal.div_le_div _ le_rfl
    calc
      _ ≤ Generic.Direct.expectedDirectEncodingQueries adversary + Generic.Direct.expectedDirectStructuralQueries adversary := le_add_left le_rfl
      _ ≤ _ := Generic.Direct.expectedDirectEncodingQueries_add_structural_le adversary D hD
  · apply mul_le_mul' _ le_rfl
    calc
      _ ≤ Generic.Direct.expectedDirectEncodingQueries (Generic.Direct.withForgedEncodingQuery adversary) +
          Generic.Direct.expectedDirectStructuralQueries (Generic.Direct.withForgedEncodingQuery adversary) := le_add_right le_rfl
      _ ≤ _ := Generic.Direct.expectedDirectEncodingQueries_add_structural_le (Generic.Direct.withForgedEncodingQuery adversary) (D + 1) hqueried

/-- info: 'XmssSecurity.TargetSum.EUFCMA.secondLane_withForgedEncodingQuery_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms secondLane_withForgedEncodingQuery_le

end XmssSecurity.TargetSum.EUFCMA
