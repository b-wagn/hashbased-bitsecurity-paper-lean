import XmssSecurity.Proof.EUFCMA.SecondLane
import XmssSecurity.Proof.Direct.QueriedEncodingAcceptance

/-! The additional encoding query makes no structural query. Retain this fact
when bounding the standard second lane, instead of charging it twice. -/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.EUFCMA

open Concrete Deciding Direct

theorem expectedDirectStructuralQueries_withForgedEncodingQuery (adversary : XmssSecurity.Adversary) :
    expectedDirectStructuralQueries (withForgedEncodingQuery adversary) =
      expectedDirectStructuralQueries adversary := by
  unfold expectedDirectStructuralQueries
  apply tsum_congr
  intro key
  by_cases hkey : key ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)
  · rw [← expectedStructuralQueries_adversaryPhase_eq, ← expectedStructuralQueries_adversaryPhase_eq,
      expectedStructuralQueries_withForgedEncodingQuery_eq adversary key.1.1 key.1.2
        (keygen_publicKey_parameter_eq key hkey)]
  · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]

theorem secondLane_withForgedEncodingQuery_le (adversary : XmssSecurity.Adversary) (D : ℕ)
    (hD : IsDirectQueryBound adversary D) :
    Pr[fun execution : GameOutcome × QueryCache HashSpec => standardWon execution.1 = true ∧
        ¬ OutcomeBadEventOccurs execution.2 execution.1 .encoding ∧
        ¬ DecidingChainValueRevealed execution.2 execution.1 |
      detailedGameWithCache Concrete.scheme (withForgedEncodingQuery adversary)] ≤
      (D : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞) + ((D + 1 : ℕ) : ℝ≥0∞) *
        (Checksum.acceptanceProbability * ((40 : ℝ≥0∞) / ((2 ^ digestBits : ℕ) : ℝ≥0∞))) := by
  have hqueried := withForgedEncodingQuery_isDirectQueryBound adversary D hD
  have hsecond := decidingSecondLane_probability_le_expectedEncoding (withForgedEncodingQuery adversary) (by
    intro key hkey result hresult
    have hcached := adversaryPhase_withForgedEncodingQuery_cached adversary key.1.1 key.1.2 key.2 result hresult
    rw [keygen_publicKey_parameter_eq key hkey] at hcached
    exact hcached)
  rw [expectedDirectStructuralQueries_withForgedEncodingQuery] at hsecond
  apply hsecond.trans
  apply add_le_add
  · apply ENNReal.div_le_div _ le_rfl
    calc
      _ ≤ expectedDirectEncodingQueries adversary + expectedDirectStructuralQueries adversary := le_add_left le_rfl
      _ ≤ _ := expectedDirectEncodingQueries_add_structural_le adversary D hD
  · apply mul_le_mul' _ le_rfl
    calc
      _ ≤ expectedDirectEncodingQueries (withForgedEncodingQuery adversary) +
          expectedDirectStructuralQueries (withForgedEncodingQuery adversary) := le_add_right le_rfl
      _ ≤ _ := expectedDirectEncodingQueries_add_structural_le (withForgedEncodingQuery adversary) (D + 1) hqueried

/-- info: 'XmssSecurity.EUFCMA.secondLane_withForgedEncodingQuery_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms secondLane_withForgedEncodingQuery_le

end XmssSecurity.EUFCMA
