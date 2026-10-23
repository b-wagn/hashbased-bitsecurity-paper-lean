import Xmss.Proof.TargetSum.Modes.SignerSourceBudget
import Xmss.Proof.TargetSum.Direct.SourceQueryProjection
import Xmss.Proof.TargetSum.Direct.ReferenceSeedQueries
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! The expected losses in the reference experiment use one statement-level signer budget. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum

namespace Modes
open Xmss.Modes

open Seeded CappedExecution Direct

theorem signer_expectedClassBudget (adversary : AdversaryBridge.StatementAdversary)
    (q : Nat) (hsmall : q < 2 ^ 256)
    (hbound : (SUFCMA.notion ⟨false, true, false, false⟩).HasQueryBound Generic.xmss adversary q) :
    Direct.expectedDirectEncodingQueries (Seeded.memoAdversary (AdversaryBridge.embed adversary)) +
      Direct.expectedDirectStructuralQueries (Seeded.memoAdversary (AdversaryBridge.embed adversary)) +
      expectedDirectSeedQueries (Seeded.memoAdversary (AdversaryBridge.embed adversary)) +
      2 * expectedSourceSignerHashes (Seeded.memoAdversary (AdversaryBridge.embed adversary)) ≤ q := by
  unfold Direct.expectedDirectEncodingQueries Direct.expectedDirectStructuralQueries expectedDirectSeedQueries
    expectedSourceSignerHashes
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  calc
    _ ≤ ∑' keyResult, Pr[= keyResult | (simulateQ romImpl precomputedScheme.keygen).run ∅] *
        (q : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro keyResult
      rw [mul_left_comm 2, ← mul_add, ← mul_add, ← mul_add]
      by_cases hkey : keyResult ∈ support ((simulateQ romImpl precomputedScheme.keygen).run ∅)
      · apply mul_le_mul' le_rfl
        exact reference_expectedClassBudget keyResult.1.1 keyResult.1.2 keyResult.2 keyResult.2 q
          ((Seeded.memoAdversary (AdversaryBridge.embed adversary)).main keyResult.1.1)
          (signer_countedSourceBudget_after_keygen adversary q hsmall hbound keyResult hkey)
      · rw [probOutput_eq_zero_of_not_mem_support hkey, zero_mul, zero_mul]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one le_rfl).trans_eq (one_mul _)

/-- info: 'Xmss.TargetSum.Modes.signer_expectedClassBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signer_expectedClassBudget

end Modes
end Xmss.TargetSum
