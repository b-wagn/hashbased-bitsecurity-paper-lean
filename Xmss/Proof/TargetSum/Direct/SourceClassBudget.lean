import Xmss.Proof.TargetSum.Direct.SeedQueryPartition
import Xmss.Proof.TargetSum.Direct.CountedSourceCoupling
import Xmss.Proof.TargetSum.ExpectedStateCounter
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability

/-! Encoding, structural, and seed-guessing queries share the actual source direct
count. Together with twice the reference signer cost they obey the same semantic budget. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.TargetSum.CappedExecution

theorem countedSource_expectedDirect_eq {α : Type} (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CountedSourceState)
    (hzero : state.counts.direct = 0) :
    expectedSimulatedQueryCount (countedSourceImpl secretKey) Direct.IsDirectHashQuery computation state =
      ∑' result, Pr[= result | (simulateQ (countedSourceImpl secretKey) computation).run state] *
        (result.2.counts.direct : ℝ≥0∞) := by
  have h := expectedStateCounter_eq_initial_add_queries (countedSourceImpl secretKey)
    Direct.IsDirectHashQuery (fun state => state.counts.direct)
    (fun input state result hresult => by
      rw [countedSourceImpl_direct_eq secretKey input state result hresult, Direct.directHashActionCost_eq_if])
    computation state
  simpa only [hzero, Nat.cast_zero, zero_add] using h.symm

theorem countedSource_expectedClassBudget {α : Type} (secretKey : Generic.SecretKey)
    (targetCache : QueryCache HashSpec) (limit : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CountedSourceState)
    (hzero : state.counts.direct = 0) (hbudget : CountedSourceBudget secretKey limit computation state) :
    expectedSimulatedQueryCount (countedSourceImpl secretKey)
        (Direct.IsDirectEncodingQuery secretKey.parameter) computation state +
      expectedSimulatedQueryCount (countedSourceImpl secretKey)
        (Direct.IsDirectStructuralQuery secretKey targetCache) computation state +
      expectedSimulatedQueryCount (countedSourceImpl secretKey) Direct.IsDirectSeedQuery computation state +
      2 * (∑' result, Pr[= result | (simulateQ (countedSourceImpl secretKey) computation).run state] *
        (result.2.counts.signing : ℝ≥0∞)) ≤ limit := by
  calc
    _ ≤ expectedSimulatedQueryCount (countedSourceImpl secretKey) Direct.IsDirectHashQuery computation state +
        2 * (∑' result, Pr[= result | (simulateQ (countedSourceImpl secretKey) computation).run state] *
          (result.2.counts.signing : ℝ≥0∞)) :=
      add_le_add (Direct.expectedDirect_classes_le (countedSourceImpl secretKey) secretKey targetCache computation state) le_rfl
    _ = ∑' result, Pr[= result | (simulateQ (countedSourceImpl secretKey) computation).run state] *
        (result.2.charge : ℝ≥0∞) := by
      rw [countedSource_expectedDirect_eq secretKey computation state hzero, ← ENNReal.tsum_mul_left,
        ← ENNReal.tsum_add]
      apply tsum_congr
      intro result
      simp only [CountedSourceState.charge, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ ≤ ∑' result, Pr[= result | (simulateQ (countedSourceImpl secretKey) computation).run state] *
        (limit : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hresult : result ∈ support ((simulateQ (countedSourceImpl secretKey) computation).run state)
      · exact mul_le_mul' le_rfl (by exact_mod_cast hbudget result hresult)
      · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact (mul_le_mul' tsum_probOutput_le_one le_rfl).trans_eq (one_mul _)

/-- info: 'Xmss.TargetSum.CappedExecution.countedSource_expectedClassBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms countedSource_expectedClassBudget

end Xmss.TargetSum.CappedExecution
