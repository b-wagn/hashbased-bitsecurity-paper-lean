import Xmss.Proof.TargetSum.Direct.CountedSourceBudget
import Xmss.Proof.Generic.CappedEncodingPrehitExpectedBound
import Xmss.Proof.TargetSum.Code
import Xmss.Proof.TargetSum.EncodingProbability
/-! Charge source encoding-cache entries to direct encoding queries and actual signer
hashes. This count includes failed signing attempts and allows cached replies. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

open Xmss.Generic

namespace Xmss.TargetSum

theorem cachedEncodingInputCount_countHashQueries_le {α : Type}
    (parameter : PublicParameter) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (result : (α × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (countHashQueries computation)).run cache)) :
    cachedEncodingInputCount result.2 parameter ≤
      cachedEncodingInputCount cache parameter + (result.1.2 : ℝ≥0∞) := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simp only [countHashQueries_pure, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      simp
  | query_bind input next ih =>
      simp only [countHashQueries_query_bind, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, bind_pure_comp, simulateQ_map, StateT.run_map,
        mem_support_bind_iff, support_map] at hresult
      obtain ⟨head, hhead, tail, htail, rfl⟩ := hresult
      have hcache := cachedEncodingInputCount_romImpl_step_le parameter input cache head hhead
      have hrest := ih head.1 head.2 tail htail
      have hstep : cachedEncodingInputCount head.2 parameter ≤
          cachedEncodingInputCount cache parameter + (Seeded.queryCost input : ℝ≥0∞) := by
        apply hcache.trans
        apply add_le_add le_rfl
        cases input with
        | inl n => simp [CappedEncodingMonitor.IsEncodingHashQuery, Seeded.queryCost]
        | inr input => simp [Seeded.queryCost]; split_ifs <;> simp
      calc
        _ ≤ (cachedEncodingInputCount cache parameter + (Seeded.queryCost input : ℝ≥0∞)) +
            (tail.1.2 : ℝ≥0∞) := hrest.trans (add_le_add hstep le_rfl)
        _ = _ := by
          cases input <;> simp [Seeded.queryCost, Nat.cast_add, add_assoc]

namespace CappedExecution

open Seeded


theorem attackerActionFragment_encodingInputCount (parameter : PublicParameter)
    (input : (OracleWorld + SigningSpec).Domain) (output : (OracleWorld + SigningSpec).Range input) :
    (CappedExecution.attackerActionFragment input output).encodingInputCount parameter =
      match input with
      | .inl worldInput => if CappedEncodingMonitor.IsEncodingHashQuery parameter worldInput then 1 else 0
      | .inr _ => 0 := by
  simp only [CappedExecution.AttackerActionTrace.encodingInputCount, CappedExecution.attackerActionFragment_hashInputs]
  cases input with
  | inl input =>
      cases input with
      | inl n => simp only [List.countP_nil, CappedEncodingMonitor.IsEncodingHashQuery, if_false]
      | inr input =>
          have hcount := List.countP_cons
            (p := fun candidate => (encodingInputLeafIndex? parameter candidate).isSome)
            (a := input) (l := [])
          rw [hcount, List.countP_nil, Nat.zero_add]
          congr 1
  | inr request => rfl

def CountedSourceEncodingBudget (parameter : PublicParameter) (state : CountedSourceState) : Prop :=
  cachedEncodingInputCount state.counts.cache parameter ≤
    ((state.attackerTrace.encodingInputCount parameter + state.counts.signing : Nat) : ℝ≥0∞)

theorem countedSourceImpl_encodingBudget (secretKey : Generic.SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (state : CountedSourceState)
    (hbudget : CountedSourceEncodingBudget secretKey.parameter state)
    (result : (OracleWorld + SigningSpec).Range input × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey input).run state)) :
    CountedSourceEncodingBudget secretKey.parameter result.2 := by
  simp only [countedSourceImpl, StateT.run, support_map] at hresult
  obtain ⟨handled, hhandled, rfl⟩ := hresult
  cases input with
  | inl input =>
      simp only [referencePhaseCountsImpl, phaseCountsImpl, StateT.run, support_map] at hhandled
      obtain ⟨sample, hsample, rfl⟩ := hhandled
      have hstep := cachedEncodingInputCount_romImpl_step_le secretKey.parameter input state.counts.cache
        sample hsample
      change cachedEncodingInputCount sample.2 secretKey.parameter ≤ _
      apply hstep.trans
      apply le_trans (add_le_add hbudget le_rfl)
      simp only [countedSourceUpdate, CappedExecution.AttackerActionTrace.encodingInputCount_append,
        attackerActionFragment_encodingInputCount, Nat.cast_add]
      split_ifs <;> simp [add_comm, add_left_comm]
  | inr request =>
      simp only [referencePhaseCountsImpl, phaseCountsImpl, StateT.run, support_map] at hhandled
      obtain ⟨sample, hsample, rfl⟩ := hhandled
      have hstep := cachedEncodingInputCount_countHashQueries_le secretKey.parameter
        (Signing.precomputedCappedSign secretKey request.epoch request.message) state.counts.cache sample hsample
      change cachedEncodingInputCount sample.2 secretKey.parameter ≤ _
      apply hstep.trans
      apply le_trans (add_le_add hbudget le_rfl)
      simp only [countedSourceUpdate, CappedExecution.AttackerActionTrace.encodingInputCount_append,
        attackerActionFragment_encodingInputCount, Nat.add_zero, Nat.cast_add, add_assoc]
      exact le_rfl

theorem countedSource_encodingBudget {α : Type} (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CountedSourceState)
    (hbudget : CountedSourceEncodingBudget secretKey.parameter state) (result : α × CountedSourceState)
    (hresult : result ∈ support ((simulateQ (countedSourceImpl secretKey) computation).run state)) :
    CountedSourceEncodingBudget secretKey.parameter result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hbudget
  | query_bind input next ih =>
      rw [Direct.run_simulateQ_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      exact ih head.1 head.2 (countedSourceImpl_encodingBudget secretKey input state hbudget head hhead)
        result htail

end CappedExecution
end Xmss.TargetSum
