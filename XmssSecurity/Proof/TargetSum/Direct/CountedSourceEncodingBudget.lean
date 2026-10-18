import XmssSecurity.Proof.TargetSum.Direct.CountedSourceBudget
import XmssSecurity.Proof.Generic.CappedEncodingPrehitExpectedBound
import XmssSecurity.Proof.TargetSum.Code
import XmssSecurity.Proof.TargetSum.EncodingProbability
/-! Charge source encoding-cache entries to direct encoding queries and actual signer
hashes. This count includes failed signing attempts and allows cached replies. -/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000

namespace XmssSecurity.TargetSum

theorem cachedEncodingInputCount_countHashQueries_le {α : Type}
    (parameter : PublicParameter) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (result : (α × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ Generic.romImpl (Generic.countHashQueries computation)).run cache)) :
    Generic.cachedEncodingInputCount result.2 parameter ≤
      Generic.cachedEncodingInputCount cache parameter + (result.1.2 : ℝ≥0∞) := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simp only [Generic.countHashQueries_pure, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      simp
  | query_bind input next ih =>
      simp only [Generic.countHashQueries_query_bind, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, bind_pure_comp, simulateQ_map, StateT.run_map,
        mem_support_bind_iff, support_map] at hresult
      obtain ⟨head, hhead, tail, htail, rfl⟩ := hresult
      have hcache := Generic.cachedEncodingInputCount_romImpl_step_le parameter input cache head hhead
      have hrest := ih head.1 head.2 tail htail
      have hstep : Generic.cachedEncodingInputCount head.2 parameter ≤
          Generic.cachedEncodingInputCount cache parameter + (Generic.Seeded.queryCost input : ℝ≥0∞) := by
        apply hcache.trans
        apply add_le_add le_rfl
        cases input with
        | inl n => simp [Generic.CappedEncodingMonitor.IsEncodingHashQuery, Generic.Seeded.queryCost]
        | inr input => simp [Generic.Seeded.queryCost]; split_ifs <;> simp
      calc
        _ ≤ (Generic.cachedEncodingInputCount cache parameter + (Generic.Seeded.queryCost input : ℝ≥0∞)) +
            (tail.1.2 : ℝ≥0∞) := hrest.trans (add_le_add hstep le_rfl)
        _ = _ := by
          cases input <;> simp [Generic.Seeded.queryCost, Nat.cast_add, add_assoc]

namespace CappedChain

open Seeded

/-- The number of encoding-hash inputs in an attacker trace. It is declared in the generic
namespace so that field notation on `Generic.CappedChain.AttackerActionTrace` finds it. -/
noncomputable def _root_.XmssSecurity.Generic.CappedChain.AttackerActionTrace.encodingInputCount
    (parameter : PublicParameter) (trace : Generic.CappedChain.AttackerActionTrace) : Nat :=
  trace.hashInputs.countP (fun input => (Generic.encodingInputLeafIndex? parameter input).isSome)

theorem AttackerActionTrace.encodingInputCount_append (parameter : PublicParameter)
    (left right : Generic.CappedChain.AttackerActionTrace) :
    (left ++ right).encodingInputCount parameter =
      left.encodingInputCount parameter + right.encodingInputCount parameter := by
  simp only [Generic.CappedChain.AttackerActionTrace.encodingInputCount, Generic.CappedChain.AttackerActionTrace.hashInputs_append,
    List.countP_append]

theorem attackerActionFragment_encodingInputCount (parameter : PublicParameter)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (output : (OracleWorld + Generic.SigningSpec).Range input) :
    (Generic.CappedChain.attackerActionFragment input output).encodingInputCount parameter =
      match input with
      | .inl worldInput => if Generic.CappedEncodingMonitor.IsEncodingHashQuery parameter worldInput then 1 else 0
      | .inr _ => 0 := by
  simp only [Generic.CappedChain.AttackerActionTrace.encodingInputCount, Generic.CappedChain.attackerActionFragment_hashInputs]
  cases input with
  | inl input =>
      cases input with
      | inl n => simp only [List.countP_nil, Generic.CappedEncodingMonitor.IsEncodingHashQuery, if_false]
      | inr input =>
          have hcount := List.countP_cons
            (p := fun candidate => (Generic.encodingInputLeafIndex? parameter candidate).isSome)
            (a := input) (l := [])
          rw [hcount, List.countP_nil, Nat.zero_add]
          congr 1
  | inr request => rfl

def CountedSourceEncodingBudget (parameter : PublicParameter) (state : CountedSourceState) : Prop :=
  Generic.cachedEncodingInputCount state.counts.cache parameter ≤
    ((state.attackerTrace.encodingInputCount parameter + state.counts.signing : Nat) : ℝ≥0∞)

theorem countedSourceImpl_encodingBudget (secretKey : Generic.SecretKey)
    (input : (OracleWorld + Generic.SigningSpec).Domain) (state : CountedSourceState)
    (hbudget : CountedSourceEncodingBudget secretKey.parameter state)
    (result : (OracleWorld + Generic.SigningSpec).Range input × CountedSourceState)
    (hresult : result ∈ support ((countedSourceImpl secretKey input).run state)) :
    CountedSourceEncodingBudget secretKey.parameter result.2 := by
  simp only [countedSourceImpl, StateT.run, support_map] at hresult
  obtain ⟨handled, hhandled, rfl⟩ := hresult
  cases input with
  | inl input =>
      simp only [referencePhaseCountsImpl, phaseCountsImpl, StateT.run, support_map] at hhandled
      obtain ⟨sample, hsample, rfl⟩ := hhandled
      have hstep := Generic.cachedEncodingInputCount_romImpl_step_le secretKey.parameter input state.counts.cache
        sample hsample
      change Generic.cachedEncodingInputCount sample.2 secretKey.parameter ≤ _
      apply hstep.trans
      apply le_trans (add_le_add hbudget le_rfl)
      simp only [countedSourceUpdate, AttackerActionTrace.encodingInputCount_append,
        attackerActionFragment_encodingInputCount, Nat.cast_add]
      split_ifs <;> simp [add_comm, add_left_comm]
  | inr request =>
      simp only [referencePhaseCountsImpl, phaseCountsImpl, StateT.run, support_map] at hhandled
      obtain ⟨sample, hsample, rfl⟩ := hhandled
      have hstep := cachedEncodingInputCount_countHashQueries_le secretKey.parameter
        (Generic.Concrete.precomputedCappedSign secretKey request.epoch request.message) state.counts.cache sample hsample
      change Generic.cachedEncodingInputCount sample.2 secretKey.parameter ≤ _
      apply hstep.trans
      apply le_trans (add_le_add hbudget le_rfl)
      simp only [countedSourceUpdate, AttackerActionTrace.encodingInputCount_append,
        attackerActionFragment_encodingInputCount, Nat.add_zero, Nat.cast_add, add_assoc]
      exact le_rfl

theorem countedSource_encodingBudget {α : Type} (secretKey : Generic.SecretKey)
    (computation : OracleComp (OracleWorld + Generic.SigningSpec) α) (state : CountedSourceState)
    (hbudget : CountedSourceEncodingBudget secretKey.parameter state) (result : α × CountedSourceState)
    (hresult : result ∈ support ((simulateQ (countedSourceImpl secretKey) computation).run state)) :
    CountedSourceEncodingBudget secretKey.parameter result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hbudget
  | query_bind input next ih =>
      rw [Generic.Direct.run_simulateQ_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      exact ih head.1 head.2 (countedSourceImpl_encodingBudget secretKey input state hbudget head hhead)
        result htail

end CappedChain
end XmssSecurity.TargetSum
