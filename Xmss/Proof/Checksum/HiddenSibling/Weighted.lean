import Xmss.Proof.Checksum.HiddenSibling.WeightedPrune
import Xmss.Proof.Common.ExpectedQueryCount
import Xmss.Proof.Generic.Deterministic.Memoize
import Xmss.Proof.Generic.Direct.Structural
import Xmss.Proof.Checksum.Code
import Xmss.Proof.Checksum.EncodingProbability
/-!
# Weighted budgets

A program has weighted budget `budget` (`IsWeightedBound signCost`) when on every branch its
direct hash queries and `signCost` per signing request add up to at most `budget`. The pruned
program `pruneWeighted signCost budget` has this bound, and memoizing the signing requests or
answering the hash queries without querying preserves it. In every stateful implementation, the
expected direct hash queries plus `signCost` times the expected signing requests are at most the
budget (`expected_direct_add_sign_le`). With a budget of one request, a request can come only
before every hash query, and the expected number of requests does not depend on how the hash
queries are answered (`expectedSign_eq_of_uniformFaithful`).
-/

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

open Xmss.Generic

namespace Xmss.Checksum.HiddenSibling

/-- The weight of an action: one per direct hash query, `signCost` per signing request. -/
def actionWeight (signCost : ℕ) : (OracleWorld + SigningSpec).Domain → ℕ
  | .inl (.inr _) => 1
  | .inl (.inl _) => 0
  | .inr _ => signCost

/-- On every branch, the direct hash queries and `signCost` per request fit in `budget`. -/
def IsWeightedBound {α : Type} (signCost : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : ℕ) : Prop :=
  computation.IsQueryBound budget (fun input remaining => actionWeight signCost input ≤ remaining)
    (fun input remaining => remaining - actionWeight signCost input)

theorem isWeightedBound_query_bind_iff {α : Type} (signCost budget : ℕ)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) :
    IsWeightedBound signCost (liftM ((OracleWorld + SigningSpec).query input) >>= next) budget ↔
      actionWeight signCost input ≤ budget ∧
        ∀ answer, IsWeightedBound signCost (next answer)
          (budget - actionWeight signCost input) :=
  Iff.rfl

theorem IsWeightedBound.mono {α : Type} {signCost budget budget' : ℕ}
    {computation : OracleComp (OracleWorld + SigningSpec) α}
    (h : IsWeightedBound signCost computation budget) (hle : budget ≤ budget') :
    IsWeightedBound signCost computation budget' := by
  induction computation using OracleComp.inductionOn generalizing budget budget' with
  | pure value => trivial
  | query_bind input next ih =>
      rw [isWeightedBound_query_bind_iff] at h ⊢
      exact ⟨h.1.trans hle, fun answer => ih answer (h.2 answer) (by omega)⟩

/-- A program with weighted budget below `signCost` makes no signing request. -/
theorem IsWeightedBound.noSign {α : Type} {signCost budget : ℕ}
    {computation : OracleComp (OracleWorld + SigningSpec) α}
    (h : IsWeightedBound signCost computation budget) (hlow : budget < signCost) :
    computation.IsQueryBoundP IsSignQuery 0 := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind input next ih =>
      rw [isWeightedBound_query_bind_iff] at h
      rw [isQueryBoundP_query_bind_iff]
      rcases input with world | request
      · exact ⟨Or.inl (by simp [IsSignQuery]), fun answer => by
          simpa [IsSignQuery] using ih answer (h.2 answer) (by omega)⟩
      · exact absurd h.1 (by simp [actionWeight]; omega)

theorem IsWeightedBound.direct {α : Type} {signCost budget : ℕ}
    {computation : OracleComp (OracleWorld + SigningSpec) α}
    (h : IsWeightedBound signCost computation budget) :
    computation.IsQueryBoundP Direct.IsDirectHashQuery budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind input next ih =>
      rw [isWeightedBound_query_bind_iff] at h
      rw [isQueryBoundP_query_bind_iff]
      rcases input with (uniformInput | hashInput) | request
      · refine ⟨Or.inl (by simp), fun answer => ?_⟩
        have := ih answer (h.2 answer)
        simpa [actionWeight] using this
      · have hpositive : 0 < budget := by
          have := h.1
          simp [actionWeight] at this
          omega
        refine ⟨Or.inr hpositive, fun answer => ?_⟩
        have := ih answer (h.2 answer)
        simpa [actionWeight] using this
      · exact ⟨Or.inl (by simp), fun answer => by
          simpa using (ih answer (h.2 answer)).mono (Nat.sub_le _ _)⟩

/-! ## The bound is preserved -/

theorem pruneWeighted_isWeightedBound {α : Type} (signCost budget : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    IsWeightedBound signCost (pruneWeighted signCost budget computation) budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind input next ih =>
      rcases input with (uniformInput | hashInput) | request
      · rw [pruneWeighted_uniform_bind, isWeightedBound_query_bind_iff]
        exact ⟨by simp [actionWeight], fun answer => by simpa [actionWeight] using ih answer budget⟩
      · rw [pruneWeighted_hash_bind]
        split_ifs with hzero
        · subst hzero
          exact ih default 0
        · rw [isWeightedBound_query_bind_iff]
          exact ⟨by simp [actionWeight]; omega, fun answer => by
            simpa [actionWeight] using ih answer (budget - 1)⟩
      · rw [pruneWeighted_sign_bind]
        split_ifs with hlow
        · exact ih none budget
        · rw [isWeightedBound_query_bind_iff]
          exact ⟨by simp [actionWeight]; omega, fun answer => by
            simpa [actionWeight] using ih answer (budget - signCost)⟩

theorem memoize_isWeightedBound {α : Type} (signCost budget : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache SigningSpec)
    (h : IsWeightedBound signCost computation budget) :
    IsWeightedBound signCost (DeterministicSigning.memoize computation cache) budget := by
  induction computation using OracleComp.inductionOn generalizing cache budget with
  | pure value => trivial
  | query_bind input next ih =>
      rw [isWeightedBound_query_bind_iff] at h
      cases input with
      | inl input =>
          rw [DeterministicSigning.memoize_base, isWeightedBound_query_bind_iff]
          exact ⟨h.1, fun answer => ih answer _ cache (h.2 answer)⟩
      | inr request =>
          rw [DeterministicSigning.memoize_request]
          cases hcached : cache request with
          | some answer => exact ih answer budget cache ((h.2 answer).mono (Nat.sub_le _ _))
          | none =>
              rw [isWeightedBound_query_bind_iff]
              exact ⟨h.1, fun answer => ih answer _ _ (h.2 answer)⟩

/-- Answering every direct hash query by `default` without querying. -/
theorem pruneDirect_zero_isWeightedBound {α : Type} (signCost budget : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (h : IsWeightedBound signCost computation budget) :
    IsWeightedBound signCost (Direct.pruneDirect 0 computation) budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind input next ih =>
      rw [isWeightedBound_query_bind_iff] at h
      rcases input with (uniformInput | hashInput) | request
      · rw [Direct.pruneDirect_uniform_bind, isWeightedBound_query_bind_iff]
        exact ⟨h.1, fun answer => ih answer _ (h.2 answer)⟩
      · rw [Direct.pruneDirect_hash_bind, if_pos rfl]
        exact ih default budget ((h.2 default).mono (Nat.sub_le _ _))
      · rw [Direct.pruneDirect_sign_bind, isWeightedBound_query_bind_iff]
        exact ⟨h.1, fun answer => ih answer _ (h.2 answer)⟩

/-! ## The expected weighted count -/

theorem expected_direct_add_sign_le {α σ : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT σ ProbComp)) (signCost budget : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (h : IsWeightedBound signCost computation budget) (state : σ) :
    expectedSimulatedQueryCount impl Direct.IsDirectHashQuery computation state +
        signCost * expectedSimulatedQueryCount impl IsSignQuery computation state ≤ budget := by
  induction computation using OracleComp.inductionOn generalizing budget state with
  | pure value => simp
  | query_bind input next ih =>
      rw [isWeightedBound_query_bind_iff] at h
      rw [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_query_bind]
      have hweight : ((if Direct.IsDirectHashQuery input then 1 else 0 : ℝ≥0∞) +
          signCost * (if IsSignQuery input then 1 else 0 : ℝ≥0∞)) =
          (actionWeight signCost input : ℝ≥0∞) := by
        rcases input with (uniformInput | hashInput) | request <;>
          simp [actionWeight, IsSignQuery]
      have hrest : ∑' result, Pr[= result | (impl input).run state] *
            expectedSimulatedQueryCount impl Direct.IsDirectHashQuery (next result.1) result.2 +
          signCost * ∑' result, Pr[= result | (impl input).run state] *
            expectedSimulatedQueryCount impl IsSignQuery (next result.1) result.2 ≤
          ((budget - actionWeight signCost input : ℕ) : ℝ≥0∞) := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        refine le_of_eq_of_le (b := ∑' result, Pr[= result | (impl input).run state] *
          (expectedSimulatedQueryCount impl Direct.IsDirectHashQuery (next result.1) result.2 +
            signCost * expectedSimulatedQueryCount impl IsSignQuery (next result.1) result.2))
          (tsum_congr fun result => by ring) ?_
        exact Direct.tsum_probOutput_mul_le _ _ _
          fun result : (OracleWorld + SigningSpec).Range input × σ =>
            ih result.1 _ (h.2 result.1) result.2
      calc
        _ = ((if Direct.IsDirectHashQuery input then 1 else 0 : ℝ≥0∞) +
              signCost * (if IsSignQuery input then 1 else 0 : ℝ≥0∞)) +
            (∑' result, Pr[= result | (impl input).run state] *
                expectedSimulatedQueryCount impl Direct.IsDirectHashQuery (next result.1)
                  result.2 +
              signCost * ∑' result, Pr[= result | (impl input).run state] *
                expectedSimulatedQueryCount impl IsSignQuery (next result.1) result.2) := by
          ring
        _ ≤ (actionWeight signCost input : ℝ≥0∞) +
            ((budget - actionWeight signCost input : ℕ) : ℝ≥0∞) := by
          rw [hweight]
          exact add_le_add le_rfl hrest
        _ = budget := by
          rw [← Nat.cast_add, Nat.add_sub_cancel' h.1]

/-! ## The expected number of requests -/

/-- Private sampling is answered uniformly, leaving the state unchanged. -/
def UniformFaithful {σ : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT σ ProbComp)) : Prop :=
  ∀ (n : ℕ) (state : σ), (impl (.inl (.inl n))).run state =
    (fun sample => (sample, state)) <$> (unifSpec.query n : ProbComp (Fin (n + 1)))

theorem expectedSign_eq_zero {α σ : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT σ ProbComp))
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (h : computation.IsQueryBoundP IsSignQuery 0) (state : σ) :
    expectedSimulatedQueryCount impl IsSignQuery computation state = 0 :=
  le_antisymm (by exact_mod_cast expectedSimulatedQueryCount_le_of_isQueryBoundP impl _ _ _ 0 h)
    zero_le

/-- With a budget of at most one request, the expected number of requests is the probability of
reaching a request through private sampling alone, whatever the hash oracle. -/
theorem expectedSign_eq_of_uniformFaithful {α σ τ : Type}
    (left : QueryImpl (OracleWorld + SigningSpec) (StateT σ ProbComp))
    (right : QueryImpl (OracleWorld + SigningSpec) (StateT τ ProbComp))
    (hleft : UniformFaithful left) (hright : UniformFaithful right) (signCost budget : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (h : IsWeightedBound signCost computation budget) (hbudget : budget ≤ signCost)
    (_hpositive : 0 < signCost) (leftState : σ) (rightState : τ) :
    expectedSimulatedQueryCount left IsSignQuery computation leftState =
      expectedSimulatedQueryCount right IsSignQuery computation rightState := by
  induction computation using OracleComp.inductionOn generalizing budget leftState rightState with
  | pure value => simp
  | query_bind input next ih =>
      have hfull := h
      rw [isWeightedBound_query_bind_iff] at h
      rcases input with (uniformInput | hashInput) | request
      · rw [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_query_bind,
          hleft, hright, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
        simp only [IsSignQuery, if_false, zero_add]
        refine tsum_congr fun sample => congrArg _ ?_
        exact ih sample _ (h.2 sample) (by simpa [actionWeight] using hbudget) _ _
      · have hnone : (liftM ((OracleWorld + SigningSpec).query (.inl (.inr hashInput))) >>=
            next).IsQueryBoundP IsSignQuery 0 := by
          rw [isQueryBoundP_query_bind_iff]
          exact ⟨Or.inl (by simp [IsSignQuery]), fun answer => by
            simpa [IsSignQuery] using (h.2 answer).noSign (by simp [actionWeight]; omega)⟩
        rw [expectedSign_eq_zero _ _ hnone, expectedSign_eq_zero _ _ hnone]
      · have hcost : budget - signCost < signCost := by
          have := h.1
          simp [actionWeight] at this
          omega
        rw [expectedSimulatedQueryCount_query_bind, expectedSimulatedQueryCount_query_bind]
        simp only [IsSignQuery, if_true]
        congr 1
        rw [ENNReal.tsum_eq_zero.mpr fun result => by
            rw [expectedSign_eq_zero _ _ ((h.2 result.1).noSign (by simpa [actionWeight] using hcost)),
              mul_zero],
          ENNReal.tsum_eq_zero.mpr fun result => by
            rw [expectedSign_eq_zero _ _ ((h.2 result.1).noSign (by simpa [actionWeight] using hcost)),
              mul_zero]]

/-- Answering the hash queries without querying leaves the expected number of requests unchanged
when a request can only come before every hash query. -/
theorem expectedSign_pruneDirect_zero_eq {α σ : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (StateT σ ProbComp)) (signCost budget : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (h : IsWeightedBound signCost computation budget) (hbudget : budget ≤ signCost)
    (_hpositive : 0 < signCost) (state : σ) :
    expectedSimulatedQueryCount impl IsSignQuery (Direct.pruneDirect 0 computation) state =
      expectedSimulatedQueryCount impl IsSignQuery computation state := by
  induction computation using OracleComp.inductionOn generalizing budget state with
  | pure value => rfl
  | query_bind input next ih =>
      rw [isWeightedBound_query_bind_iff] at h
      rcases input with (uniformInput | hashInput) | request
      · rw [Direct.pruneDirect_uniform_bind, expectedSimulatedQueryCount_query_bind,
          expectedSimulatedQueryCount_query_bind]
        refine congrArg _ (tsum_congr fun result => congrArg _ ?_)
        exact ih result.1 _ (h.2 result.1) (by simpa [actionWeight] using hbudget) result.2
      · have hlow : budget - actionWeight signCost (.inl (.inr hashInput)) < signCost := by
          simp [actionWeight] at h ⊢
          omega
        have hnone : (liftM ((OracleWorld + SigningSpec).query (.inl (.inr hashInput))) >>=
            next).IsQueryBoundP IsSignQuery 0 := by
          rw [isQueryBoundP_query_bind_iff]
          exact ⟨Or.inl (by simp [IsSignQuery]), fun answer => by
            simpa [IsSignQuery] using (h.2 answer).noSign hlow⟩
        rw [Direct.pruneDirect_hash_bind, if_pos rfl, expectedSign_eq_zero _ _ hnone,
          expectedSign_eq_zero _ _
            ((pruneDirect_zero_isWeightedBound signCost _ _ (h.2 default)).noSign hlow)]
      · rw [Direct.pruneDirect_sign_bind, expectedSimulatedQueryCount_query_bind,
          expectedSimulatedQueryCount_query_bind]
        refine congrArg _ (tsum_congr fun result => congrArg _ ?_)
        exact ih result.1 _ (h.2 result.1) (by omega) result.2

end Xmss.Checksum.HiddenSibling
