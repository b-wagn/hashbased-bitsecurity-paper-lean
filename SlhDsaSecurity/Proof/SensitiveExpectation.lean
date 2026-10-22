import SlhDsaSecurity.Proof.ChargedProbe

/-!
# The input half's charge, before the uniform bound is taken

`ChargedProbe.prob_run_sensitive_le` charges a run one unit of `2 ^ -128` per probe, with the
number of probes supplied as a *uniform* limit: a single number bounding the record on every
supported run. That is the right shape when the room paying for the charge is a constant, and
the wrong one when it is not.

The room is no longer a constant. `RecordedBudget.work_add_pow_add_served_le_of_budget_tail`
reserves two units of the budget per served signing request, so what the record and the defects
have to fit inside is `|record| + 2 · served ≤ q − 2 ^ subtreeHeight` — a *pathwise* inequality,
in which `served` cancels against the defect it pays for. Taking a uniform bound first destroys
that cancellation, because the only uniform bound on `served` is half the budget.

So the uniform step has to come last. The proof already establishes the expectation form —
`ChargedProbe.prob_run_cell_le` concludes with an expectation over runs and
`ChargedProbe.sum_weighted_le` applies the uniform limit only afterwards — and this file states
it, with the uniform version recovered as the corollary it already was. Nothing is reproved; the
step at which the bound stops being pathwise is moved past the sum over cells.
-/

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.SensitiveExpectation

open SensitiveQuery ChargedProbe

variable {Node : Type}

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
open scoped Classical in
/-- **The input half's charge, as an expectation.** One unit of `2 ^ -128` per probe, with the
number of probes read off each run rather than bounded in advance. -/
theorem prob_run_sensitive_expected_le {γ : Type} (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : HandlerCarrier.State → CanonicalGraph.Node → Prop) (run : ProbComp γ)
    (record : γ → List (Bytes × HandlerCarrier.State)) :
    ∑ index : CanonicalGraph.Node,
        Pr[fun pair : γ × Cell =>
            ∃ entry ∈ record pair.1, ChargedBy stakes unavailable index pair.2 entry |
          (do
            let result ← run
            let cell ← ($ᵗ Cell : ProbComp Cell)
            pure (result, cell))] ≤
      (∑' result, Pr[= result | run] * (((record result).length : Nat) : ℝ≥0∞)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (Finset.sum_le_sum fun index _ =>
    prob_run_cell_le stakes unavailable index run record) ?_
  calc ∑ index : CanonicalGraph.Node,
        (∑' result, Pr[= result | run] *
          ((aiming stakes unavailable index (record result) : Nat) : ℝ≥0∞)) /
            ((2 ^ 128 : Nat) : ℝ≥0∞)
      = (∑' result, ∑ index : CanonicalGraph.Node, Pr[= result | run] *
          ((aiming stakes unavailable index (record result) : Nat) : ℝ≥0∞)) /
            ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
        refine congrArg (fun total => total * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹) ?_
        exact sum_tsum_comm Finset.univ _
    _ ≤ (∑' result, Pr[= result | run] * (((record result).length : Nat) : ℝ≥0∞)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
        refine ENNReal.div_le_div_right (ENNReal.tsum_le_tsum fun result => ?_) _
        rw [← Finset.mul_sum]
        refine mul_le_mul' le_rfl ?_
        rw [← Nat.cast_sum]
        exact Nat.cast_le.mpr
          (sum_targets_length_le stakes unavailable (record result))

/-- **The expected number of probes is bounded by any uniform bound on them**, which is the step
the charge used to take first. -/
theorem expected_length_le {γ : Type} (run : ProbComp γ)
    (record : γ → List (Bytes × HandlerCarrier.State)) (limit : Nat)
    (hlimit : ∀ result ∈ support run, (record result).length ≤ limit) :
    (∑' result, Pr[= result | run] * (((record result).length : Nat) : ℝ≥0∞)) ≤
      (limit : ℝ≥0∞) := by
  calc (∑' result, Pr[= result | run] * (((record result).length : Nat) : ℝ≥0∞))
      ≤ ∑' result, Pr[= result | run] * (limit : ℝ≥0∞) := by
        refine ENNReal.tsum_le_tsum fun result => ?_
        by_cases hmem : result ∈ support run
        · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (hlimit result hmem))
        · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]
    _ = (∑' result, Pr[= result | run]) * (limit : ℝ≥0∞) := ENNReal.tsum_mul_right
    _ ≤ 1 * (limit : ℝ≥0∞) := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = _ := one_mul _

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- The uniform charge, recovered from the expectation. -/
theorem prob_run_sensitive_le' {γ : Type} (stakes : Stakes Node CanonicalGraph.Node)
    (unavailable : HandlerCarrier.State → CanonicalGraph.Node → Prop) (run : ProbComp γ)
    (record : γ → List (Bytes × HandlerCarrier.State)) (limit : Nat)
    (hlimit : ∀ result ∈ support run, (record result).length ≤ limit) :
    ∑ index : CanonicalGraph.Node,
        Pr[fun pair : γ × Cell =>
            ∃ entry ∈ record pair.1, ChargedBy stakes unavailable index pair.2 entry |
          (do
            let result ← run
            let cell ← ($ᵗ Cell : ProbComp Cell)
            pure (result, cell))] ≤
      limit / ((2 ^ 128 : Nat) : ℝ≥0∞) :=
  le_trans (prob_run_sensitive_expected_le stakes unavailable run record)
    (ENNReal.div_le_div_right (expected_length_le run record limit hlimit) _)

end SlhDsaSecurity.SensitiveExpectation
